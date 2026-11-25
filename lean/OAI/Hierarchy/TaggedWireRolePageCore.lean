import OAI.Hierarchy.ProtocolRAMBinarySpan
import OAI.Hierarchy.ProtocolRAMScan
import OAI.ThreeFlat.RAM.WordSegment

namespace OAI
/-! # Reading a mounted finite role table by its native lookup expression -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {w : ℕ}

def bank (base n : ℕ) : Bank := ⟨base,ProtocolRAMPurchaseSampler.bits n⟩
def expr (base n : ℕ) (input : Expr) : Expr := .lookup (bank base n) input

def init {n : ℕ} (base : ℕ) (table : Fin n→ℕ) (m : Memory w) :=
  fillSegment base n (fun a=>if h:a-base<n then ((table ⟨a-base,h⟩):Word w) else 0) m

def Mounted {n : ℕ} (base : ℕ) (table : Fin n→ℕ) (m : Memory w) := ∀i,m (base+i.val)=((table i):Word w)

theorem mount {n : ℕ} (base : ℕ) (table : Fin n→ℕ) (m : Memory w) : Mounted base table (init base table m) := by
  intro i
  simp [init,fillSegment,i.isLt]

theorem read {n base : ℕ} {table : Fin n→ℕ} {m : Memory w} (ready : Mounted base table m)
    (input : Expr) (row : Word w) (i : Fin n) (room : n≤2^w) (seen : input.eval m row=(i.val:Word w)) :
    (expr base n input).eval m row=((table i):Word w) := by
  change m (base+(input.eval m row).val%(bank base n).size)=_
  rw [seen,Fin.val_cast_of_lt (i.isLt.trans_le room)]
  change m (base+i.val%ProtocolRAMPurchaseSampler.span n)=_
  rw [Nat.mod_eq_of_lt (i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span n))]
  exact ready i

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleROM
end

end OAI
