import OAI.Hierarchy.TaggedWideControlBoard
import OAI.Hierarchy.TaggedWideControlGateEval

namespace OAI
/-! # The terminal site's positive keep cell reads the native prune flag -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin.Gate
open ThreeFlat Routing Diagonal TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
variable {F : Type*} [Field F] {E Q D : Type} [Fintype E] [Fintype Q] [Fintype D]
    (B : Gate) (flag : Fin B.u)
local notation "V" => SitePins E Q D B

/-- A physical ternary cell reading the low bit of the paid machine's
unsigned retained-state word. Its other two inputs are ignored. -/
def retentionCell : BitNetwork F (Fintype.card V) where
  cells := 1
  internal := 0
  source _ _ := .pin (Fintype.equivFin V (.inr (.inr (.inr (flag,0)))))
  table _ b := if b 0=true then 1 else 0

theorem retention_value (ext : E→Bool) (sel : Q→Bool) (data : D→Bool) (out : Memory B.W)
    (keep : Prop) (addr : ℕ) (location : (B.addr flag).val=addr)
    (pruned : out addr=if keep then 1 else 0) (room : 1<2^B.W) :
    TypedWiring.value (B.retentionCell (F:=F) (E:=E) (Q:=Q) (D:=D) flag)
      (Sum.elim ext (Sum.elim sel (Sum.elim data (B.terminal out))))=if keep then 1 else 0 := by
  have one : (1:Word B.W).val=1 := Nat.mod_eq_of_lt room
  have bit : B.terminal out (flag,0)=(out addr).val.testBit 0 := by
    change (wide (out (B.addr flag).val)).val.testBit 0=_
    rw [location]
    rfl
  unfold TypedWiring.value BitNetwork.eval BitNetwork.weight BitNetwork.factor
  simp only [retentionCell,BitSource.read,Equiv.symm_apply_apply,Sum.elim_inr,bit]
  change (∑ _ : Fin 0→Bool, ∏ _ : Fin 1, if (out addr).val.testBit 0=true then (1:F) else 0)=_
  have empty (a : F) : (∑ _ : Fin 0→Bool,a)=a := by
    simp [Finset.sum_const]
  rw [empty,Fin.prod_univ_one]
  by_cases kept : keep
  · rw [pruned,ite_eq_left kept,one]
    simp [kept]
  · rw [pruned,ite_eq_right kept]
    simp [kept]

end Hierarchy.Tagged.WideControlJoin.Gate

end
end OAI
