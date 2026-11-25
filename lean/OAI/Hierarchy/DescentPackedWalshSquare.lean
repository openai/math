import OAI.Hierarchy.DescentPackedWalshPasses
import OAI.Hierarchy.DescentWalshPhysicalRange

namespace OAI
/-! # Squaring the selected signed Walsh coefficients in place by a short-word dictionary -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {b w H u l : ℕ}

def square (b l : ℕ) (i : Cell (smallKey l b)) : Cell (smallKey l b) :=
  encode b (2^l) (fun j=>let e:=(encode b (2^l)).symm i j; e*e)

theorem square_chunk (x : Cube l→Cell b) : square b l (chunk x)=chunk (fun q=>x q*x q) := by
  unfold square chunk
  apply congrArg (encode b (2^l))
  funext j
  rw [Equiv.symm_apply_apply]

def squareExpr (source table : Bank) : Expr := .lookup table (.lookup source .row)

def squareROM (base : ℕ) (m : Memory w) (b l : ℕ) (z : ℕ) : Word w :=
  if base≤z then if h : z-base<2^(smallKey l b) then (square b l ⟨_,h⟩).val else m z else m z

theorem squareROM_at (base : ℕ) (m : Memory w) (i : Cell (smallKey l b)) :
    squareROM base m b l (base+i.val)=((square b l i).val:Word w) := by simp [squareROM,i.isLt]

theorem squares (B D : Bank) (out : ℕ) (mem : Memory w) (x : Fin H→Cube u→Cube l→Cell b)
    (bf : B.Fits w out) (df : D.Fits w out) (enough : H*2^u≤B.size) (keys : 2^(smallKey l b)≤D.size)
    (limit : out+H*2^u<2^w) (old : Installed B.base x mem)
    (table : ∀i : Cell (smallKey l b),mem (D.base+i.val)=((square b l i).val:Word w)) :
    let expr:=squareExpr B D;let dst:=image out (H*2^u) expr mem
    (scan w out (H*2^u) expr).Exec mem dst (4+28*(H*2^u)) ∧
      Installed out (fun v p q=>x v p q*x v p q) dst ∧
      (∀z<out,dst z=mem z) ∧ ∀z,out+H*2^u≤z→dst z=mem z := by
  have legal : (squareExpr B D).Fits w out:=⟨df,bf,trivial⟩
  have price : 2*(squareExpr B D).work+4=28:=rfl
  refine ⟨by rw [show 4+28*(H*2^u)=4+(H*2^u)*(2*(squareExpr B D).work+4) by rw [price,Nat.mul_comm 28]]; intro P R K machine; exact scan_exec out (H*2^u) _ mem legal limit machine,?_,
    fun z h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl h),fun z h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr h)⟩
  intro v p
  rw [ProtocolRAMGeneratedWrite.read_image]
  change D.read mem (B.read mem ((row v p).val:Word w))=_
  rw [DescentPackedZip.bank_read B mem ((row v p).isLt.trans_le enough) bf,old,
    DescentPackedZip.bank_read D mem ((chunk (x v p)).isLt.trans_le keys) df,table (chunk (x v p)),square_chunk]

/-- A completed pass retains a pointwise read at every original address. -/
theorem Installed.bitValue {addrBase : ℕ} {m : Memory w} {x : Fin H→Cube u→Cube l→Cell b}
    (read : Installed addrBase x m) (room : smallKey l b≤w) (v : Fin H) (p : Cube u) (q : Cube l) :
    digit b (ordinal l q).val (m (addrBase+(row v p).val)).val=(x v p q).val := by
  have small:= (chunk (x v p)).isLt.trans_le (Nat.pow_le_pow_right (by decide) room)
  rw [read,Fin.val_cast_of_lt small,chunk,digit_encode,Equiv.symm_apply_apply]

end
end Hierarchy.DescentPackedWalsh

end OAI
