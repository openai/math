import OAI.ThreeFlat.Diagonal.CompressorTypedFiles
import OAI.ThreeFlat.Diagonal.CompressorDemandROM
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # The native key and residual-lane lookups in the selected output-width scan -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.PostImage
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr
open scoped Fin.NatCast
variable {B : Type*} {w n N d l : ℕ}
variable (pub : Param → Word w) (mem : Memory w) (vs : Fin n → Word w)
local notation "V" => Formula.value pub mem vs

theorem readKey (base : B ≃ Fin N) (p : B × Fin d) (lane : BitWord l) (idx size key : Formula n)
    (keyBase : ℕ) (value : Word w) (hidx : V idx=((SlotImage.edgeOrdinal base (tagOrdinal l) (p,lane)):Word w))
    (hsize : V size=((2^l:ℕ):Word w)) (hbase : V key=(keyBase:Word w))
    (cap : SlotImage.edgeOrdinal base (tagOrdinal l) (p,lane)<2^w)
    (lsize : 2^l<2^w) (keyFit : keyBase+SlotImage.ordinal base p<2^w)
    (stored : mem (keyBase+SlotImage.ordinal base p)=value) :
    V (.load (.op .add key (.op .div idx size)))=value ∧
      V (.op .mod idx size)=tagWord (show l≤w by
        by_contra! bad
        exact (Nat.not_le_of_gt lsize) (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt bad))) lane := by
  let e := SlotImage.edgeOrdinal base (tagOrdinal l) (p,lane)
  let h := SlotImage.ordinal base p
  let g := (tagOrdinal l lane).val
  have low : g<2^l := (tagOrdinal l lane).isLt
  have div : e/2^l=h := by
    change (h*2^l+g)/2^l=h
    rw [Nat.mul_comm,Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt low,Nat.add_zero]
  have mod : e%2^l=g := by change (h*2^l+g)%2^l=g; simp [Nat.add_mod,Nat.mod_eq_of_lt low]
  have hq : V (.op .div idx size)=(h:Word w) := by
    change BinaryOp.div.eval (V idx) (V size)=_
    rw [hidx,hsize,op_cast .div _ _ ⟨cap,lsize⟩]
    exact congrArg Nat.cast div
  have hr : V (.op .mod idx size)=(g:Word w) := by
    change BinaryOp.mod.eval (V idx) (V size)=_
    rw [hidx,hsize,op_cast .mod _ _ ⟨cap,lsize⟩]
    exact congrArg Nat.cast mod
  refine ⟨?_,hr.trans (Demand.tag_cast _ lane)⟩
  change mem (V key+V (.op .div idx size)).val=_
  rw [hbase,hq,←Nat.cast_add,Fin.val_cast_of_lt keyFit]
  exact stored

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.PostImage

end OAI
