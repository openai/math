import OAI.ThreeFlat.Diagonal.CompressorPhysicalPadding
import OAI.ThreeFlat.Diagonal.CompressorTypedFiles

namespace OAI
/-! # Quotient and remainder at the physical address of a six-column row -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr
open scoped Fin.NatCast
variable {w : ℕ} (cell : Word w) (m : Memory w) (vs : Fin 1 → Word w)
local notation "V" => Formula.value (fun _=>cell) m vs

theorem split_address (dest : F) (origin base port d : ℕ) (hd : d<2^w) (hp : port<d)
    (safe : base*d+port<2^w) (hdest : V dest=(origin:Word w))
    (here : vs 0=((origin+(base*d+port):ℕ):Word w)) :
    V (.op .div (.op .sub (.reg 0) dest) (.lit d))=(base:Word w) ∧
    V (.op .mod (.op .sub (.reg 0) dest) (.lit d))=(port:Word w) := by
  have idx : V (.op .sub (.reg 0) dest)=((base*d+port:ℕ):Word w) := by
    change vs 0-V dest=_
    rw [here,hdest,Nat.cast_add]
    abel
  constructor
  · change BinaryOp.div.eval (V (.op .sub (.reg 0) dest)) (d:Word w)=_
    rw [idx,op_cast .div _ _ ⟨safe,hd⟩]
    change (((base*d+port)/d:ℕ):Word w)=_
    rw [Nat.mul_comm base,Nat.mul_add_div (Nat.zero_lt_of_lt hp),Nat.div_eq_of_lt hp,Nat.add_zero]
  · change BinaryOp.mod.eval (V (.op .sub (.reg 0) dest)) (d:Word w)=_
    rw [idx,op_cast .mod _ _ ⟨safe,hd⟩]
    change (((base*d+port)%d:ℕ):Word w)=_
    simp [Nat.add_mod,Nat.mod_eq_of_lt hp]

def columnNumber (back : Bool) (f : Fin 3) : Fin 6 :=
  ⟨SlotImage.column back f,by cases back <;> have := f.isLt <;> simp [SlotImage.column] <;> omega⟩

theorem columnNumber_read (S : Graph.Stage) (lay rev : Bool) (f : Fin 3)
    (lo len row : ℕ) (fit : 6≤2^w) (hLen : len<2^w) (within : row<len)
    (top : lo+len*SlotImage.column rev f+row<2^w)
    (start : V (Template.f nextGraph)=(lo:Word w)) (length : V (Template.f nextSlots)=(len:Word w))
    (here : vs 0=((lo+len*SlotImage.column rev f+row:ℕ):Word w))
    (chosen : V (Template.f selected)=if lay then 1 else 0) (one : (1:Word w)≠0) :
    V (graph S false)=V (update S lay rev (graphField f)
      (column o (Template.f nextGraph) (Template.f nextSlots) (SlotImage.column rev f))) := by
  have h := column_read cell m vs S lay (columnNumber rev f) lo len row fit hLen within
    (by simpa [columnNumber,Nat.mul_comm] using top) start length
    (by simpa only [columnNumber,Nat.mul_comm len] using here) chosen one
  cases rev <;> fin_cases f <;> exact h

theorem value_column (lo len : ℕ) (start : V (f nextGraph)=(lo:Word w))
    (length : V (f nextSlots)=(len:Word w)) (i : ℕ) :
    V (column o (f nextGraph) (f nextSlots) i)=((lo+len*i:ℕ):Word w) := by
  change V (f nextGraph) + V (f nextSlots)*(i:Word w)=_
  rw [start,length,Nat.cast_add]
  apply congrArg (fun n : Word w => (lo : Word w) + n)
  apply Fin.ext
  exact (Nat.mul_mod len i (2^w)).symm


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
