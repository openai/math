import OAI.ThreeFlat.Diagonal.LaneBucketAddresses
import OAI.ThreeFlat.Diagonal.LaneCursorRelay
import OAI.ThreeFlat.Diagonal.TraceMaskDictionary

namespace OAI
/-! # Mixed-radix receipt and emission fields of a local bucket -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout
open Computability.VPVNP.BurstRAM RAM.EffectStream
open scoped Fin.CommRing
variable {F : Type*} {p k low o c W r : ℕ} {N : BitNetwork F p} (P : RowLayout N (k+1) low o c)

/-- The rectangular relay tags use offset-major, source-low, destination
slot, and leg order. -/
theorem tagNumber (t : Tags o low c) :
    ((tagOrder o low c).symm t).val =
      ((t.1.val*2^low+t.2.1.val)*c+t.2.2.1.val)*3+t.2.2.2.val := by
  change t.2.2.2.val+3*t.2.2.1.val+(c*3)*t.2.1.val+(2^low*(c*3))*t.1.val=_
  ring

theorem tag_occurrence (a : Occurrence N) :
    ((tagOrder o low c).symm (P.tag a)).val =
      (((P.code a).val*2^low+(P.owner a).val%2^low)*c+(P.cellAddress a.val.1).2.val)*3+a.val.2.val := by
  rw [tagNumber]; rfl

theorem selected_bit (i : Fin (k+1)) (j : Fin o) :
    (selected (r:=r) P.mask j i).val=((P.offset j).val/2^(low+i.val))%2 := by
  change (P.mask j i).val + 2*0 = _
  simp only [Nat.mul_zero,Nat.add_zero,mask,splitRow_lane,highBits,Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq,Nat.div_div_eq_div_mul,Nat.pow_add]
  by_cases hit : ((P.offset j).val/(2^low*2^i.val))%2=1
  · simp [hit]
  · have zero : ((P.offset j).val/(2^low*2^i.val))%2=0 := by omega
    simp [zero]

theorem owner_xor (a : Occurrence N) :
    (P.owner a).val ^^^ (P.cellAddress a.val.1).1.val = (P.offset (P.code a)).val := by
  have h := congrArg Fin.val (P.reaches a)
  change (P.cellAddress a.val.1).1.val = (P.owner a).val ^^^ (P.offset (P.code a)).val at h
  rw [h,←Nat.xor_assoc,Nat.xor_self,Nat.zero_xor]

/-- Reading the sparse public dictionary at the measured XOR displacement
returns the actual source's canonical offset ordinal. -/
theorem dictionary_code (base : ℕ) (m : Memory W) (fit : base+2^(k+1)*2^low ≤ 2^W)
    (a : Occurrence N) :
    after m (events (P.dictionary base)) (base+((P.owner a).val ^^^ (P.cellAddress a.val.1).1.val)) =
      ((P.canonical.code a).val : Word W) := by
  rw [owner_xor]
  exact P.read_dictionary base m fit _

end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
