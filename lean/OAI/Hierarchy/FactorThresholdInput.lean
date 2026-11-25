import OAI.Hierarchy.FactorThresholds
import OAI.Hierarchy.TraceRecordInput

namespace OAI
/-! # Native decoding of the shared threshold bitstring -/

namespace Hierarchy.FactorBucketRAM

open Computability.VPVNP.BurstRAM ThreeFlat
open RAM.PhysicalProcedure RAM Diagonal TraceAdmission
open scoped Fin.CommRing

/-- The same literal bits can be copied to every receiver. Their word number
and within-word index determine them, independently of all selected factors. -/
def thresholdBit (width a : ℕ) : Bool :=
  (FactorBucket.threshold (a/width)).testBit (width-1-a%width)

theorem threshold_word_decode (w : ℕ) (hw : 0<w) (i : ℕ) (hi : i≤20*(w+1)) :
    inputWord (W:=64*w) (thresholdBit (64*w)) i = (FactorBucket.threshold i:Word (64*w)) := by
  let W := 64*w
  have pos : 0<W := Nat.mul_pos (by decide) hw
  apply (MotifBinaryPacking.word W).symm.injective
  change (MotifBinaryPacking.word W).symm ((MotifBinaryPacking.word W) _) = _
  rw [Equiv.symm_apply_apply]
  funext j
  have jlt : j.val<W := j.isLt
  have valid : W-1-j.val<W := by omega
  have div : (W*i+(W-1-j.val))/W=i := by
    rw [Nat.mul_comm W i,Nat.add_comm,Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt valid,zero_add]
  have mod : (W*i+(W-1-j.val))%W=W-1-j.val := by
    simp [Nat.mul_comm W i,Nat.mod_eq_of_lt valid]
  change (FactorBucket.threshold ((W*i+(W-1-j.val))/W)).testBit (W-1-(W*i+(W-1-j.val))%W) =
    ((FactorBucket.threshold i:Word W)).val.testBit j.val
  rw [div,mod,show W-1-(W-1-j.val)=j.val by omega,
    Fin.val_cast_of_lt (FactorBucket.threshold_word hw hi)]

/-- The stock fixed fifteen-label input reader actually materializes each word
from the charged public bitstring, leaving the rest of memory unchanged. -/
theorem threshold_input (w src dst : ℕ) (positive : 0<w)
    (apart : dst+(20*(w+1)+1) ≤ src ∨ src+(64*w)*(20*(w+1)+1) ≤ dst)
    (dstFit : dst+(20*(w+1)+1)<2^(64*w)) (srcFit : src+(64*w)*(20*(w+1)+1)<2^(64*w)) :
    (inputPacker (64*w) src dst (20*(w+1)+1)).Spec
      (fun m=> ∀ a<(64*w)*(20*(w+1)+1), m (src+a)=((thresholdBit (64*w) a).toNat:Word (64*w)))
      (fun m out=> (∀ i≤20*(w+1), (out (dst+i)).val=FactorBucket.threshold i) ∧
        ∀ a, a<dst ∨ dst+(20*(w+1)+1)≤a → out a=m a)
      ((20*(w+1)+1)*(5*(64*w)+6)+6) := by
  intro P R K M pc reg pub exit installed constants c m entry bits
  obtain ⟨ticks,time,final,out,ran,returned,populated⟩ :=
    inputPacker_run src dst (20*(w+1)+1) (thresholdBit (64*w)) apart dstFit srcFit
      M pc reg pub exit installed constants c m entry bits
  refine ⟨ticks,time,final,out,ran,returned,?_⟩
  rw [populated]
  constructor
  · intro i hi
    simp [fillSegment,show dst≤dst+i ∧ dst+i<dst+(20*(w+1)+1) by omega,
      threshold_word_decode w positive i hi,Fin.val_cast_of_lt (FactorBucket.threshold_word positive hi)]
  · intro a ha
    simp [fillSegment,show ¬(dst≤a ∧ a<dst+(20*(w+1)+1)) by omega]

end Hierarchy.FactorBucketRAM

end OAI
