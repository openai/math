import OAI.Hierarchy.TaggedAlignBuckets
import OAI.Hierarchy.TaggedPassRead
import OAI.Hierarchy.TaggedLocalSortBuckets
import OAI.Hierarchy.TaggedPassState

namespace OAI
/-! # The retained local prefixes preserve each real digit bucket -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork RadixStage SortedBlock
open scoped Classical
noncomputable section

variable {d w j t : ℕ}

namespace PassShape
variable (s : PassShape) (dummy : Bits w) (real isDummy : Fin w) (digit : Fin s.digitBits → Fin w)

/-- The complete exact local sort/align bank, followed by clipping its padding,
reads an unchanged bucket of the requested digit over all logical blocks. -/
theorem retained_buckets (room : s.packBits+2 ≤ s.digitBits) (blank : dummy real = false) (flags : dummy isDummy = !(dummy real))
    (x : RowBits s.rows w → Bool) (valid : shapeFlags s.rows real isDummy x) (a : ℕ)
    (fits : s.perBlock ≤ 2^s.localBits) :
    sweep s.blocks (fun b => sweep s.perBlock (fun i => observeRow real digit a (s.blockWord (s.localOut dummy real isDummy digit x) b (i.castLE fits)))) =
      sweep s.rows (fun i => observeRow real digit a (fun j => x (i,j))) := by
  let inBlocks := staticRead (s.enter dummy) x
  let sorted := s.localSortRun isDummy digit inBlocks
  let input := fun b => s.blockWord inBlocks b
  let mid := fun b => s.blockWord sorted b
  let see := observeRow real digit a
  have localWord (b i) : s.blockWord (s.localOut dummy real isDummy digit x) b i = align (j := s.packBits) (t := s.upperBits) digit real (mid b) i := by
    exact congrFun (unwrap_pack (align (j := s.packBits) (t := s.upperBits) digit real (mid b))) i
  have sortedWord (b) : mid b = stable (maskedDigit digit isDummy) (input b) := by
    exact unwrap_pack (stable (maskedDigit digit isDummy) (input b))
  have good (b) := s.aligned_input dummy real isDummy digit room blank flags x valid b
  have localFlags (b i) : input b i isDummy = !(input b i real) := by
    dsimp only [input,inBlocks]; rw [enter_block_word]; split <;> first | (split <;> first | exact valid _ | exact flags) | exact flags
  have count (b) : prefixSize real (mid b) ≤ s.block := by
    rw [sortedWord]; apply bound
    intro i hr
    by_contra! h
    simp [input,inBlocks,enter_block_word,not_lt.mpr h,blank] at hr
  have same (b) : sweep s.perBlock (fun i => see (align (j := s.packBits) (t := s.upperBits) digit real (mid b) (i.castLE fits))) =
      sweep (2^s.localBits) (fun i => see (input b i)) := by
    have inactive (i : Row s.localBits) (off : s.perBlock ≤ i.val) : see (align (j := s.packBits) (t := s.upperBits) digit real (mid b) i)=[] := by
      by_cases hr : align (j := s.packBits) (t := s.upperBits) digit real (mid b) i real = true
      · have bound := align_support (mid b) real digit (good b) i hr
        have large : s.block+2^s.digitBits*2^s.packBits ≤ s.perBlock := by unfold perBlock Radix.PassShape.pack; rw [Nat.add_mul]; omega
        exact ((Nat.not_lt_of_ge off) (bound.trans_le ((Nat.add_le_add_right (count b) _).trans large))).elim
      · simp [see,observeRow,hr]
    calc
      _ = sweep (2^s.localBits) (fun i => see (align (j := s.packBits) (t := s.upperBits) digit real (mid b) i)) :=
        (sweep_extend fits _ _ (fun _ => rfl) inactive).symm
      _ = sweep (2^s.localBits) (fun i => see (mid b i)) :=
        localAlign_buckets (j := s.packBits) (t := s.upperBits) (mid b) real digit a (good b)
      _ = _ := by
        rw [sortedWord]
        exact localSort_buckets _ _ _ _ _ (localFlags b)
  have pre : s.block ≤ 2^s.localBits := (Nat.le_add_right ..).trans fits
  simp_rw [localWord]
  change sweep s.blocks (fun b => sweep s.perBlock (fun i => see (align (j := s.packBits) (t := s.upperBits) digit real (mid b) (i.castLE fits)))) = _
  simp_rw [same]
  exact s.enter_sweep dummy x see (by simp [see,observeRow,blank]) pre

end PassShape
end
end Hierarchy.Tagged.Radix

end OAI
