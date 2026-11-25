import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Splitting public cable intervals into pools

At a fixed bin in Lemma 6.1, the ordered cable records cover consecutive bit intervals. Two cuts
isolate the portion belonging to the matched prefix of a direction pool. Each cut uses a constant
number of words, independently of the cable widths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

/-- Position of a bin cut within one cable's interval. -/
def cutOffset (start width cut : ℕ) : ℕ := min width (cut - start)

/-- Width selected from an interval for one matched direction pool. -/
def overlapWidth (start width lo hi : ℕ) : ℕ := cutOffset start width hi - cutOffset start width lo

/-- The old cable is the concatenation of the retained prefix, matched segment and retained suffix. -/
theorem cut_partition (start width lo hi : ℕ) (ordered : lo ≤ hi) :
    cutOffset start width lo + overlapWidth start width lo hi +
        (width - cutOffset start width hi) = width := by
  simp only [cutOffset, overlapWidth]
  omega

/-- Reindexing a bit of the selected piece gives exactly the old interval positions between the cuts. -/
theorem in_overlap_iff (start width lo hi i : ℕ) (hiw : i < width) :
    (cutOffset start width lo ≤ i ∧ i < cutOffset start width hi) ↔
      lo ≤ start + i ∧ start + i < hi := by
  unfold cutOffset
  omega

/-- The scalar scan over record widths, keeping the cumulative offset in the bin. -/
def matchedWidths (lo hi : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | start, w :: ws => overlapWidth start w lo hi :: matchedWidths lo hi (start + w) ws

/-- The scan preserves one output width per input descriptor, including zero overlaps. -/
theorem matchedWidths_length (lo hi start : ℕ) (ws : List ℕ) :
    (matchedWidths lo hi start ws).length = ws.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simp [matchedWidths, ih]

/-- The entire scan assigns exactly the matched width; a cut never loses a bit at a cable boundary. -/
theorem matchedWidths_sum (lo hi start : ℕ) (ws : List ℕ) (ordered : lo ≤ hi) :
    (matchedWidths lo hi start ws).sum = overlapWidth start ws.sum lo hi := by
  induction ws generalizing start with
  | nil => simp [matchedWidths, overlapWidth, cutOffset]
  | cons w ws ih =>
    simp only [matchedWidths, List.sum_cons, ih, overlapWidth, cutOffset]
    omega

/-- A matched prefix lying within the bin has exactly the selected common width in this direction. -/
theorem matchedWidths_full (ws : List ℕ) (lo width : ℕ) (fits : lo + width ≤ ws.sum) :
    (matchedWidths lo (lo + width) 0 ws).sum = width := by
  rw [matchedWidths_sum lo _ 0 ws (by omega)]
  simp only [overlapWidth, cutOffset]
  omega

end Packing

end BorderVNP
end Computability
end OAI
