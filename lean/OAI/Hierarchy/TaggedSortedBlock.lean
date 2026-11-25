import OAI.Hierarchy.TaggedBlockRecords
import OAI.Hierarchy.TaggedSortedKeys
import OAI.Hierarchy.TaggedAlignmentData
import Mathlib.Data.Fin.Tuple.Sort

namespace OAI
/-! # A sorted local bank has a real prefix in increasing digit order -/

namespace Hierarchy.Tagged.SortedBlock
open ThreeFlat Routing SortNetwork
open Radix.PassShape
open scoped Classical
noncomputable section

variable {l d w : ℕ}

theorem sorted_digit {j t : ℕ} (digit : Fin d → Fin w) (real dummy : Fin w) (input : Records (j+t) w)
    (flags : ∀ i, input i dummy = !(input i real)) :
    AlignRows.Ordered real digit (stable (maskedDigit digit dummy) input) := by
  let key := fun i : Row (j+t) => addressEquiv (d+1) (input i ∘ maskedDigit digit dummy)
  let e := Tuple.sort key
  intro edge left right
  have ord : (key (e edge.1)).val ≤ (key (e (next edge))).val :=
    Tuple.monotone_sort key (show edge.1 ≤ next edge from Nat.le_succ _)
  change readKey (maskedDigit digit dummy) (input (e edge.1)) ≤ readKey (maskedDigit digit dummy) (input (e (next edge))) at ord
  change input (e edge.1) real = true at left
  change input (e (next edge)) real = true at right
  change readKey digit (input (e edge.1)) ≤ readKey digit (input (e (next edge)))
  simpa only [masked_value,flags,left,right,Bool.not_true,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using ord

end
end Hierarchy.Tagged.SortedBlock

end OAI
