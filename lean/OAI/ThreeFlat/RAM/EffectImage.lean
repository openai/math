import OAI.ThreeFlat.RAM.EffectStream
import OAI.ThreeFlat.RAM.WordSegment

namespace OAI
/-! # Staging a chronological stream of two-word RAM effects -/

namespace ThreeFlat.RAM.EffectStream

open Computability.VPVNP.BurstRAM

variable {w : ℕ}

/-- At an absolute tape address, read the address half or value half of
the indexed record. Positions beyond the supplied record list yield zero. -/
def packedWord (src : ℕ) (updates : List (Record w)) (a : ℕ) : Word w :=
  let offset := a-src
  let pair := updates[offset/2]?.getD (0,0)
  if offset%2 = 0 then pair.1 else pair.2

theorem packedWord_address (src : ℕ) (updates : List (Record w)) (i : Fin updates.length) :
    packedWord src updates (src+2*i.val) = (updates.get i).1 := by
  have idx : (src+2*i.val-src)/2 = i.val := by omega
  have even : (src+2*i.val-src)%2 = 0 := by omega
  simp only [packedWord, idx, even, ite_true, List.getElem?_eq_getElem i.isLt, Option.getD_some]; rfl

theorem packedWord_value (src : ℕ) (updates : List (Record w)) (i : Fin updates.length) :
    packedWord src updates (src+2*i.val+1) = (updates.get i).2 := by
  have idx : (src+2*i.val+1-src)/2 = i.val := by omega
  have odd : ¬ (src+2*i.val+1-src)%2 = 0 := by omega
  simp only [packedWord, idx, ite_eq_right odd, List.getElem?_eq_getElem i.isLt, Option.getD_some]; rfl

/-- A contiguous descriptor scan writes the address and value words
required by the native chronological replay loop. -/
theorem loaded_fillSegment (src : ℕ) (updates : List (Record w)) (input : Memory w) :
    Loaded (fillSegment src (2*updates.length) (packedWord src updates) input) src updates := by
  apply (loaded_iff _ _ _).2
  intro i
  have hi := i.isLt
  have left : src ≤ src+2*i.val ∧ src+2*i.val < src+2*updates.length := by omega
  have right : src ≤ src+2*i.val+1 ∧ src+2*i.val+1 < src+2*updates.length := by omega
  exact ⟨(ite_eq_left left).trans (packedWord_address src updates i),
    (ite_eq_left right).trans (packedWord_value src updates i)⟩

/-- Subsequent writes to any addresses preserve initial agreement at a
fixed location, even when the trace writes there repeatedly. -/
theorem after_eq_at (xs : List (Event w)) (m m' : Memory w) (a : ℕ) (same : m a = m' a) :
    after m xs a = after m' xs a := by
  induction xs generalizing m m' with
  | nil => exact same
  | cons e xs ih =>
    change after (update m e) xs a = after (update m' e) xs a
    apply ih
    cases e with
    | tick => exact same
    | choice _ => exact same
    | read _ _ => exact same
    | write x v =>
      change (if a = x.val then v else m a) = (if a = x.val then v else m' a)
      rw [same]

/-- The scratch tape is invisible outside its own interval after any
common event trace. The trace may also write into the scratch interval. -/
theorem after_fillSegment_outside (src n : ℕ) (get : ℕ → Word w) (input : Memory w)
    (es : List (Event w)) (a : ℕ) (away : a < src ∨ src+n ≤ a) :
    after (fillSegment src n get input) es a = after input es a := by
  apply after_eq_at
  exact ite_eq_right (by omega : ¬ (src ≤ a ∧ a < src+n))

end ThreeFlat.RAM.EffectStream

end OAI
