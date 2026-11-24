import OAI.Computability.VPVNP.RAMTapeSuccessorFormat
import OAI.Computability.VPVNP.RAMTapeSuccessorTagPreserve
import OAI.Computability.VPVNP.RAMTapeStackLift

/-!
# The eight-word tag pass of a successor validator

The finite control scans word seven down to word zero. It stores each tag
on return from the preserving scan and immediately starts the next word.
The eight input stacks and the common scratch stack are restored on exit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Successor

open SuccessorTags BurstRAM

/-- Control for the eight-word tag scan, retaining the word index, accumulated tags, and
current word scan state. -/
inductive TagState where
  | scan (i : Fin 8) (tags : Tags) (q : KeepState)
  | done (tags : Tags)
  deriving DecidableEq, Fintype

/-- Start at word seven with all tag slots zero and the single-word scanner at its first bit. -/
def tagEntry : TagState := .scan 7 (fun _ => .zero) (.read .first)

private def tagLabel (i : Fin 8) (tags : Tags) : KeepState → TagState
  | .done t =>
    let saved := Function.update tags i t
    if i.val = 0 then .done saved else .scan ⟨i.val - 1, by omega⟩ saved (.read .first)
  | q => .scan i tags q

/-- Install the eight scans at their respective word ports. The last empty
scratch pop of each scan goes directly to its continuation. -/
def tagCode {K : Type*} (word : Fin 8 → K) (tmp : K) : StackCode K TagState
  | .scan i tags q => (codeKeep (word i) tmp q).rename id (tagLabel i tags)
  | .done _ => .halt true

variable {K : Type*} [DecidableEq K] (word : Fin 8 → K) (tmp : K) (hne : ∀ i, word i ≠ tmp)
  (s : Stacks K) (ht : s tmp = []) {w : ℕ} (a : Fin 8 → Word w)
  (ha : ∀ i, s (word i) = wordBits (a i))

include hne ht ha

private theorem one_tag (i : Fin 8) (tags : Tags) :
    StackRuns (tagCode word tmp) (4*w+2) (.scan i tags (.read .first)) s
      (tagLabel i tags (.done (wordTags a i))) s := by
  have rows (q : KeepState) (h : (codeKeep (word i) tmp q).returns = false) :
      tagCode word tmp (tagLabel i tags q) = (codeKeep (word i) tmp q).rename id (tagLabel i tags) := by
    cases q <;> first | rfl | contradiction
  have scan := (keep_run (word i) tmp (hne i) s ht).lift id Function.injective_id (tagLabel i tags) s rows
  have hst := installStacks_eq Function.injective_id s s (fun _ => rfl)
  simpa only [hst, ha, length_wordBits, TapeWord.value_wordBits, wordTags, tagLabel] using scan

private theorem remaining_tags (i : Fin 8) (tags : Tags)
    (saved : ∀ j : Fin 8, i.val < j.val → tags j = wordTags a j) :
    StackRuns (tagCode word tmp) ((i.val+1)*(4*w+2)) (.scan i tags (.read .first)) s
      (.done (wordTags a)) s := by
  obtain ⟨k, hk⟩ := i
  induction k generalizing tags with
  | zero =>
    let i : Fin 8 := ⟨0, hk⟩
    have complete : Function.update tags i (wordTags a i) = wordTags a := by
      funext j
      by_cases hj : j = i
      · subst j; exact Function.update_self ..
      · rw [Function.update_of_ne hj]
        apply saved j
        change 0 < j.val
        exact Nat.pos_of_ne_zero fun h => hj (Fin.ext h)
    have hstep := one_tag word tmp hne s ht a ha i tags
    change StackRuns (tagCode word tmp) (4*w+2) (.scan i tags (.read .first)) s (.done (Function.update tags i (wordTags a i))) s at hstep
    rw [complete] at hstep
    simpa [i] using hstep
  | succ k ih =>
    let i : Fin 8 := ⟨k+1, hk⟩
    let next := Function.update tags i (wordTags a i)
    have checked (j : Fin 8) (hj : k < j.val) : next j = wordTags a j := by
      by_cases he : j = i
      · subst j; exact Function.update_self ..
      · rw [show next j = tags j from Function.update_of_ne he ..]
        apply saved j
        change k+1 < j.val
        have hval : j.val ≠ k+1 := fun h => he (Fin.ext h)
        omega
    have hstep := one_tag word tmp hne s ht a ha i tags
    have hrest := ih next (by omega) checked
    have hlink : tagLabel i tags (.done (wordTags a i)) = .scan ⟨k, by omega⟩ next (.read .first) := by
      simp [tagLabel, next, i]
    rw [hlink] at hstep
    convert hstep.trans hrest using 1
    change (k+1+1)*_ = _ + (k+1)*_
    ring

/-- The complete field pass classifies all eight words and preserves the caller's
stacks. Only the temporary stack must be distinct from each data port. -/
theorem tag_run :
    StackRuns (tagCode word tmp) (8*(4*w+2)) tagEntry s (.done (wordTags a)) s := by
  apply remaining_tags word tmp hne s ht a ha 7 (fun _ => .zero)
  intro j hj
  have := j.isLt
  change 7 < j.val at hj
  omega

end RAMTape.Successor

end VPVNP
end Computability
end OAI
