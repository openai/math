import OAI.Hierarchy.DescentResetBlockFields
import OAI.Hierarchy.DescentBatchedNodeOrder

namespace OAI
/-! # Locate the original operand in its chronologically sorted width interval -/
namespace Hierarchy.DescentResetPointerFields
open DescentOrderedWords
open scoped Classical BigOperators
noncomputable section
/-- Locate the unique interval using only its cumulative start and width. -/
def findInterval {X : Type} (start width : X→ℕ) (z : ℕ) : List X→Option X
  | []=>none
  | x::xs=>if start x≤z ∧ z<start x+width x then some x else findInterval start width z xs

private theorem find_only {X : Type} (start width : X→ℕ) (z : ℕ) (i : X)
    (only : ∀x,(start x≤z ∧ z<start x+width x) ↔ x=i) (xs : List X) (mem : i∈xs) :
    findInterval start width z xs=some i := by
  induction xs with
  | nil => simp at mem
  | cons x xs ih =>
    by_cases yes : x=i
    · subst x
      simp [findInterval,(only i).mpr rfl]
    · simp [findInterval,show ¬(start x≤z ∧ z<start x+width x) from fun h=>yes ((only x).mp h),
        ih ((List.mem_cons.mp mem).resolve_left (Ne.symm yes))]

theorem findInterval_address {X : Type} [Fintype X] {L : ℕ} (k : X↪Fin L) (width : X→ℕ)
    (z : Fin (∑x,width x)) (xs : List X) (all : ∀x,x∈xs) :
    findInterval (offset k width) width z.val xs=some ((address k width).symm z).1 := by
  rcases eqn : (address k width).symm z with ⟨i,t⟩
  have inverse : address k width ⟨i,t⟩=z := ((Equiv.symm_apply_eq _).mp eqn).symm
  have val := congrArg Fin.val inverse
  rw [address_val] at val
  apply find_only _ _ _ _ _ _ (all i)
  intro x
  constructor
  · intro ⟨lo,hi⟩
    have ti:=t.isLt
    rcases lt_trichotomy (k x) (k i) with less|same|more
    · have endAt := earlier k width x i less
      omega
    · exact k.injective same
    · have endAt := earlier k width i x more
      omega
  · rintro rfl
    have ti:=t.isLt
    omega

end
end Hierarchy.DescentResetPointerFields

end OAI
