import OAI.Computability.NearSquareRoot.ScheduleRegisterLoom
import OAI.Computability.IntegerMultiplication.Code.Zip

/-!
# Resource bounds for the P192 two-forest zipper

This is the command that P192 uses to pair records in tape order. The heads
of the two streams, a reusable transit register and a register holding
completed pairs suffice for every input.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Code.Task
open CommonRegisters Space

open private zipBody from OAI.Computability.IntegerMultiplication.Code.Zip

/-- The concrete P192 zipper with the first forest transferred to register one. -/
def zipCommand : Cmd :=
  splitRoot 0 (fun _ => .pass) ((move 0 1 2).join (.tie zipBody))

theorem zip_within : Within 4 zipCommand := by
  apply split_within (by decide)
  · exact fun _ => trivial
  refine ⟨move_within (by decide) (by decide) (by decide), ?_⟩
  apply split_within (by decide)
  · exact fun _ => split_within (by decide) (fun _ => (by decide : 0 < 4)) trivial
  · apply split_within (by decide)
    · exact fun _ => trivial
    exact ⟨move_within (by decide) (by decide) (by decide), (by decide : 0 < 4),
      move_within (by decide) (by decide) (by decide), trivial,
      move_within (by decide) (by decide) (by decide), (by decide : 0 < 4)⟩

/-- Both forests have one record for each entry of the same input list. -/
theorem zip_fits {X : Type*} (f g : X → Tree) (l : List X) (E : Env) (r : Deck) :
    Fits E zipCommand (pile 0 (.fork (forest f l) (forest g l)) r)
      (pile 0 (forest (fun x => .fork (f x) (g x)) l) r)
      (200 * ((forest f l).count + (forest g l).count + 1)) := by
  let j := fun x => Tree.fork (f x) (g x)
  let b := zipBody
  let H := fun l => 150 * ((forest f l).count + (forest g l).count)
  suffices hc : Fits (b::E) b (pile 1 (forest f l) (pile 0 (forest g l) r))
      (pile 0 (forest j l) r) (H l) by
    refine (fits_pair ((fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide)
      (forest f l) E _).join hc.tie)).mono ?_
    simp only [H]
    omega
  induction l generalizing r with
  | nil => exact (fits_bit (b:=false) (fits_bit (b:=false) (fits_give false r _ _))).mono (by simp [H])
  | cons x l ih =>
    let env := b::E
    let z := pile 1 (forest f l) (pile 0 (forest g l) r)
    have h₁ := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) (f x) env
      (pile 0 (g x) z)
    have h₂ := fits_pack (f x) (g x) z 0 env
    have h₃ := fits_move (i:=0) (j:=3) (u:=2) (by decide) (by decide) (j x) env z
    have hi := ih (pile 3 (j x) r)
    rw [pile_comm 0 _ r 3 _ (by decide), pile_comm 1 _ _ 3 _ (by decide),
        pile_comm 0 (forest j l) _ _ _ (by decide)] at hi
    have h₄ := fits_move (i:=3) (j:=0) (u:=2) (by decide) (by decide) (j x) env (pile 0 (forest j l) r)
    have he := h₁.join (h₂.join (h₃.join ((Fits.again0 hi).join (h₄.join (fits_pack _ _ _ _ _)))))
    dsimp only [z] at he
    rw [pile_comm 1 (f x) _ 0 (g x) (by decide),
        pile_comm 1 _ r 0 (forest g l) (by decide),
        pile_comm 1 _ _ 0 (forest g l) (by decide)] at he
    have he' := fits_pair (c := fun _ => .pass) he
    rw [pile_comm 0 (.fork ..) _ 1 _ (by decide),
        pile_comm 0 (.fork ..) r 1 _ (by decide)] at he'
    refine (fits_pair he').mono ?_
    simp only [H, Tree.count, j, forest_cons]
    omega

/-- The zipper reuses four registers above the caller's parked deck. -/
theorem zip_bounded {X : Type*} (f g : X → Tree) (l : List X) (env : Env) (r : Deck)
    (base : ℕ) (hr : DeckCap base r) :
    let V := (forest f l).count + (forest g l).count + 1
    BoundedFits env zipCommand (pile 0 (.fork (forest f l) (forest g l)) r)
      (pile 0 (forest (fun x => .fork (f x) (g x)) l) r)
      (200 * V) (base + 201 * V) (200 * V) := by
  refine BoundedFits.of_fits (zip_fits f g l env r) (fun i => ?_) le_rfl
  have h := hr.pile 0 (.fork (forest f l) (forest g l)) i
  simp only [Tree.count] at h
  omega

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
