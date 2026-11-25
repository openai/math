import OAI.Computability.NearSquareRoot.BoundedProgram
import OAI.Computability.IntegerMultiplication.Prog.Compile

/-!
# Recovering an ordinary P192 task from a space-bounded task

For a fixed command, the compiler's finite register list bounds the part of
the parked deck the command can inspect. Projecting an arbitrary parked deck
to this list supplies the finite initial height required by a bounded task.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space.BoundedTask

open IntegerMultiplication IntegerMultiplication.Code

private def replaceOutside {A : Type} (active : Finset ℕ) (r frame : Reg A) : Reg A :=
  fun j => if j ∈ active then r j else frame j

private theorem replaceOutside_update {A : Type} {active : Finset ℕ} {i : ℕ}
    (hi : i ∈ active) (r frame : Reg A) (v : List A) :
    replaceOutside active (Function.update r i v) frame =
      Function.update (replaceOutside active r frame) i v := by
  funext j
  by_cases h : j = i
  · subst j; simp [replaceOutside, hi]
  · simp [replaceOutside, Function.update_of_ne h]

section
open Prog
variable {A : Type} [Fintype A] (U : List (Loc A))

/-- Arbitrary parked data on registers absent from the finite code have no effect on a run. -/
private theorem outsideRun {Γ : Scope A} {c r n s} (run : Prog.Run Γ c r n s)
    (good : Good U Γ c) (above : Above U Γ) (frame : Reg A) :
    Prog.Run Γ c (replaceOutside (used U).toFinset r frame) n
      (replaceOutside (used U).toFinset s frame) := by
  classical
  have touch {G : Scope A} {p : Prog A} (gp : Good U G p) :
      touched p ∈ (used U).toFinset := by
    simp only [used, List.mem_toFinset, List.mem_cons, List.mem_map]
    exact Or.inr ⟨(G, p), gp (sites_self _ _), rfl⟩
  induction run with
  | pass => exact .pass
  | @push Γ i x r =>
    have hi : i ∈ (used U).toFinset := touch good
    rw [replaceOutside_update hi, ← show replaceOutside (used U).toFinset r frame i = r i by
      simp [replaceOutside, hi]]
    exact .push
  | @pop Γ i r =>
    have hi : i ∈ (used U).toFinset := touch good
    rw [replaceOutside_update hi, ← show replaceOutside (used U).toFinset r frame i = r i by
      simp [replaceOutside, hi]]
    exact .pop
  | @look Γ i f r t s child ih =>
    have hi : i ∈ (used U).toFinset := touch good
    apply Prog.Run.look
    rw [show replaceOutside (used U).toFinset r frame i = r i by simp [replaceOutside, hi]]
    apply ih _ above
    intro loc hl
    apply good
    rw [sites]
    simp only [List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨_, mem_options _, hl⟩
  | @join Γ c d r n s m t left right ih jh =>
    refine .join (ih ?_ above) (jh ?_ above)
    · intro loc hl; apply good; rw [sites]; simp [hl]
    · intro loc hl; apply good; rw [sites]; simp [hl]
  | @tie Γ c r n s child ih =>
    have hc : Good U (c :: Γ) c := by intro loc hl; apply good; rw [sites]; simp [hl]
    apply Prog.Run.tie (ih hc ?_)
    intro i a hi
    cases i with
    | zero =>
      have : c = a := by simpa using hi
      subst a; exact hc
    | succ i =>
      simpa using above i a (by simpa using hi)
  | @again Γ i c r n s hi child ih =>
    refine .again hi (ih (above _ _ hi) ?_)
    intro j d hj
    simp only [List.getElem?_drop] at hj
    simpa [List.drop_drop, add_comm] using above _ _ hj

end

/-- A bounded task yields the original task specification even for parked
decks whose heights have no finite common bound over infinitely many register
names. A fixed closed command touches only finitely many registers. -/
theorem forget {I : Type*} {time space : I → ℕ} {input output : I → Tree}
    (h : BoundedTask time space input output) : Code.Task time input output := by
  classical
  obtain ⟨c, C, cert⟩ := h
  apply Code.Task.make c C
  intro i r
  let : Fintype Ltr := ⟨{.node, .sep, .bit true, .bit false}, by
    intro a; cases a with
    | node | sep => simp
    | bit a => cases a <;> simp⟩
  let U := Prog.sites [] c
  let active := (Prog.used U).toFinset
  let localDeck : Deck := fun j => if j ∈ active then r j else []
  let base := active.sup (fun j => (letters r j).length)
  have hr : ∀ j, (letters localDeck j).length ≤ base := by
    intro j
    by_cases hj : j ∈ active
    · simpa [localDeck, letters, hj, base] using
        (Finset.le_sup (f := fun j => (letters r j).length) hj)
    · simp [localDeck, letters, hj]
  have localRun := (cert i [] localDeck base hr).fits
  obtain ⟨n, hn, run⟩ := localRun
  have f (x : Tree) : replaceOutside active (letters (pile 0 x localDeck)) (letters r) =
      letters (pile 0 x r) := by
    funext j
    have h0 : 0 ∈ active := by simp [active, Prog.used]
    by_cases hj : j = 0
    · subst j
      simp [replaceOutside, h0, letters, localDeck]
    · by_cases ha : j ∈ active <;>
        simp [replaceOutside, ha, letters, localDeck, hj]
  refine ⟨n, hn, ?_⟩
  have whole := outsideRun U run (fun _ ha => ha) (by intro i; simp) (letters r)
  exact (f (input i)) ▸ (f (output i)) ▸ whole

end Space.BoundedTask

end NearSquareRoot
end Computability
end OAI
