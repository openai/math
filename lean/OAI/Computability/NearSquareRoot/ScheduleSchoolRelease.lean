import OAI.Computability.IntegerMultiplication.SM.Output
import OAI.Computability.NearSquareRoot.ShortWordSpace

/-!
# Physical space of the released stack machine

The completed implementation first simulates the stack transitions. It then
switches to the output routine and drains the answer stack onto a fresh tape.
Both parts contribute to the visited cells.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Schoolbook

open IntegerMultiplication

/-- Release an actual stack computation, including the final output copy,
while bounding every head's absolute coordinates at every prefix. -/
theorem complete_run_fence {A Q I : Type} [DecidableEq I] [Fintype I]
    {n H : ℕ} {i k : I} {s : List A} {q} {g : SM.Rule A Q I} {x}
    (h : Trace (SM.advance g) (SM.origin q i s) n x) (hg : SM.advance g x = none)
    (height : ∀ {u z}, u ≤ n → Trace (SM.advance g) (SM.origin q i s) u z →
      ∀ j, (z.stack j).length ≤ H) :
    let load : Option I → TM.Tape (Option A) := fun j => if j = some i
      then TM.Tape.loaded none (s.map some) else TM.Tape.loaded none []
    let init : TM.Config _ _ _ := ⟨some (Sum.inl q), load⟩
    let time := 2 * n + 1 + (x.stack k).length
    ∃ done, Trace (TM.advance (SM.complete k g)) init time done ∧
      TM.advance (SM.complete k g) done = none ∧
      TM.whole none ((x.stack k).map some) (done.tape none) ∧
      ∀ u ≤ time, ∀ z, Trace (TM.advance (SM.complete k g)) init u z →
        ∀ j, -2 * (H : ℤ) - 2 ≤ (z.tape j).pos ∧ (z.tape j).pos ≤ 2 * (H : ℤ) + 2 := by
  let blank : TM.Tape (Option A) := TM.Tape.loaded none []
  let tape : I → TM.Tape (Option A) := fun j =>
    if j = i then TM.Tape.loaded none (s.map some) else blank
  let stackInit : TM.Config (Option A) (SM.PC A Q I) I := ⟨.inl q, tape⟩
  have rep : SM.faithful (SM.origin q i s).stack tape := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa [SM.origin, tape] using SM.display_loaded s
    · simpa [SM.origin, tape, hj, blank] using SM.display_loaded ([] : List A)
  obtain ⟨T, _, full⟩ := SM.simulate h tape rep
  have sim : Trace (TM.advance (SM.toTM g)) stackInit (2*n) ⟨.inl x.pc, T⟩ := full
  let init := SM.configOut stackInit blank
  have eqInit : init = TM.Config.mk (some (Sum.inl q)) (fun j =>
      if j = some i then TM.Tape.loaded none (s.map some) else blank) := by
    unfold init SM.configOut
    congr 1
    funext j
    cases j <;> simp [stackInit, tape]
  dsimp only
  change ∃ done, _
  obtain ⟨done, run, halt, out⟩ := SM.complete_run (k := k) h hg
  refine ⟨done, run, halt, out, ?_⟩
  rw [← eqInit]
  have small (u : ℕ) (hu : u ≤ 2*n) (z) (hz : Trace (TM.advance (SM.complete k g)) init u z)
      (j : Option I) : -(H : ℤ) - 1 ≤ (z.tape j).pos ∧ (z.tape j).pos ≤ (H : ℤ) + 1 := by
    obtain ⟨v, pre, _⟩ := trace_split sim hu
    have lift := SM.lift_many (k := k) pre blank
    have eq := trace_endpoint_unique hz lift
    subst z
    cases j with
    | none => change -(H : ℤ) - 1 ≤ 0 ∧ 0 ≤ (H : ℤ) + 1; omega
    | some j =>
      change -(H : ℤ) - 1 ≤ (v.tape j).pos ∧ (v.tape j).pos ≤ (H : ℤ) + 1
      have fence := stack_fence h tape rep j H (fun hle tr => height hle tr j) hu pre
      have pos : (tape j).pos = 0 := by by_cases hj : j = i <;> simp [tape, hj, blank, TM.Tape.loaded]
      dsimp only at fence
      rw [pos, zero_add] at fence
      have size := height (Nat.zero_le _) (.nil _) j
      omega
  have cap := height (Nat.le_refl _) h k
  intro u hu z hz j
  by_cases cut : u ≤ 2*n
  · have := small u cut z hz j
    omega
  · obtain ⟨v, pre, tail⟩ := trace_split hz (k := 2*n) (by omega)
    have := small _ le_rfl v pre j
    have := head_excursion tail j
    omega

/-- Release an actual stack computation, including the final output copy,
while bounding the distinct visited cells of its entire physical trace. -/
theorem complete_run_space {A Q I : Type} [DecidableEq I] [Fintype I]
    {n H : ℕ} {i k : I} {s : List A} {q} {g : SM.Rule A Q I} {x}
    (h : Trace (SM.advance g) (SM.origin q i s) n x) (hg : SM.advance g x = none)
    (height : ∀ {u z}, u ≤ n → Trace (SM.advance g) (SM.origin q i s) u z →
      ∀ j, (z.stack j).length ≤ H) :
    let load : Option I → TM.Tape (Option A) := fun j => if j = some i
      then TM.Tape.loaded none (s.map some) else TM.Tape.loaded none []
    let init : TM.Config _ _ _ := ⟨some (Sum.inl q), load⟩
    let time := 2 * n + 1 + (x.stack k).length
    ∃ done, Trace (TM.advance (SM.complete k g)) init time done ∧
      TM.advance (SM.complete k g) done = none ∧
      TM.whole none ((x.stack k).map some) (done.tape none) ∧
      VisitsAtMost (SM.complete k g) init time (Fintype.card (Option I) * (4 * H + 5)) := by
  obtain ⟨done, run, halt, out, fence⟩ := complete_run_fence (k := k) h hg height
  refine ⟨done, run, halt, out, ?_⟩
  have cover := visitsAtMost_of_common_fence _ _ fence
  convert cover using 2
  omega

end Schoolbook

end NearSquareRoot
end Computability
end OAI
