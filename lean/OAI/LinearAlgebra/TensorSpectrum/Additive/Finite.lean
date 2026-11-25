import OAI.LinearAlgebra.TensorSpectrum.Additive.States
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Positivity

/-! The compactness obstruction can be restricted to finitely many coordinates,
including the unit. Outside those coordinates, zero is a valid box coordinate.
This is the concrete finite-dimensional input to rational linear elimination. -/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommSemiring S] [PartialOrder S]

noncomputable def StateConstraint.coordinates (T : S) : StateConstraint S → Finset S := by
  classical
  exact fun c => match c with
    | .zero => {0}
    | .one => {1}
    | .add x y => {x + y, x, y}
    | .order x y _ => {x, y}
    | .detect s => {T * s, s}

theorem StateConstraint.holds_congr (T : S) (k : ℕ) (c : StateConstraint S)
    {f g : S → ℝ} (h : ∀ x ∈ c.coordinates T, f x = g x) :
    c.Holds T k f ↔ c.Holds T k g := by
  classical
  cases c with
  | zero => simp only [StateConstraint.Holds, h 0 (by simp [StateConstraint.coordinates])]
  | one => simp only [StateConstraint.Holds, h 1 (by simp [StateConstraint.coordinates])]
  | add x y =>
    simp only [StateConstraint.Holds, h (x + y) (by simp [StateConstraint.coordinates]),
      h x (by simp [StateConstraint.coordinates]), h y (by simp [StateConstraint.coordinates])]
  | order x y hxy =>
    simp only [StateConstraint.Holds, h x (by simp [StateConstraint.coordinates]),
      h y (by simp [StateConstraint.coordinates])]
  | detect s =>
    simp only [StateConstraint.Holds, h (T * s) (by simp [StateConstraint.coordinates]),
      h s (by simp [StateConstraint.coordinates])]

/-- A finite obstruction includes only these coordinate bounds; no infinite
system is passed silently to the finite rational cone theorem. -/
theorem finite_coordinate_obstruction (T : S) (k : ℕ) (R : S → ℕ)
    (hnone : stateSet T k = ∅) :
    ∃ (F : Finset (StateConstraint S)) (U : Finset S),
      0 ∈ U ∧ 1 ∈ U ∧
      (∀ c ∈ F, c.coordinates T ⊆ U) ∧
      ¬ ∃ f : S → ℝ, (∀ s ∈ U, f s ∈ Icc 0 (R s : ℝ)) ∧
        ∀ c ∈ F, c.Holds T k f := by
  classical
  obtain ⟨F, hF⟩ := finite_inconsistent_subsystem T k R hnone
  let U : Finset S := {0, 1} ∪ F.biUnion (fun c => c.coordinates T)
  have hsub : ∀ c ∈ F, c.coordinates T ⊆ U := by
    intro c hc x hx
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨c, hc, hx⟩))
  refine ⟨F, U, by simp [U], by simp [U], hsub, ?_⟩
  rintro ⟨f, hbox, hconstraints⟩
  let g : S → ℝ := fun s => if s ∈ U then f s else 0
  apply hF
  refine ⟨g, ?_, ?_⟩
  · intro s
    by_cases hs : s ∈ U
    · simpa only [g, ite_eq_left hs] using hbox s hs
    · simp only [g, ite_eq_right hs, mem_Icc, le_refl, true_and]
      positivity
  · intro c hc
    apply (c.holds_congr T k (f := f) (g := g) ?_).mp (hconstraints c hc)
    intro x hx
    simp only [g, ite_eq_left (hsub c hc hx)]

end OAI.LinearAlgebra.TensorSpectrum
