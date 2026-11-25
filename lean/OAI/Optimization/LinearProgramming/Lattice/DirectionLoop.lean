import OAI.Optimization.LinearProgramming.Lattice.Induction
import OAI.Optimization.LinearProgramming.Lattice.ProjectionMatrix

/-! Correctness of the bounded iteration that builds the comparison directions. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open SignType WithLp

variable {p : ℕ}

/-- Append a new comparison direction while the residual is nonzero. Earlier vectors are
stored in reverse order for the rational projector; the result is in significance order. -/
def directionLoop (next : List (Fin p → ℤ) → Option (Fin p → ℤ)) :
    ℕ → List (Fin p → ℤ) → List (Fin p → ℤ)
  | 0, _ => []
  | fuel + 1, old =>
    match next old with
    | none => []
    | some z => z :: directionLoop next fuel (z :: old)

theorem directionLoop_correct (next : List (Fin p → ℤ) → Option (Fin p → ℤ))
    (v : Fin p → ℝ) (M D : ℤ)
    (hstop : ∀ old, next old = none → toLp 2 v ∈ integerDirectionSpan old)
    (hstep : ∀ old z, next old = some z → (∀ i, |z i| ≤ D) ∧
        toLp 2 (realCoordinates z) ∉ integerDirectionSpan old ∧
        ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ M →
          (∀ y ∈ integerDirectionSpan old, realCoordinates a ⬝ᵥ y.ofLp = 0) →
          a ⬝ᵥ z ≠ 0 → sign (a ⬝ᵥ z) = sign (realCoordinates a ⬝ᵥ v)) :
    (directionLoop next p []).length ≤ p ∧
      (∀ z ∈ directionLoop next p [], ∀ i, |z i| ≤ D) ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ M →
        leadingSign ((directionLoop next p []).map (dotProduct a)) =
          sign (realCoordinates a ⬝ᵥ v) := by
  classical
  have go (k : ℕ) (old : List (Fin p → ℤ))
      (hk : p ≤ Module.finrank ℝ (integerDirectionSpan old) + k) :
      (directionLoop next k old).length ≤ k ∧
        (∀ z ∈ directionLoop next k old, ∀ i, |z i| ≤ D) ∧
        ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ M →
          (∀ y ∈ integerDirectionSpan old, realCoordinates a ⬝ᵥ y.ofLp = 0) →
          leadingSign ((directionLoop next k old).map (dotProduct a)) =
            sign (realCoordinates a ⬝ᵥ v) := by
    induction k generalizing old with
    | zero =>
      have hle := (integerDirectionSpan old).finrank_le
      have heq : Module.finrank ℝ (integerDirectionSpan old) =
          Module.finrank ℝ (EuclideanSpace ℝ (Fin p)) := by
        rw [finrank_euclideanSpace_fin] at hle ⊢
        omega
      have hv : toLp 2 v ∈ integerDirectionSpan old :=
        Submodule.eq_top_of_finrank_eq heq ▸ Submodule.mem_top
      refine ⟨by simp [directionLoop], by simp [directionLoop], ?_⟩
      intro a _ ha
      have he := ha (toLp 2 v) hv
      simp [directionLoop, leadingSign, he]
    | succ k ih =>
      cases h : next old with
      | none =>
        rw [directionLoop, h]
        refine ⟨by simp, by simp, ?_⟩
        intro a _ ha
        have he := ha (toLp 2 v) (hstop old h)
        simp [leadingSign, he]
      | some z =>
        rw [directionLoop, h]
        obtain ⟨hz, hnew, htest⟩ := hstep old z h
        have hw : toLp 2 (realCoordinates z) ∈ integerDirectionSpan (z :: old) :=
          (show ℝ ∙ toLp 2 (realCoordinates z) ≤ integerDirectionSpan (z :: old) from le_sup_right)
            (Submodule.subset_span (Set.mem_singleton _))
        have hlt : integerDirectionSpan old < integerDirectionSpan (z :: old) :=
          lt_of_le_of_ne le_sup_left (fun he => hnew (he ▸ hw))
        have hdim := Submodule.finrank_lt_finrank_of_lt hlt
        obtain ⟨hlen, hb, hall⟩ := ih (z :: old) (by omega)
        refine ⟨by simpa using hlen, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hz
          · exact hb x hx
        · intro a ha hS
          simp only [List.map_cons, leadingSign]
          split_ifs with hzero
          · exact hall a ha (annihilates_span_extension _ a z hS hzero)
          · exact htest a ha hS hzero
  obtain ⟨hlen, hb, hall⟩ := go p [] (by simp [integerDirectionSpan])
  refine ⟨hlen, hb, fun a ha => hall a ha ?_⟩
  intro y hy
  simp only [integerDirectionSpan, Submodule.mem_bot] at hy
  simp [hy]

end Lattice
end LinearProgramming
end Optimization
end OAI
