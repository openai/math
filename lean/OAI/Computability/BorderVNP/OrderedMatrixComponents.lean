import OAI.Computability.BorderVNP.OrderedModel
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Marking the source word length in a substitution

Multiplying each substituted letter by a central formal indeterminate lets one recover
the homogeneous part *before* the substitution, even when the substituted letters have
nonzero constant terms or take values in a matrix algebra.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Ordered

variable {K σ A : Type*} [CommRing K] [Ring A] [Algebra K A]

/-- Coefficient of a central marker recording the number of source letters. -/
noncomputable def markedComponent (d : ℕ) (v : σ → A) (p : WordPoly K σ) : A :=
  (substitute (fun x => Polynomial.C (v x) * Polynomial.X) p).coeff d

private theorem lift_marked (v : σ → A) (w : FreeMonoid σ) :
    FreeMonoid.lift (fun x => Polynomial.C (v x) * Polynomial.X) w =
      Polynomial.monomial w.toList.length (FreeMonoid.lift v w) := by
  induction w using FreeMonoid.recOn with
  | one => simp
  | of_mul x w ih =>
    rw [map_mul, FreeMonoid.lift_eval_of, ih]
    rw [Polynomial.C_mul_X_eq_monomial, Polynomial.monomial_mul_monomial]
    simp [Nat.add_comm]

/-- Word indices enumerate each word of the specified length exactly once. -/
theorem word_injective {d : ℕ} : Function.Injective (word (σ := σ) (d := d)) :=
  FreeMonoid.ofList.injective.comp List.ofFn_injective

/-- On basis words, the marker retains precisely the prescribed source length. -/
theorem markedComponent_single (d : ℕ) (v : σ → A) (w : FreeMonoid σ) (r : K) :
    markedComponent d v (MonoidAlgebra.single w r) =
      if w.toList.length = d then r • FreeMonoid.lift v w else 0 := by
  by_cases h : w.toList.length = d <;> simp [markedComponent, substitute,
    MonoidAlgebra.lift_single, lift_marked, Polynomial.coeff_monomial, h]

/-- After marking, only the length-`d` coefficients of the input polynomial are read. -/
theorem markedComponent_eq_sum [Fintype σ] (d : ℕ) (v : σ → A) (p : WordPoly K σ) :
    markedComponent d v p =
      ∑ a : Fin d → σ, coefficients d p a • FreeMonoid.lift v (word a) := by
  classical
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp [markedComponent, coefficients]
  | add x y hx hy =>
    simp only [markedComponent, map_add, Polynomial.coeff_add] at hx hy ⊢
    rw [hx, hy, ← Finset.sum_add_distrib]
    simp [coefficients, MonoidAlgebra.coeff_add, add_smul]
  | single w r =>
    rw [markedComponent_single]
    by_cases h : w.toList.length = d
    · subst d
      let a := w.toList.get
      have ha : word a = w := by simp [a, word, List.ofFn_get]
      simp only [ite_true]
      symm
      rw [Finset.sum_eq_single a]
      · simp [coefficients, ha]
      · intro b _ hb
        have hne : word b ≠ w := fun e => hb (word_injective (e.trans ha.symm))
        simp [coefficients, hne.symm]
      · simp
    · simp only [h, ite_false]
      symm
      apply Finset.sum_eq_zero
      intro b _
      have hne : w ≠ word b := by
        rintro rfl
        exact h (by simp [word])
      simp [coefficients, hne]

/-- For a polynomial supported in a single source degree, extracting that degree
before substitution has the same value as the unmarked substitution. -/
theorem markedComponent_eq_substitute (d : ℕ) (v : σ → A) (p : WordPoly K σ)
    (hp : ∀ w ∈ p.coeff.support, (FreeMonoid.toList w).length = d) :
    markedComponent d v p = substitute v p := by
  conv_lhs => rw [← p.sum_coeff_single]
  conv_rhs => rw [← p.sum_coeff_single]
  change (substitute (fun x => Polynomial.C (v x) * Polynomial.X) (∑ w ∈ p.coeff.support, MonoidAlgebra.single w (p.coeff w))).coeff d =
    substitute v (∑ w ∈ p.coeff.support, MonoidAlgebra.single w (p.coeff w))
  rw [map_sum, Polynomial.finsetSum_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  change markedComponent d v (MonoidAlgebra.single w (p.coeff w)) = _
  rw [markedComponent_single]
  simp [hp w hw, substitute, MonoidAlgebra.lift_single]

end Ordered

end BorderVNP
end Computability
end OAI
