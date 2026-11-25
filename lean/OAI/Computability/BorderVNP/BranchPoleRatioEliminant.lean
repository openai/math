import OAI.Computability.BorderVNP.BranchNonsingularFiber
import OAI.Computability.BorderVNP.BranchPoleEliminant
import OAI.Computability.BorderVNP.BranchPoleRatio
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # A bounded eliminant for a rational function on a finite parameter fiber

Apply the Macaulay minor to the equations obtained by adjoining the inverse of
the denominator. The bidegree bound is uniform in the number of fiber equations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

/-- A nonzero bivariate equation for every defined value of the rational function on the
fiber over `φ`, with separate bounds in the value variable and the base parameter. -/
theorem defined_fiber_ratio_eliminant {K L I : Type*} [Field K] [Field L] [IsAlgClosed L]
    [Fintype I] {h d e : ℕ} (φ : Polynomial K →+* L)
    (g : I → MvPolynomial (Fin h) (Polynomial K)) (A B : MvPolynomial (Fin h) (Polynomial K))
    (hd : 2 ≤ d) (hg : ∀ i, (g i).totalDegree ≤ d) (hA : A.totalDegree ≤ d)
    (hB : B.totalDegree ≤ d) (hgt : ∀ i m, ((g i).coeff m).natDegree ≤ e)
    (hAt : ∀ m, (A.coeff m).natDegree ≤ e) (hBt : ∀ m, (B.coeff m).natDegree ≤ e)
    (hfin : {x : Fin h → L | (∀ i, eval₂ φ x (g i) = 0) ∧ eval₂ φ x B ≠ 0}.Finite) :
    ∃ Q : Polynomial (Polynomial K), Q ≠ 0 ∧ Q.natDegree ≤ eliminantWidth (h+1) (d+1) ∧
      (∀ j, (Q.coeff j).natDegree ≤ eliminantWidth (h+1) (d+1) * e) ∧
      ∀ x : Fin h → L, (∀ i, eval₂ φ x (g i) = 0) → eval₂ φ x B ≠ 0 →
        Q.eval₂ φ (eval₂ φ x A / eval₂ φ x B) = 0 := by
  obtain ⟨Q, hQ, hW, ht, he⟩ := generic_fiber_eliminant φ (ratioSystem g A B) (by omega : 3 ≤ d+1)
    (ratioSystem_totalDegree_le g A B hg hA hB) (ratioSystem_Wdegree_le g A B)
    (ratioSystem_tdegree_le g A B hgt hAt hBt) (finite_ratioSystem_parameters_of_domain φ g A B hfin)
  refine ⟨Q, hQ, hW, ht, fun x hx hden => ?_⟩
  obtain ⟨y, hy⟩ := (ratioSystem_solution_iff φ _ g A B).2 ⟨x, hx, hden, rfl⟩
  exact he _ y hy

/-- A nonzero bivariate equation for every defined value of the rational function on the
fiber over `φ`, with separate bounds in the value variable and the base parameter. -/
theorem finite_fiber_ratio_eliminant {K L I : Type*} [Field K] [Field L] [IsAlgClosed L]
    [Fintype I] {h d e : ℕ} (φ : Polynomial K →+* L)
    (g : I → MvPolynomial (Fin h) (Polynomial K)) (A B : MvPolynomial (Fin h) (Polynomial K))
    (hd : 2 ≤ d) (hg : ∀ i, (g i).totalDegree ≤ d) (hA : A.totalDegree ≤ d)
    (hB : B.totalDegree ≤ d) (hgt : ∀ i m, ((g i).coeff m).natDegree ≤ e)
    (hAt : ∀ m, (A.coeff m).natDegree ≤ e) (hBt : ∀ m, (B.coeff m).natDegree ≤ e)
    (hfin : {x : Fin h → L | ∀ i, eval₂ φ x (g i) = 0}.Finite) :
    ∃ Q : Polynomial (Polynomial K), Q ≠ 0 ∧ Q.natDegree ≤ eliminantWidth (h+1) (d+1) ∧
      (∀ j, (Q.coeff j).natDegree ≤ eliminantWidth (h+1) (d+1) * e) ∧
      ∀ x : Fin h → L, (∀ i, eval₂ φ x (g i) = 0) → eval₂ φ x B ≠ 0 →
        Q.eval₂ φ (eval₂ φ x A / eval₂ φ x B) = 0 := by
  exact defined_fiber_ratio_eliminant φ g A B hd hg hA hB hgt hAt hBt
    (hfin.subset fun _ h => h.1)

/-- A bounded eliminant when every point where the ratio is defined is a simple root.
Singular components of the cleared equations can have arbitrary dimension. -/
theorem nonsingular_fiber_ratio_eliminant {K L : Type*} [Field K] [Field L] [IsAlgClosed L]
    {h d e : ℕ} (φ : Polynomial K →+* L)
    (g : Fin h → MvPolynomial (Fin h) (Polynomial K)) (A B : MvPolynomial (Fin h) (Polynomial K))
    (hd : 2 ≤ d) (hg : ∀ i, (g i).totalDegree ≤ d) (hA : A.totalDegree ≤ d)
    (hB : B.totalDegree ≤ d) (hgt : ∀ i m, ((g i).coeff m).natDegree ≤ e)
    (hAt : ∀ m, (A.coeff m).natDegree ≤ e) (hBt : ∀ m, (B.coeff m).natDegree ≤ e)
    (hsimple : ∀ x : Fin h → L, (∀ i, eval₂ φ x (g i) = 0) → eval₂ φ x B ≠ 0 →
      (Matrix.of fun i j => eval₂ φ x (pderiv j (g i))).det ≠ 0) :
    ∃ Q : Polynomial (Polynomial K), Q ≠ 0 ∧ Q.natDegree ≤ eliminantWidth (h+1) (d+1) ∧
      (∀ j, (Q.coeff j).natDegree ≤ eliminantWidth (h+1) (d+1) * e) ∧
      ∀ x : Fin h → L, (∀ i, eval₂ φ x (g i) = 0) → eval₂ φ x B ≠ 0 →
        Q.eval₂ φ (eval₂ φ x A / eval₂ φ x B) = 0 := by
  apply defined_fiber_ratio_eliminant φ g A B hd hg hA hB hgt hAt hBt
  apply (finite_nonsingular_roots (fun i => map φ (g i))).subset
  intro x hx
  refine ⟨fun i => ?_, ?_⟩
  · simpa only [← eval₂_eq_eval_map] using hx.1 i
  · simpa only [pderiv_map, ← eval₂_eq_eval_map] using hsimple x hx.1 hx.2

/-- The equation produced over the geometric fiber holds in the arithmetic function
field itself, by injectivity of its embedding in the algebraic closure. -/
theorem nonsingular_fiber_ratio_eliminant_over_field {K L : Type*} [Field K] [Field L]
    {h d e : ℕ} (φ : Polynomial K →+* L)
    (g : Fin h → MvPolynomial (Fin h) (Polynomial K)) (A B : MvPolynomial (Fin h) (Polynomial K))
    (hd : 2 ≤ d) (hg : ∀ i, (g i).totalDegree ≤ d) (hA : A.totalDegree ≤ d)
    (hB : B.totalDegree ≤ d) (hgt : ∀ i m, ((g i).coeff m).natDegree ≤ e)
    (hAt : ∀ m, (A.coeff m).natDegree ≤ e) (hBt : ∀ m, (B.coeff m).natDegree ≤ e)
    (hsimple : let ψ := (algebraMap L (AlgebraicClosure L)).comp φ
      ∀ x : Fin h → AlgebraicClosure L, (∀ i, eval₂ ψ x (g i) = 0) → eval₂ ψ x B ≠ 0 →
        (Matrix.of fun i j => eval₂ ψ x (pderiv j (g i))).det ≠ 0) :
    ∃ Q : Polynomial (Polynomial K), Q ≠ 0 ∧ Q.natDegree ≤ eliminantWidth (h+1) (d+1) ∧
      (∀ j, (Q.coeff j).natDegree ≤ eliminantWidth (h+1) (d+1) * e) ∧
      ∀ x : Fin h → L, (∀ i, eval₂ φ x (g i) = 0) → eval₂ φ x B ≠ 0 →
        Q.eval₂ φ (eval₂ φ x A / eval₂ φ x B) = 0 := by
  let incl := algebraMap L (AlgebraicClosure L)
  obtain ⟨Q, hQ, hW, ht, hr⟩ := nonsingular_fiber_ratio_eliminant (incl.comp φ)
    g A B hd hg hA hB hgt hAt hBt hsimple
  refine ⟨Q, hQ, hW, ht, fun x hx hb => incl.injective ?_⟩
  have he (p : MvPolynomial (Fin h) (Polynomial K)) :
      eval₂ (incl.comp φ) (incl ∘ x) p = incl (eval₂ φ x p) :=
    (eval₂_comp_left incl φ x p).symm
  have hr' := hr (incl ∘ x) (fun i => (he _).trans ((congrArg incl (hx i)).trans (map_zero _)))
    (by rw [he]; exact (map_ne_zero_iff _ incl.injective).2 hb)
  rwa [Polynomial.hom_eval₂, map_div₀, ← he, ← he, map_zero]

/-- A polynomial exponent bounds the value-degree cutoff when the input degree has
at most `b+1` bits. The extra variable is the inverse of the denominator. -/
theorem ratioEliminant_width_le {h d b : ℕ} (hd : d ≤ 2 ^ b) :
    eliminantWidth (h+1) (d+1) ≤ 2 ^ (((b+2) * (4*(h+3)) + 2) * (h+1)) := by
  let k := 4 * (h+3)
  have h₁ : d+1 ≤ 2 ^ (b+1) := by rw [pow_succ]; have := Nat.two_pow_pos b; omega
  have h₂ : 2*(d+1) ≤ 2 ^ (b+2) := by rw [pow_succ' 2 (b+1)]; omega
  have hm : (2*(d+1))^k ≤ 2 ^ ((b+2)*k) := by
    rw [pow_mul 2 (b+2) k]
    exact Nat.pow_le_pow_left h₂ _
  have hn : d+1 ≤ 2 ^ ((b+2)*k) := by
    have hpos : 1 ≤ k := by dsimp [k]; omega
    exact h₁.trans (Nat.pow_le_pow_right (by decide) (by nlinarith only [hpos]))
  have hbase : (2*(d+1))^k + (d+1) + 1 ≤ 2 ^ ((b+2)*k + 2) := by
    rw [pow_add]
    have := Nat.two_pow_pos ((b+2)*k)
    omega
  rw [pow_mul]
  exact Nat.pow_le_pow_left hbase _

/-- The parameter-degree cutoff also has polynomial bit length, including the input
parameter degree factor in the Macaulay determinant. -/
theorem ratioEliminant_parameterDegree_le {h d e b : ℕ} (hd : d ≤ 2 ^ b) (he : e ≤ 2 ^ b) :
    eliminantWidth (h+1) (d+1) * e ≤ 2 ^ ((((b+2) * (4*(h+3)) + 2) * (h+1)) + b) := by
  rw [pow_add]
  exact Nat.mul_le_mul (ratioEliminant_width_le hd) he

end Branch

end BorderVNP
end Computability
end OAI
