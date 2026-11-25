import OAI.Computability.BorderVNP.BranchCurveBoxRatio
import OAI.Computability.BorderVNP.BranchCurveParameterCoefficients
import OAI.Computability.BorderVNP.BranchPoleRatioEliminant

/-! # Bounded eliminants for all the coordinate functions and box tests

The denominator always contains the Jacobian. Its nonvanishing removes the
singular components before elimination. Coordinate eliminants use `xᵢJ/J`,
and box eliminants use the explicitly cleared `tʲxᵅ/J`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial ResidueBox Residue.JetRing

variable {E L : Type*} [Field E] [Field L] {h : ℕ}

private theorem chart_ratio_eliminant (φ : Polynomial E →+* L)
    (g : Fin h → MvPolynomial (Option (Fin h)) E) (A U : MvPolynomial (Option (Fin h)) E)
    (d : ℕ) (hd : 2 ≤ d) (hg : ∀ i, (g i).totalDegree ≤ d)
    (hA : A.totalDegree ≤ d) (hB : (U * boxJacobian g).totalDegree ≤ d) (x : Fin h → L)
    (hx : ∀ i, eval₂Hom (φ.comp Polynomial.C) (fun j : Option (Fin h) => j.elim (φ Polynomial.X) x) (g i) = 0)
    (hden : eval₂Hom (φ.comp Polynomial.C) (fun j : Option (Fin h) => j.elim (φ Polynomial.X) x) (U * boxJacobian g) ≠ 0) :
    let v := eval₂Hom (φ.comp Polynomial.C) (fun j : Option (Fin h) => j.elim (φ Polynomial.X) x)
    ∃ Q : Polynomial (Polynomial E), Q ≠ 0 ∧ Q.natDegree ≤ eliminantWidth (h+1) (d+1) ∧
      (∀ k, (Q.coeff k).natDegree ≤ eliminantWidth (h+1) (d+1) * d) ∧
      Q.eval₂ φ (v A / v (U * boxJacobian g)) = 0 := by
  let T := optionEquivRight E (Fin h)
  let B := U * boxJacobian g
  let ψ := (algebraMap L (AlgebraicClosure L)).comp φ
  have simple (y : Fin h → AlgebraicClosure L) (hy : eval₂ ψ y (T B) ≠ 0) :
      (Matrix.of fun i j => eval₂ ψ y (pderiv j (T (g i)))).det ≠ 0 := by
    let v := eval₂Hom (ψ.comp Polynomial.C) (fun j : Option (Fin h) => j.elim (ψ Polynomial.X) y)
    have hden' : v (U * boxJacobian g) ≠ 0 :=
      fun hz => hy ((eval_parameter_coefficients ψ y B).trans hz)
    rw [map_mul, eval_boxJacobian] at hden'
    have e : (Matrix.of fun i j => eval₂ ψ y (pderiv j (T (g i)))) =
        chartJacobian (ψ.comp Polynomial.C) (fun j : Option (Fin h) => j.elim (ψ Polynomial.X) y) g := by
      ext i j
      rw [Matrix.of_apply, parameter_pderiv, eval_parameter_coefficients]
      rfl
    rw [e]
    exact right_ne_zero_of_mul hden'
  obtain ⟨Q, hQ, hW, hD, ha⟩ := nonsingular_fiber_ratio_eliminant_over_field φ (fun i => T (g i))
    (T A) (T B) hd (fun i => (parameter_totalDegree_le _).trans (hg i))
    ((parameter_totalDegree_le A).trans hA) ((parameter_totalDegree_le B).trans hB)
    (fun i m => (parameter_coeff_natDegree_le _ m).trans (hg i))
    (fun m => (parameter_coeff_natDegree_le A m).trans hA)
    (fun m => (parameter_coeff_natDegree_le B m).trans hB) (fun y _ => simple y)
  refine ⟨Q, hQ, hW, hD, ?_⟩
  have hAx := ha x (fun i => (eval_parameter_coefficients φ x (g i)).trans (hx i))
    (fun e => hden ((eval_parameter_coefficients φ x B).symm.trans e))
  rwa [eval_parameter_coefficients φ x A, eval_parameter_coefficients φ x B] at hAx

/-- The affine coordinates of a nonsingular solution satisfy bivariate
eliminants with bounded degrees in both the coordinate and the parameter. -/
theorem chart_coordinate_eliminants (φ : Polynomial E →+* L)
    (g : Fin h → MvPolynomial (Option (Fin h)) E) (d : ℕ) (hd : 2 ≤ d)
    (hS : (∑ j, (g j).totalDegree) + 1 ≤ d) (x : Fin h → L)
    (hx : ∀ i, eval₂Hom (φ.comp Polynomial.C)
      (fun j : Option (Fin h) => j.elim (φ Polynomial.X) x) (g i) = 0)
    (hJ : eval₂Hom (φ.comp Polynomial.C)
      (fun j : Option (Fin h) => j.elim (φ Polynomial.X) x) (boxJacobian g) ≠ 0) :
    ∀ i : Fin h, ∃ Q : Polynomial (Polynomial E), Q ≠ 0 ∧
      Q.natDegree ≤ eliminantWidth (h+1) (d+1) ∧
      (∀ k, (Q.coeff k).natDegree ≤ eliminantWidth (h+1) (d+1) * d) ∧
      Q.eval₂ φ (x i) = 0 := by
  intro i
  let A := X (some i) * boxJacobian g
  have hg (j) : (g j).totalDegree ≤ d := (Finset.single_le_sum
    (fun l _ => Nat.zero_le (g l).totalDegree) (Finset.mem_univ j)).trans (Nat.le_succ _ |>.trans hS)
  have hA : A.totalDegree ≤ d := (totalDegree_mul ..).trans (by
    rw [totalDegree_X, Nat.add_comm]
    exact (Nat.add_le_add_right (boxJacobian_degree g) 1).trans hS)
  have hB : (1 * boxJacobian g).totalDegree ≤ d := by
    simpa using (boxJacobian_degree g).trans (Nat.le_succ _ |>.trans hS)
  obtain ⟨Q, hQ, hW, hD, hr⟩ := chart_ratio_eliminant φ g A 1 d hd hg hA hB x hx (by simpa using hJ)
  refine ⟨Q, hQ, hW, hD, ?_⟩
  rwa [one_mul, show A = X (some i) * boxJacobian g from rfl, map_mul, eval₂Hom_X',
    Option.elim_some, mul_div_cancel_right₀ _ hJ] at hr

/-- A uniform degree bound for the cleared coordinate and box quotients. -/
def boxEliminantInputDegree (h H S : ℕ) : ℕ := 2 + H + h * H + S

/-- Coordinate and ratio eliminants at one actual simple root, over the coefficient
field of the equations. Both degree bounds are independent of the chosen root. -/
theorem chart_box_eliminants (φ : Polynomial E →+* L) (t : Lˣ) (ht : φ Polynomial.X = t)
    (x : Fin h → L) (g : Fin h → MvPolynomial (Option (Fin h)) E) (H : ℕ)
    (hx : ∀ i, eval₂Hom (φ.comp Polynomial.C) (fun j : Option (Fin h) => j.elim (t : L) x) (g i) = 0)
    (hJ : (chartJacobian (φ.comp Polynomial.C) (fun j : Option (Fin h) => j.elim (t : L) x) g).det ≠ 0) :
    let S := ∑ i, (g i).totalDegree
    let d := boxEliminantInputDegree h H S
    let C := eliminantWidth (h+1) (d+1)
    let J := (chartJacobian (φ.comp Polynomial.C) (fun j : Option (Fin h) => j.elim (t : L) x) g).det
    (∀ i : Fin h, ∃ R : Polynomial (Polynomial E), R ≠ 0 ∧ R.natDegree ≤ C ∧ R.eval₂ φ (x i) = 0) ∧
    (∀ e : {a : Exponent (Fin h) // InBox H a}, ∃ Q : Polynomial (Polynomial E), Q ≠ 0 ∧
      (∀ j ∈ Q.support, (Q.coeff j).natDegree ≤ C*d) ∧
      Q.eval₂ φ ((t : L) ^ (e.val none) * (∏ i, x i ^ (e.val (some i)).toNat) / J) = 0) := by
  let S := ∑ i, (g i).totalDegree
  let d := boxEliminantInputDegree h H S
  let v := eval₂Hom (φ.comp Polynomial.C) (fun j : Option (Fin h) => j.elim (t : L) x)
  have hd : 2 ≤ d := by dsimp [d, boxEliminantInputDegree]; omega
  have hS : S + 1 ≤ d := by dsimp [d, boxEliminantInputDegree]; omega
  have hg (i) : (g i).totalDegree ≤ d := (Finset.single_le_sum
    (fun j _ => Nat.zero_le (g j).totalDegree) (Finset.mem_univ i)).trans (Nat.le_succ S |>.trans hS)
  have hx' : ∀ i, eval₂Hom (φ.comp Polynomial.C) (fun j : Option (Fin h) => j.elim (φ Polynomial.X) x) (g i) = 0 :=
    ht ▸ hx
  have hjv : v (boxJacobian g) ≠ 0 := by
    change eval₂Hom _ _ (boxJacobian g) ≠ 0
    rw [eval_boxJacobian]
    exact hJ
  dsimp only
  constructor
  · intro i
    obtain ⟨Q, hQ, hW, _, hr⟩ := chart_coordinate_eliminants φ g d hd hS x hx' (ht ▸ hjv) i
    exact ⟨Q, hQ, hW, hr⟩
  · intro e
    let U : MvPolynomial (Option (Fin h)) E := X none ^ (-(e.val none)).toNat
    have hA : (boxNumerator (E := E) e.val).totalDegree ≤ d :=
      (boxNumerator_degree _ e.property).trans (by simp only [Fintype.card_fin]; dsimp [d, boxEliminantInputDegree]; omega)
    have hB : (U * boxJacobian g).totalDegree ≤ d := (boxDenominator_degree _ _ e.property).trans (by
      dsimp [d, boxEliminantInputDegree, S]; omega)
    obtain ⟨Q, hQ, _, hD, hr⟩ := chart_ratio_eliminant φ g (boxNumerator e.val) U d hd hg hA hB x hx'
      (by rw [ht, map_mul]; apply mul_ne_zero _ hjv; simp [U])
    refine ⟨Q, hQ, fun k _ => hD k, ?_⟩
    rw [ht] at hr
    exact (eval_boxRatio (φ.comp Polynomial.C) (t : L) x g e.val) ▸ hr

end Branch

end BorderVNP
end Computability
end OAI
