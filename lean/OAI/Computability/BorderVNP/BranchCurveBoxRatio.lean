import OAI.Computability.BorderVNP.BranchJacobianDegree
import OAI.Computability.BorderVNP.ResidueJetJacobian
import OAI.Computability.BorderVNP.ResidueBox

/-!
# Polynomial presentation of a box differential

For a signed time exponent `j`, put `t^max(j,0)` in the numerator and
`t^max(-j,0)` in the denominator. The other denominator factor is the
polynomial Jacobian of the given equations. Its total degree and the bound
on all box exponents bound both polynomial degrees before elimination.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial ResidueBox Residue.JetRing

variable {E σ : Type*} [Field E] [Fintype σ] [DecidableEq σ]

/-- The polynomial Jacobian in all the coordinates, with partial derivatives
only in the `some` coordinates. -/
noncomputable def boxJacobian (g : σ → MvPolynomial (Option σ) E) : MvPolynomial (Option σ) E :=
  (Matrix.of fun i j => pderiv (some j) (g i)).det

/-- Numerator obtained by clearing the negative time exponent. -/
noncomputable def boxNumerator (e : Exponent σ) : MvPolynomial (Option σ) E :=
  X none ^ (e none).toNat * ∏ i, X (some i) ^ (e (some i)).toNat

/-- Denominator obtained by clearing the negative time exponent. -/
noncomputable def boxDenominator (g : σ → MvPolynomial (Option σ) E) (e : Exponent σ) :
    MvPolynomial (Option σ) E := X none ^ (-e none).toNat * boxJacobian g

/-- The polynomial determinant specializes to the Jacobian evaluated on the chart. -/
theorem eval_boxJacobian {L : Type*} [Field L] (φ : E →+* L) (z : Option σ → L)
    (g : σ → MvPolynomial (Option σ) E) : eval₂Hom φ z (boxJacobian g) = (chartJacobian φ z g).det := by
  rw [boxJacobian, RingHom.map_det]
  rfl

/-- The Jacobian determinant's total degree is bounded by the sum of the equation degrees. -/
theorem boxJacobian_degree (g : σ → MvPolynomial (Option σ) E) :
    (boxJacobian g).totalDegree ≤ ∑ i, (g i).totalDegree := by
  rw [boxJacobian, Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro π _
  apply (totalDegree_smul_le ..).trans
  apply (totalDegree_finsetProd ..).trans
  calc
    _ ≤ ∑ i, (g (π i)).totalDegree := Finset.sum_le_sum fun i _ => pderiv_degree _ _
    _ = _ := Equiv.sum_comp π (fun i => (g i).totalDegree)

omit [DecidableEq σ] in
/-- The cleared numerator has at most `H` degrees in each coordinate including time. -/
theorem boxNumerator_degree {H : ℕ} (e : Exponent σ) (he : InBox H e) :
    (boxNumerator (E := E) e).totalDegree ≤ H + Fintype.card σ * H := by
  apply (totalDegree_mul ..).trans (Nat.add_le_add ?_ ?_)
  · rw [totalDegree_X_pow]
    exact Int.toNat_le.mpr he.1.2
  · apply (totalDegree_finsetProd ..).trans
    calc
      _ ≤ ∑ _ : σ, H := Finset.sum_le_sum fun i _ =>
        (totalDegree_X_pow (some i) ((e (some i)).toNat)).le.trans (Int.toNat_le.mpr (he.2 i).2)
      _ = _ := by simp

/-- The time factor adds at most the radius to the Jacobian degree. -/
theorem boxDenominator_degree {H : ℕ} (g : σ → MvPolynomial (Option σ) E) (e : Exponent σ)
    (he : InBox H e) : (boxDenominator g e).totalDegree ≤ H + ∑ i, (g i).totalDegree := by
  apply (totalDegree_mul ..).trans (Nat.add_le_add ?_ (boxJacobian_degree g))
  rw [totalDegree_X_pow]
  exact Int.toNat_le.mpr (neg_le.mp he.1.1)

/-- The cleared quotient has exactly the box monomial divided by the Jacobian as its value. -/
theorem eval_boxRatio {L : Type*} [Field L] (φ : E →+* L) (t : L) (x : σ → L)
    (g : σ → MvPolynomial (Option σ) E) (e : Exponent σ) :
    let v := eval₂Hom φ (fun o => o.elim t x)
    v (boxNumerator e) / v (boxDenominator g e) =
      t ^ (e none) * (∏ i, x i ^ (e (some i)).toNat) / (chartJacobian φ (fun o => o.elim t x) g).det := by
  dsimp only
  simp only [boxNumerator, boxDenominator, map_mul, map_pow, map_prod, eval₂Hom_X',
    Option.elim_none, Option.elim_some, eval_boxJacobian]
  cases e none with
  | ofNat j => simp
  | negSucc j => simp [div_eq_mul_inv]; ac_rfl

end Branch

end BorderVNP
end Computability
end OAI
