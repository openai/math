import OAI.Computability.BorderVNP.BranchCurveRamification
import OAI.Computability.BorderVNP.BranchCurveDegreeBound
import OAI.Computability.BorderVNP.ResidueLaurentDerivative

/-!
# The uniform pole bound for residue tests

In §10.2 the function `w` is the ratio of a box monomial by the Jacobian.
A bounded bivariate eliminant for each such ratio and the coordinate
eliminants give the required pole bound in the actual completion of the
arithmetic branch. Multiplication by the finite-field basis coefficient
and by the differential of the deformation parameter preserves the bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open HahnSeries

/-- The derivative of a positive-order Laurent series is regular. -/
theorem derivative_regular {κ : Type*} [Field κ] (τ : LaurentSeries κ) (hτ : 0 < τ.order) :
    0 ≤ (LaurentSeries.derivative κ τ).order := by
  obtain h | h := eq_or_ne (LaurentSeries.derivative κ τ) 0
  · simp [h]
  · apply (le_order_iff_forall h).mpr
    intro i hi
    rw [Residue.laurentDerivative_coeff, coeff_eq_zero_of_lt_order (by omega : i + 1 < τ.order),
      mul_zero]

/-- If the function part of a residue test has order at least `-B`, the full
differential has the same lower bound after multiplying by the basis
coefficient and by `dt/ds`. -/
theorem order_bound_of_test_differential {E κ : Type*} [Field E] [Finite E] [Field κ]
    (φ : E →+* LaurentSeries κ) (b : E) (τ w : LaurentSeries κ) (hτ : 0 < τ.order)
    (B : ℕ) (hw : -(B : ℤ) ≤ w.order) :
    -(B : ℤ) ≤ (φ b * w * LaurentSeries.derivative κ τ).order := by
  by_cases hb : b = 0
  · simp [hb]
  by_cases hz : w = 0
  · simp [hz]
  by_cases hd : LaurentSeries.derivative κ τ = 0
  · simp [hd]
  have hφ := (map_ne_zero_iff _ φ.injective).mpr hb
  rw [order_mul (mul_ne_zero hφ hz) hd, order_mul hφ hz, order_finite_scalar φ b hb, zero_add]
  exact hw.trans (le_add_of_nonneg_right (derivative_regular τ hτ))

/-- A bounded bivariate relation for a test ratio and the coordinate
eliminants give the pole budget `D * C ^ h` on the completed branch. -/
theorem completed_eliminant_pole_bound {E L σ : Type*} [Field E] [Finite E] [Field L]
    [Algebra (Polynomial E) L] [Algebra (FractionRing (Polynomial E)) L]
    [IsScalarTower (Polynomial E) (FractionRing (Polynomial E)) L] [Fintype σ]
    (V : ValuationSubring L) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime]
    [CharP V p] [CharP (IsLocalRing.ResidueField V) p] [Finite (IsLocalRing.ResidueField V)]
    (s : V) (hs : Irreducible s) (ht : algebraMap (Polynomial E) L Polynomial.X ∈ V.nonunits)
    (x : σ → L) (R : σ → Polynomial (Polynomial E))
    (hgen : IntermediateField.adjoin (FractionRing (Polynomial E)) (Set.range x) = ⊤)
    (hne : ∀ i, R i ≠ 0) (hroot : ∀ i,
      Polynomial.aeval (x i) ((R i).map (algebraMap (Polynomial E) (FractionRing (Polynomial E)))) = 0)
    (C : ℕ) (hC : ∀ i, (R i).natDegree ≤ C)
    (Q : Polynomial (Polynomial E)) (hQ : Q ≠ 0) (D : ℕ)
    (hD : ∀ j ∈ Q.support, (Q.coeff j).natDegree ≤ D)
    (w : L) (hw : Q.eval₂ (algebraMap (Polynomial E) L) w = 0) :
    -((D * C ^ Fintype.card σ : ℕ) : ℤ) ≤
      (Residue.branchLaurentExpansion p s hs L w).order := by
  obtain ⟨fin, hdeg⟩ := finrank_le_of_bivariate_eliminants x R hgen hne hroot C hC
  let f := Residue.branchLaurentExpansion p s hs L
  let τ := f (algebraMap (Polynomial E) L Polynomial.X)
  let φ := (f.comp (algebraMap (Polynomial E) L)).comp Polynomial.C
  have ev : f.comp (algebraMap (Polynomial E) L) = Polynomial.eval₂RingHom φ τ :=
    Polynomial.ringHom_ext (fun a => (Polynomial.eval₂_C φ τ).symm) (Polynomial.eval₂_X φ τ).symm
  obtain ⟨hpos, hram⟩ := completed_order_le_degree V p s hs ht
  have hz : Q.eval₂ (Polynomial.eval₂RingHom φ τ) (f w) = 0 := by
    rw [← ev, ← Polynomial.hom_eval₂, hw, map_zero]
  have hp := order_bound_of_eliminant φ τ (f w) hpos Q hQ D hD hz
  apply le_trans _ hp
  have ht' : τ.order ≤ (C ^ Fintype.card σ : ℕ) := hram.trans (by exact_mod_cast hdeg)
  push_cast
  simpa only [neg_mul, Nat.cast_pow] using neg_le_neg (mul_le_mul_of_nonneg_left ht' (Int.natCast_nonneg D))

end Branch

end BorderVNP
end Computability
end OAI
