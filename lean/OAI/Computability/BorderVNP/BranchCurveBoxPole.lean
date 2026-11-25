import OAI.Computability.BorderVNP.BranchCurvePoleBound
import OAI.Computability.BorderVNP.ResiduePinsFinite
import OAI.Computability.BorderVNP.ResidueJetJacobian
import Mathlib.Data.Nat.Size

/-! # Pole and bit bounds for the box tests of §10.2

Expand each ratio of a box monomial by the chart Jacobian at the actual DVR.
Its bounded eliminant controls the order even when a coordinate has a pole.
The finite-field basis scalar and the derivative of the regular deformation
parameter then give the same bound for the differential used in the pin.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open Residue ResidueBox ResiduePins Residue.JetRing Module

/-- Expansion of the evaluated chart Jacobian determinant agrees with evaluating
that same determinant in the completion. -/
theorem map_chartJacobian_det {E K L σ : Type*} [Field E] [Field K] [Field L]
    [Fintype σ] [DecidableEq σ] (φ : E →+* K) (ρ : K →+* L) (t : K) (x : σ → K)
    (g : σ → MvPolynomial (Option σ) E) :
    ρ (chartJacobian φ (fun i => i.elim t x) g).det =
      (chartJacobian (ρ.comp φ) (fun i => i.elim (ρ t) (ρ ∘ x)) g).det := by
  rw [ρ.map_det]
  congr 1
  ext i j
  change ρ (MvPolynomial.eval₂Hom φ _ _) = MvPolynomial.eval₂Hom _ _ _
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  funext k
  cases k <;> rfl

set_option maxHeartbeats 1000000 in
/-- The pole bound for every concrete differential `b x^α t^j dt/J`
in the finite residue-pin basis, including negative time powers. -/
theorem box_test_pole_bound {E L σ β : Type*} [Field E] [Finite E] [Field L]
    [Algebra E L] [Algebra (Polynomial E) L] [Algebra (FractionRing (Polynomial E)) L]
    [IsScalarTower (Polynomial E) (FractionRing (Polynomial E)) L] [Fintype σ] [DecidableEq σ]
    (V : ValuationSubring L) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime]
    [CharP V p] [CharP (IsLocalRing.ResidueField V) p] [Finite (IsLocalRing.ResidueField V)]
    [Algebra (ZMod p) E] (s : V) (hs : Irreducible s) (t : Lˣ)
    (ht : (t : L) = algebraMap (Polynomial E) L Polynomial.X) (h0 : (t : L) ∈ V.nonunits)
    (x : σ → L) (R : σ → Polynomial (Polynomial E))
    (hgen : IntermediateField.adjoin (FractionRing (Polynomial E)) (Set.range x) = ⊤)
    (hne : ∀ i, R i ≠ 0) (hroot : ∀ i,
      Polynomial.aeval (x i) ((R i).map (algebraMap (Polynomial E) (FractionRing (Polynomial E)))) = 0)
    (C : ℕ) (hC : ∀ i, (R i).natDegree ≤ C) (g : σ → MvPolynomial (Option σ) E)
    (H D : ℕ) (B : Basis β (ZMod p) E)
    (hQ : ∀ e : {a : Exponent σ // InBox H a}, ∃ Q : Polynomial (Polynomial E), Q ≠ 0 ∧
      (∀ j ∈ Q.support, (Q.coeff j).natDegree ≤ D) ∧
      Q.eval₂ (algebraMap (Polynomial E) L)
        ((t : L) ^ (e.val none) * (∏ i, x i ^ (e.val (some i)).toNat) /
          (chartJacobian (algebraMap E L) (fun i => i.elim (t : L) x) g).det) = 0) :
    let ρ := branchLaurentExpansion p s hs L
    let φ := ρ.comp (algebraMap E L)
    let τ := Units.map ρ.toMonoidHom t
    let J := (chartJacobian φ (fun i => i.elim (τ : LaurentSeries _) (ρ ∘ x)) g).det
    ∀ i : Index β σ H, -((D * C ^ Fintype.card σ : ℕ) : ℤ) ≤
      (evaluate φ (ρ ∘ x) τ (test B i) * (LaurentSeries.derivative (IsLocalRing.ResidueField V) (τ : LaurentSeries _) / J)).order := by
  let ρ := branchLaurentExpansion p s hs L
  let τ := Units.map ρ.toMonoidHom t
  let φ := ρ.comp (algebraMap E L)
  let J := (chartJacobian (algebraMap E L) (fun i => i.elim (t : L) x) g).det
  have fin := (finrank_le_of_bivariate_eliminants x R hgen hne hroot C hC).1
  have ht₀ := ht ▸ h0
  have hτ : 0 < (ρ (t : L)).order := by
    rw [ht]
    exact (completed_order_le_degree V p s hs ht₀).1
  dsimp only
  intro i
  obtain ⟨Q, hneQ, hD, hw⟩ := hQ i.2
  let w := (t : L) ^ (i.2.val none) * (∏ k, x k ^ (i.2.val (some k)).toNat) / J
  have hp := completed_eliminant_pole_bound V p s hs ht₀ x R hgen hne hroot C hC Q hneQ D hD w hw
  have h := order_bound_of_test_differential φ (B i.1) (ρ (t : L)) (ρ w) hτ _ hp
  rw [evaluate_test]
  change _ ≤ (φ (B i.1) * (↑(τ ^ i.2.val none) * ∏ k, ρ (x k) ^ (i.2.val (some k)).toNat) *
    (LaurentSeries.derivative (IsLocalRing.ResidueField V) (ρ (t : L)) / (chartJacobian φ _ g).det)).order
  have hJ : ρ J = (chartJacobian φ (fun j => j.elim (τ : LaurentSeries _) (ρ ∘ x)) g).det :=
    map_chartJacobian_det (algebraMap E L) ρ (t : L) x g
  rw [← hJ]
  have he : ρ w = (↑(τ ^ i.2.val none) * ∏ k, ρ (x k) ^ (i.2.val (some k)).toNat) / ρ J := by
    simp only [w, map_div₀, map_mul, map_zpow₀, map_prod, map_pow, Units.val_zpow_eq_zpow_val]
    rfl
  rw [he] at h
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, J] using h

/-- The first extraction power used by the residue matrices takes at most the
sum of the bit bounds for the field, the parameter degree and all coordinate degrees. -/
theorem pin_power_bit_bound {q k D C h a b c : ℕ} (hk : k ≤ 2 ^ a) (hD : D ≤ 2 ^ b)
    (hC : C ≤ 2 ^ c) (hq : q ≤ k * max (D * C ^ h) 1) :
    Nat.clog 2 q ≤ a + b + c * h := by
  apply Nat.clog_le_of_le_pow
  rw [Nat.add_assoc, pow_add, pow_add, pow_mul]
  refine hq.trans (Nat.mul_le_mul hk (max_le ?_ ?_))
  · exact Nat.mul_le_mul hD (Nat.pow_le_pow_left hC _)
  · exact Nat.one_le_iff_ne_zero.mpr (by positivity)

end Branch

end BorderVNP
end Computability
end OAI
