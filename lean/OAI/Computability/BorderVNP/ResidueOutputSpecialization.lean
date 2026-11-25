import OAI.Computability.BorderVNP.ResidueLaurent
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Specializing entire contractions at the branch

Equation (11.1) substitutes one regular output for each coefficient query.
Any polynomial in those outputs has nonnegative order and its constant
coefficient is the value of that same polynomial on the boundary. The
parameter coordinates used to produce the outputs may have arbitrary poles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open HahnSeries MvPolynomial
open scoped PowerSeries

variable {κ k σ ι : Type*} [Field κ] [CommRing k]

/-- A regular Laurent series is the image of the power series formed from its
nonnegative coefficients. -/
theorem of_nonnegative_coeffs {D : LaurentSeries κ} (h : 0 ≤ D.order) :
    ofPowerSeries ℤ κ (PowerSeries.mk fun i => D.coeff i) = D := by
  ext i
  change ((PowerSeries.mk fun n : ℕ => D.coeff n : PowerSeries κ) : LaurentSeries κ).coeff i = _
  rw [PowerSeries.coeff_coe]
  by_cases hi : i < 0
  · rw [ite_eq_left hi, coeff_eq_zero_of_lt_order (hi.trans_le h)]
  · rw [ite_eq_right hi, PowerSeries.coeff_mk]
    congr 1
    omega

/-- Laurent series coming from power series have nonnegative order, including zero. -/
theorem ofPowerSeries_nonnegative (f : PowerSeries κ) : 0 ≤ (ofPowerSeries ℤ κ f).order := by
  by_cases hf : ofPowerSeries ℤ κ f = 0
  · simp [hf]
  · apply (le_order_iff_forall hf).mpr
    intro i hi
    exact (PowerSeries.coeff_coe f i).trans (ite_eq_left hi)

/-- Simultaneous specialization for any formal polynomial in the regular table
outputs, including every pin-indexed contraction in Section 11. -/
theorem output_specializes (ψ : k →+* κ) (Y : ι → LaurentSeries κ) (c : ι → k)
    (hy : ∀ i, 0 ≤ (Y i).order) (hc : ∀ i, (Y i).coeff 0 = ψ (c i))
    (P : MvPolynomial ι k) :
    let A := eval₂Hom (HahnSeries.C.comp ψ) Y P
    0 ≤ A.order ∧ A.coeff 0 = ψ (eval c P) := by
  let v (i : ι) : PowerSeries κ := PowerSeries.mk fun n => (Y i).coeff n
  let F := eval₂Hom (PowerSeries.C.comp ψ) v P
  have hF : ofPowerSeries ℤ κ F = eval₂Hom (HahnSeries.C.comp ψ) Y P := by
    dsimp only [F]
    rw [map_eval₂Hom]
    congr 2
    · exact RingHom.ext fun a => ofPowerSeries_C (Γ := ℤ) (ψ a)
    · exact funext fun i => of_nonnegative_coeffs (hy i)
  rw [← hF]
  refine ⟨ofPowerSeries_nonnegative F, ?_⟩
  rw [show ((ofPowerSeries ℤ κ) F).coeff 0 = PowerSeries.constantCoeff F from
    (ofPowerSeries_apply_coeff F 0).trans (PowerSeries.coeff_zero_eq_constantCoeff_apply F)]
  dsimp only [F]
  rw [map_eval₂Hom]
  have hmap : (PowerSeries.constantCoeff : PowerSeries κ →+* κ).comp (PowerSeries.C.comp ψ) = ψ := by
    ext a
    simp
  have hval : (fun i => PowerSeries.constantCoeff (v i)) = ψ ∘ c := by
    funext i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact hc i
  rw [hmap, hval]
  exact (map_eval₂Hom (RingHom.id k) c ψ P).symm

/-- Specialization after formal substitution over an extension of the prime field.
This form takes the parameter polynomial whose degree enters the pin bound. -/
theorem substituted_output_specializes {E : Type*} [CommRing E] (p : ℕ)
    (ψ : ZMod p →+* κ) (φ : E →+* LaurentSeries κ) (base : ZMod p →+* E)
    (x : σ → LaurentSeries κ) (Y : ι → MvPolynomial σ E) (c : ι → ZMod p)
    (hy : ∀ i, 0 ≤ (eval₂Hom φ x (Y i)).order)
    (hc : ∀ i, (eval₂Hom φ x (Y i)).coeff 0 = ψ (c i)) (P : MvPolynomial ι (ZMod p)) :
    let A := eval₂Hom (MvPolynomial.C.comp base) Y P
    0 ≤ (eval₂Hom φ x A).order ∧ (eval₂Hom φ x A).coeff 0 = ψ (eval c P) := by
  have hb : (eval₂Hom φ x).comp (MvPolynomial.C.comp base) = HahnSeries.C.comp ψ :=
    RingHom.ext_zmod _ _
  have h := map_eval₂Hom (MvPolynomial.C.comp base) Y (eval₂Hom φ x) P
  rw [hb] at h
  dsimp only
  rw [h]
  exact output_specializes ψ _ c hy hc P

end Residue

end BorderVNP
end Computability
end OAI
