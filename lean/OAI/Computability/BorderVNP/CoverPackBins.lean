import OAI.Computability.BorderVNP.CoverConfigurationLaw
import OAI.Computability.BorderVNP.CoverProductSamplesDeck
import OAI.Computability.BorderVNP.CoverHeckeDensity
import OAI.Computability.BorderVNP.CoverHeckeDenominators

/-!
# Actual pack-motion means in the product host

The averaging length can be selected once for a finite catalog of ordered
segment speeds and relative bin tests, before the cover level or any pack
widths are given. Independent uniform deck post-translations divide each
relative bin probability by the exact number of product tiles. Thus the
total error over tile addresses does not grow with the depth.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open MeasureTheory Hecke Epoch Set Finset Filter
open scoped Classical Topology ENNReal BoundedContinuousFunction

/-- The finite Hecke alphabet used in an actual motion word. -/
abbrev Letters := Cosets (intersection (lattice 1) elliptic)

/-- Enumerate the finite branch alphabet of the actual quaternion correspondence. -/
noncomputable instance letterFintype : Fintype Letters := @Fintype.ofFinite _ finite_elliptic_indices.1

private theorem baseHaar_stationary (f : Cosets (lattice 1) →ᵇ ℝ) :
    ∫ x, operator (lattice 1) elliptic f x ∂baseHaar = ∫ x, f x ∂baseHaar := by
  let : Fintype (Cosets (intersection (lattice 1) elliptic⁻¹)) := @Fintype.ofFinite _ finite_elliptic_indices.2
  have hi : Integrable f baseHaar := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact Hecke.integral_average (lattice 1) _ elliptic (exact_position_frame_tile 0).1
    (exact_position_frame_tile 0).2 (positionFrameTile_mass 0) _ f.continuous.measurable hi

variable {I : Type*} [Fintype I]

/-- The probability of one relative bin and one tile under the actual finite motion choices. -/
noncomputable def actualBinMass {d n : ℕ} (speed : I → ℝ) (B : Set (HyperbolicHost I × PiLp 2 (fun _ : I => ℂ)))
    (x : Equiv.Perm I → I → SL) (carry : Equiv.Perm I → ProductSample (lattice 1) elliptic I n → I → Deck d)
    (h : I → Deck d) : ℝ :=
  ∑ s : PackSample (lattice 1) elliptic I d n, (packWeight (lattice 1) elliptic s : ℝ) *
    if shiftedAddress s.2.2 (carry s.1 s.2.1) = h then
      ((segmentChart speed s.1) ⁻¹' B).indicator 1 (productPoint (lattice 1) elliptic n (x s.1) s.2.1)
    else 0

private theorem real_jointLaw (speed : I → ℝ) (B : Set (HyperbolicHost I × PiLp 2 (fun _ : I => ℂ))) :
    ((productPositions I).prod (idealDirectionLaw speed)).real B =
      (Fintype.card (Equiv.Perm I) : ℝ)⁻¹ * ∑ p, (classLaw speed p).real B := by
  have hfin (p : Equiv.Perm I) : IsFiniteMeasure (classLaw speed p) := by
    dsimp [classLaw]; infer_instance
  simp only [Measure.real_def,jointLaw_eq_mixture,Measure.smul_apply,smul_eq_mul,
    Measure.finsetSum_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun p _ => measure_ne_top (classLaw speed p) B)]

/-- Uniform per-address estimate for all source segment types and all levels. An arbitrary
dependence of the carry on the source address, relative frame, and motion words is allowed. -/
theorem pack_address_error {T J : Type*} [Finite T] [Finite J] (speed : T → I → ℝ)
    (B : T → J → Set (HyperbolicHost I × PiLp 2 (fun _ : I => ℂ))) (hB : ∀ t j, MeasurableSet (B t j))
    (hn : ∀ t j, ((productPositions I).prod (idealDirectionLaw (speed t))) (frontier (B t j)) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t j d (x : Equiv.Perm I → I → SL)
      (carry : Equiv.Perm I → ProductSample (lattice 1) elliptic I n → I → Deck d) (h : I → Deck d),
      |actualBinMass (speed t) (B t j) x carry h -
        ((productPositions I).prod (idealDirectionLaw (speed t))).real (B t j) / Fintype.card (I → Deck d)| <
        ε / Fintype.card (I → Deck d) := by
  have hd : Dense (Subgroup.closure ((lattice 1 : Set SL) ∪ {elliptic}) : Set SL) := by
    simpa only [Set.union_singleton] using dense_generated
  have he := product_chart_bin_estimate (lattice 1) elliptic baseHaar baseHaar_stationary hd
    (T := T × Equiv.Perm I) (fun a => segmentChart (speed a.1) a.2) (fun a => classLaw (speed a.1) a.2)
    (fun a => segmentChart_preserving _ _) (fun a => segmentChart_ae_continuous _ _)
    (fun a j => B a.1 j) (fun a j => hB a.1 j) (fun a j => class_frontier_null _ _ (hn a.1 j)) hε
  filter_upwards [he] with n hnear t j d x carry h
  let P (p : Equiv.Perm I) := (productLaw (lattice 1) elliptic n (x p)).toMeasure.real
    (segmentChart (speed t) p ⁻¹' B t j)
  let Q (p : Equiv.Perm I) := (classLaw (speed t) p).real (B t j)
  let k : ℝ := Fintype.card (Equiv.Perm I)
  let v : ℝ := Fintype.card (I → Deck d)
  have hk : 0 < k := by dsimp [k]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hsum : |∑ p, (P p-Q p)| < k*ε := by
    apply (abs_sum_le_sum_abs _ _).trans_lt
    have hall : ∀ p : Equiv.Perm I, |P p-Q p| < ε := fun p => hnear (t,p) j (x p)
    simpa [k, nsmul_eq_mul] using Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun p _ => hall p)
  have hmass : actualBinMass (speed t) (B t j) x carry h = (k*v)⁻¹ * ∑ p, P p :=
    pack_single_address_mean (lattice 1) elliptic x carry h _ (fun p => (hB t j).preimage
      (segmentChart_preserving (speed t) p).measurable)
  rw [hmass,real_jointLaw]
  change |(k*v)⁻¹ * ∑ p, P p - k⁻¹ * (∑ p, Q p) / v| < ε/v
  rw [show (k*v)⁻¹ * ∑ p, P p - k⁻¹ * (∑ p, Q p) / v =
    (∑ p, (P p-Q p))/(k*v) from by rw [Finset.sum_sub_distrib]; field_simp,
    abs_div, abs_of_pos (mul_pos hk hv), div_lt_div_iff₀ (mul_pos hk hv) hv]
  nlinarith only [mul_lt_mul_of_pos_right hsum hv]

/-- Summing the per-address errors over the entire growing cover gives a variation
bound that depends only on the fixed number of crossing directions. -/
theorem pack_bin_variation {T B : Type*} [Finite T] [Fintype B] (D : ℕ) (hD : 0 < D)
    (speed : T → I → ℝ) (code : T → (HyperbolicHost I × PiLp 2 (fun _ : I => ℂ)) → B)
    (hB : ∀ t b, MeasurableSet (code t ⁻¹' {b}))
    (hn : ∀ t b, ((productPositions I).prod (idealDirectionLaw (speed t)))
      (frontier (code t ⁻¹' {b})) = 0) :
    ∀ᶠ n in atTop, ∀ t d (x : Equiv.Perm I → I → SL)
      (carry : Equiv.Perm I → ProductSample (lattice 1) elliptic I n → I → Deck d),
      (∑ a : (I → Deck d) × B, |actualBinMass (speed t) (code t ⁻¹' {a.2}) x carry a.1 -
        ((productPositions I).prod (idealDirectionLaw (speed t))).real (code t ⁻¹' {a.2}) /
          Fintype.card (I → Deck d)|) ≤ 1 / (2*(D:ℝ)) := by
  let b : ℝ := Fintype.card B
  let δ := 1 / ((2*(D:ℝ))*(b+1))
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hp : 0 < (D:ℝ) := by exact_mod_cast hD
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have err := pack_address_error speed (fun t b => code t ⁻¹' {b}) hB hn hδ
  filter_upwards [err] with n he t d x carry
  let v : ℝ := Fintype.card (I → Deck d)
  have hv : 0 < v := by dsimp [v]; positivity
  calc
    _ ≤ ∑ _a : (I → Deck d) × B, δ/v := Finset.sum_le_sum fun a _ => (he t a.2 d x carry a.1).le
    _ = b * δ := by simp [v,b,Fintype.card_prod, nsmul_eq_mul]; field_simp
    _ ≤ _ := by dsimp [δ]; field_simp; linarith

end Cover.Frame

end BorderVNP
end Computability
end OAI
