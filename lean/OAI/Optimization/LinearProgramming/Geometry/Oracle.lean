import OAI.Optimization.LinearProgramming.Geometry.Basic
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfe
import OAI.Optimization.LinearProgramming.Geometry.Clipping

/-! The geometric label test given the rational projector of Section 2. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Finset Matrix SignType
open scoped BigOperators Matrix

variable {n : ℕ}

/-- Canonical priced and normalized member of the family of compressed circuits. -/
noncomputable def priceNormalize (t c : Fin n → ℝ) (i : Fin n) : ℝ :=
  pricedVector t c i / ‖pricedVector t c‖

theorem priceNormalize_in_labelBox {C : Finset (Fin n → ℝ)}
    (hC : ∀ c ∈ C, ∀ j, 0 ≤ c j) (t : Fin n → ℝ) (i : Fin n)
    (hi : 0 < circuitEnvelope C i)
    (hnear : ∀ j, 0 < circuitEnvelope C j →
      circuitCost C i + t i ≤ circuitCost C j + t j + 2) :
    ∃ c ∈ C, InLabelBox i (priceNormalize t c) := by
  obtain ⟨c, hc, k, hk, hb, hi'⟩ := exists_priced_circuit_witness hC t i hi hnear
  have hn j : 0 ≤ pricedVector t c j :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hC c hc j)
  have hnorm : ‖pricedVector t c‖ = pricedVector t c k := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg hk.le).mpr
      intro j
      rw [Real.norm_eq_abs, abs_of_nonneg (hn j)]
      exact (div_le_one hk).mp (hb j).2
    · simpa [Real.norm_eq_abs, abs_of_nonneg (hn k)] using norm_le_pi_norm (pricedVector t c) k
  refine ⟨c, hc, ?_⟩
  intro j
  simp only [priceNormalize, hnorm]
  constructor
  · by_cases hj : j = i
    · simpa [fwLower, hj] using hi'
    · simpa [fwLower, hj] using (hb j).1
  · exact (hb j).2

/-- Reusing the same row after zero-price normalization gives precisely the
normalized minor row at the queried prices; the common original scale cancels. -/
theorem priceNormalize_normalizedMinorRow (v f t : Fin n → ℝ) :
    priceNormalize t (normalizedMinorRow v f 0) = normalizedMinorRow v f t := by
  let v₀ := pricedMinorRow v f 0
  let vt := pricedMinorRow v f t
  by_cases hz : ‖v₀‖ = 0
  · have h₀ : v₀ = 0 := norm_eq_zero.mp hz
    have hvt : vt = 0 := by
      ext j
      have h := congrFun h₀ j
      change ((sign (v j) : SignType) : ℝ) * (2 : ℝ) ^ (f j - 0) = 0 at h
      rw [mul_eq_zero] at h
      rcases h with h | h
      · simp [vt, pricedMinorRow, h]
      · exact ((Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne' h).elim
    have hbase : normalizedMinorRow v f 0 = 0 := by
      ext j
      change ‖v₀‖⁻¹ * v₀ j = 0
      rw [hz, _root_.inv_zero, zero_mul]
    rw [hbase]
    ext j
    change _ = ‖vt‖⁻¹ * vt j
    rw [hvt]
    simp [priceNormalize, pricedVector]
  · have hp : 0 < ‖v₀‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hscaled : pricedVector t (normalizedMinorRow v f 0) = ‖v₀‖⁻¹ • vt := by
      ext j
      change (2 : ℝ) ^ (-t j) * (‖v₀‖⁻¹ * pricedMinorRow v f 0 j) =
        ‖v₀‖⁻¹ * pricedMinorRow v f t j
      simp only [pricedMinorRow, Pi.zero_apply, sub_zero]
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    ext j
    change pricedVector t (normalizedMinorRow v f 0) j / ‖pricedVector t (normalizedMinorRow v f 0)‖ =
      ‖vt‖⁻¹ * vt j
    rw [hscaled, norm_smul]
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hp.le,
      div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
    field_simp [hz]

/-- This is exactly `8 n / τ²`, with `τ = 1 / (1000 n)`. -/
def labelIterations (n : ℕ) : ℕ := 8000000 * n ^ 3

def labelTolerance {K : Type*} [Field K] (n : ℕ) : K := 1 / (1000 * (n : K))

/-- A computable rational predicate when specialized to `K = ℚ`. -/
def projectorLabel {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : Matrix (Fin n) (Fin n) K) (i : Fin n) : Bool :=
  let Q := 1 - P
  decide (fwEnergy Q (fwIterate Q i (labelIterations n)) ≤ (labelTolerance n : K) ^ 2)

theorem squareLength_eq_dot (x : Fin n → ℝ) : squareLength x = x ⬝ᵥ x := by
  simp only [squareLength, dotProduct, pow_two]

theorem labelBox_to_coordinates {i : Fin n} {z : Fin n → ℝ} (hz : InLabelBox i z) :
    (∀ j, 0 ≤ z j ∧ z j ≤ 1) ∧ 1 / 4 ≤ z i := by
  constructor
  · intro j
    have hl : (0 : ℝ) ≤ fwLower i j := by unfold fwLower; split <;> norm_num
    exact ⟨hl.trans (hz j).1, (hz j).2⟩
  · simpa [fwLower] using (hz i).1

/-- The exact normalized primal/dual residual estimates in (2.4) give both
required outputs of the finite test. Complexities of the preceding minor
requests are independent of this final separation argument. -/
theorem projectorLabel_spec {C D : Finset (Fin n → ℝ)}
    (hC : ∀ c ∈ C, ∀ j, 0 ≤ c j) (hD : ∀ d ∈ D, ∀ j, 0 ≤ d j)
    (t : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hs : P.IsSymm) (he : P * P = P)
    (hp : ∀ c ∈ C, squareLength (priceNormalize t c - P *ᵥ priceNormalize t c) ≤
      (labelTolerance n : ℝ) ^ 2 / 4)
    (hd : ∀ d ∈ D, squareLength (P *ᵥ priceNormalize (-t) d) ≤ (labelTolerance n : ℝ) ^ 2 / 4)
    (i : Fin n) :
    ((0 < circuitEnvelope C i ∧ ∀ j, 0 < circuitEnvelope C j →
       circuitCost C i + t i ≤ circuitCost C j + t j + 2) → projectorLabel P i = true) ∧
    ((0 < circuitEnvelope D i ∧ ∀ j, 0 < circuitEnvelope D j →
       circuitCost D i - t i ≤ circuitCost D j - t j + 2) → projectorLabel P i = false) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast i.pos
  have hτ : 0 < (labelTolerance n : ℝ) := by unfold labelTolerance; positivity
  have hsmall : 2 * (Fintype.card (Fin n) : ℝ) * labelTolerance n < 1 / 16 := by
    simp only [Fintype.card_fin, labelTolerance]
    field_simp
    linarith
  have hiter : 8 * (n : ℝ) ≤ labelIterations n * (labelTolerance n : ℝ) ^ 2 := by
    simp only [labelIterations, labelTolerance, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
    ring_nf
    exact le_rfl
  let Q : Matrix (Fin n) (Fin n) ℝ := 1 - P
  have hqs : Qᵀ = Q := by simp [Q, hs.eq]
  have hqe : Q * Q = Q := by simp [Q, sub_mul, mul_sub, he]
  have henergy (x : Fin n → ℝ) : fwEnergy Q x = squareLength (x - P *ᵥ x) := by
    simp [fwEnergy, Q, sub_mulVec, squareLength_eq_dot]
  constructor
  · rintro ⟨hi, hnear⟩
    obtain ⟨c, hc, hw⟩ := priceNormalize_in_labelBox hC t i hi hnear
    apply decide_eq_true
    exact fwIterate_accept Q hqs hqe i _ hw _ ((henergy _).symm ▸ hp c hc) _ hiter
  · rintro ⟨hi, hnear⟩
    have hnear' : ∀ j, 0 < circuitEnvelope D j →
        circuitCost D i + (-t) i ≤ circuitCost D j + (-t) j + 2 := by
      simpa only [Pi.neg_apply, sub_eq_add_neg] using hnear
    obtain ⟨d, hd', hw⟩ := priceNormalize_in_labelBox hD (-t) i hi hnear'
    obtain ⟨hy, hyi⟩ := labelBox_to_coordinates hw
    obtain ⟨hz, hzi⟩ := labelBox_to_coordinates (fwIterate_mem Q i (labelIterations n))
    have hpy : squareLength (P *ᵥ priceNormalize (-t) d) ≤ (labelTolerance n : ℝ) ^ 2 := by
      nlinarith [hd d hd', sq_nonneg (labelTolerance n : ℝ)]
    apply decide_eq_false
    rw [henergy]
    exact dual_witness_excludes_small_residual P hs i _ hτ.le hsmall hy hz hyi hzi hpy

/-- Exact transport from the materialized rational calculation to the statement over
real circuit costs, including the tolerance and iteration count. -/
theorem fwLabel_one_sub_eq_projectorLabel (P : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    fwLabel (1 - P) i = projectorLabel (P.map (Rat.castHom ℝ)) i := by
  rw [fwLabel_cast_eq]
  have hQ : (1 - P).map (Rat.castHom ℝ) = 1 - P.map (Rat.castHom ℝ) := by
    simp [Matrix.map_sub]
  rw [hQ]
  simp [projectorLabel, fwTolerance, labelTolerance, labelIterations, fwRounds]

/-- The signs returned by the rational program for computed, complementary projections.
The residual hypotheses are exactly the preceding rounded-projector inequalities. -/
theorem rational_projectorLabel_spec {C D : Finset (Fin n → ℝ)}
    (hC : ∀ c ∈ C, ∀ j, 0 ≤ c j) (hD : ∀ d ∈ D, ∀ j, 0 ≤ d j)
    (t : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℚ)
    (hs : (P.map (Rat.castHom ℝ)).IsSymm)
    (he : P.map (Rat.castHom ℝ) * P.map (Rat.castHom ℝ) = P.map (Rat.castHom ℝ))
    (hp : ∀ c ∈ C, squareLength (priceNormalize t c -
       P.map (Rat.castHom ℝ) *ᵥ priceNormalize t c) ≤ (labelTolerance n : ℝ) ^ 2 / 4)
    (hd : ∀ d ∈ D, squareLength (P.map (Rat.castHom ℝ) *ᵥ priceNormalize (-t) d) ≤
      (labelTolerance n : ℝ) ^ 2 / 4)
    (i : Fin n) :
    ((0 < circuitEnvelope C i ∧ ∀ j, 0 < circuitEnvelope C j →
       circuitCost C i + t i ≤ circuitCost C j + t j + 2) → fwLabel (1-P) i = true) ∧
    ((0 < circuitEnvelope D i ∧ ∀ j, 0 < circuitEnvelope D j →
       circuitCost D i - t i ≤ circuitCost D j - t j + 2) → fwLabel (1-P) i = false) := by
  rw [fwLabel_one_sub_eq_projectorLabel]
  exact projectorLabel_spec hC hD t _ hs he hp hd i

end Geometry
end LinearProgramming
end Optimization
end OAI
