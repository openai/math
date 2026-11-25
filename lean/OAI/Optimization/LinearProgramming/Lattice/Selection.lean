import OAI.Optimization.LinearProgramming.Lattice.DirectionLoop
import OAI.Optimization.LinearProgramming.Lattice.Precision
import OAI.Optimization.LinearProgramming.Lattice.DirichletRational

/-! Interface between the rational approximation procedure and the sign-oracle digit loop. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open SignType WithLp

variable {p M : ℕ}

/-- A normalized residual probe returns no vector at an exactly vanishing residual. -/
def selectedDirection (probe : List (Fin p → ℤ) → Option (Fin p → ℚ))
    (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ)) (old : List (Fin p → ℤ)) :
    Option (Fin p → ℤ) := (probe old).map fun u => (select u).2

/-- Combine the integer digit choices made in at most `p` residual probes. -/
def roundWithSelection (M : ℕ) (probe : List (Fin p → ℤ) → Option (Fin p → ℚ))
    (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ)) : Fin p → ℤ :=
  radixVector ((2 : ℤ) ^ radixWidth p M) (directionLoop (selectedDirection probe select) p [])

private theorem dyadic_lift_bound (hp : 0 < p) (hM : 0 < M) {q : ℕ}
    (hq : q ≤ searchDenominator p M ^ (p + 1)) :
    (q : ℝ) * (1 / (2 : ℝ) ^ searchPrecision p M) ≤ (1 / (4 * (p : ℝ) * M)) / 2 := by
  let Q := searchDenominator p M
  have hQ : 0 < (Q : ℝ) := by exact_mod_cast searchDenominator_pos p M
  have hpow : (2 : ℝ) ^ searchPrecision p M = (Q : ℝ) ^ (p + 2) := by
    exact_mod_cast two_pow_searchPrecision p M
  have hq' : (q : ℝ) ≤ (Q : ℝ) ^ (p + 1) := by exact_mod_cast hq
  have hbig : 8 * (p : ℝ) * M ≤ Q := by exact_mod_cast searchDenominator_ge p M
  have hpos : 0 < 8 * (p : ℝ) * M := by positivity
  calc
    _ ≤ (Q : ℝ) ^ (p + 1) / (Q : ℝ) ^ (p + 2) := by
      rw [mul_one_div, hpow]
      exact div_le_div_of_nonneg_right hq' (by positivity)
    _ = 1 / Q := by rw [show p + 2 = (p + 1) + 1 by omega, pow_succ]; field_simp; simp [pow_succ]; ring
    _ ≤ 1 / (8 * (p : ℝ) * M) := one_div_le_one_div_of_le hpos hbig
    _ = _ := by ring

/-- A returned digit grows the integer span, has bounded coordinates, and determines
the sign of every bounded form that it detects for the first time. -/
theorem selectedDirection_correct (hp : 0 < p) (hM : 0 < M) (v : Fin p → ℝ)
    (probe : List (Fin p → ℤ) → Option (Fin p → ℚ))
    (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ))
    (hzero : ∀ old, probe old = none ↔ toLp 2 v ∈ integerDirectionSpan old)
    (hprobe : ∀ old u, probe old = some u → ∀ i,
      |roundingDirection (integerDirectionSpan old) v i - (u i : ℝ)| ≤
        1 / (2 : ℝ) ^ searchPrecision p M)
    (hsel : ∀ u, 0 < (select u).1 ∧ (select u).1 ≤ searchDenominator p M ^ (p + 1) ∧
      ∀ i, |((select u).1 : ℚ) * u i - (select u).2 i| ≤ 1 / (8 * (p : ℚ) * M))
    (old : List (Fin p → ℤ)) (z : Fin p → ℤ) (h : selectedDirection probe select old = some z) :
    (∀ i, |z i| ≤ ((searchDenominator p M ^ (p + 1) + 1 : ℕ) : ℤ)) ∧
    toLp 2 (realCoordinates z) ∉ integerDirectionSpan old ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
      (∀ y ∈ integerDirectionSpan old, realCoordinates a ⬝ᵥ y.ofLp = 0) →
      a ⬝ᵥ z ≠ 0 → sign (a ⬝ᵥ z) = sign (realCoordinates a ⬝ᵥ v) := by
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
  have hv : toLp 2 v ∉ integerDirectionSpan old := fun hv => by
    have hn := (hzero old).mpr hv
    simp [hu] at hn
  obtain ⟨hq, hqle, hz⟩ := hsel u
  let q := (select u).1
  let z := (select u).2
  let ε := 1 / (4 * (p : ℝ) * M)
  have he : ∀ i, |(q : ℝ) * roundingDirection (integerDirectionSpan old) v i - z i| ≤ ε := by
    apply simultaneous_approximation_stable _ (fun i => (u i : ℝ)) z q
      (1 / (2 : ℝ) ^ searchPrecision p M) ε (hprobe old u hu) (dyadic_lift_bound hp hM hqle)
    intro i
    have ht : |(q : ℝ) * (u i : ℝ) - z i| ≤ 1 / (8 * (p : ℝ) * M) := by
      simpa [q, z] using (Rat.cast_le (K := ℝ)).mpr (hz i)
    exact ht.trans_eq (by dsimp [ε]; ring)
  refine ⟨?_, roundingProjectionStep (integerDirectionSpan old) v hv hp hM q hq z he⟩
  intro i
  have hε : ε ≤ 1 := by
    change 1 / (4 * (p : ℝ) * M) ≤ 1
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    rw [div_le_iff₀ (by positivity), one_mul]
    nlinarith [mul_le_mul hp' hM' (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
  have habs : |(z i : ℝ)| ≤ (q : ℝ) + 1 := by
    let x := (q : ℝ) * roundingDirection (integerDirectionSpan old) v i
    calc
      |(z i : ℝ)| = |x - (x - z i)| := by ring_nf
      _ ≤ |x| + |x - z i| := abs_sub ..
      _ ≤ (q : ℝ) + 1 := by
        dsimp [x]
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
        exact add_le_add (mul_le_of_le_one_right (by positivity) (abs_roundingDirection_le_one _ _ _))
          ((he i).trans hε)
  have hzq : |z i| ≤ (q : ℤ) + 1 := by exact_mod_cast habs
  exact hzq.trans (by exact_mod_cast Nat.add_le_add_right hqle 1)

/-- If the rational selector supplies the short approximation of Appendix A, applying it
to the oracle's dyadic answers preserves all signs. The bound counts actual output bits. -/
theorem roundWithSelection_correct (hp : 0 < p) (hM : 0 < M) (v : Fin p → ℝ)
    (probe : List (Fin p → ℤ) → Option (Fin p → ℚ))
    (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ))
    (hzero : ∀ old, probe old = none ↔ toLp 2 v ∈ integerDirectionSpan old)
    (hprobe : ∀ old u, probe old = some u → ∀ i,
      |roundingDirection (integerDirectionSpan old) v i - (u i : ℝ)| ≤
        1 / (2 : ℝ) ^ searchPrecision p M)
    (hsel : ∀ u, 0 < (select u).1 ∧ (select u).1 ≤ searchDenominator p M ^ (p + 1) ∧
      ∀ i, |((select u).1 : ℚ) * u i - (select u).2 i| ≤ 1 / (8 * (p : ℚ) * M)) :
    (∀ i, ((roundWithSelection M probe select i).natAbs).size ≤ radixWidth p M * p) ∧
    ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
      sign (dotProduct a (roundWithSelection M probe select)) = sign (dotProduct (realCoordinates a) v) := by
  let next := selectedDirection probe select
  let D := searchDenominator p M ^ (p + 1) + 1
  let B : ℤ := 2 ^ radixWidth p M
  have hstop old (h : next old = none) : toLp 2 v ∈ integerDirectionSpan old :=
    (hzero old).mp (Option.map_eq_none_iff.mp h)
  have hstep := selectedDirection_correct hp hM v probe select hzero hprobe hsel
  obtain ⟨hlen, hz, hsign⟩ := directionLoop_correct next v M D hstop hstep
  have hD : (D : ℤ) < B := by
    dsimp [B, D]
    exact_mod_cast (digit_bounds p M).1
  have hMD : (M : ℤ) * D < B := by
    dsimp [B, D]
    exact_mod_cast (digit_bounds p M).2
  have hB : 1 ≤ B := by
    dsimp [B]
    have := pow_pos (by decide : (0 : ℤ) < 2) (radixWidth p M)
    omega
  constructor
  · intro i
    apply Nat.size_le.mpr
    have h := abs_radixVector_lt (B := B) (by omega) (directionLoop next p [])
      (fun z hm j => (hz z hm j).trans_lt hD) i
    have h' : |roundWithSelection M probe select i| < (2 : ℤ) ^ (radixWidth p M * p) := by
      rw [pow_mul]
      exact h.trans_le (pow_le_pow_right₀ hB hlen)
    have hc : ((roundWithSelection M probe select i).natAbs : ℤ) < ((2 ^ (radixWidth p M * p) : ℕ) : ℤ) := by
      simpa only [Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat] using h'
    exact_mod_cast hc
  · intro a ha
    rw [roundWithSelection, sign_dotProduct_radixVector (by omega) (by positivity : (0 : ℤ) ≤ D)
      hMD _ hz a ha]
    exact hsign a ha

/-- The explicit bounded search is one deterministic rational selector satisfying the
comparison interface. Its internal exhaustive search does not enter the oracle count. -/
theorem search_selector_correct (hp : 0 < p) (hM : 0 < M) (u : Fin p → ℚ) :
    let r := rationalDirichlet (searchDenominator p M) u
    0 < r.1 ∧ r.1 ≤ searchDenominator p M ^ (p + 1) ∧
      ∀ i, |(r.1 : ℚ) * u i - r.2 i| ≤ 1 / (8 * (p : ℚ) * M) := by
  obtain ⟨hq, hqle, hz⟩ := rationalDirichlet_correct (searchDenominator_pos p M) u
  refine ⟨hq, hqle.trans (Nat.pow_le_pow_right (searchDenominator_pos p M) (by omega)), fun i => ?_⟩
  exact (hz i).trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast searchDenominator_ge p M))

end Lattice
end LinearProgramming
end Optimization
end OAI
