import OAI.LinearAlgebra.SpectralBooks.Rank

/-! The exact threshold of the radical test for weights `(1,1,t)` (Section 6). -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

private theorem elongated_test_iff (t L : ℝ) :
    RadicalTest (loads 1 1 t) L ↔
      2 ≤ L ∧ 1 + t ≤ L ∧ L ≤ Real.sqrt (L ^ 2 - 2 ^ 2) +
        2 * Real.sqrt (L ^ 2 - (1 + t) ^ 2) := by
  norm_num [RadicalTest, loads, Fin.forall_fin_succ, Fin.sum_univ_succ, add_comm t 1]
  constructor
  · rintro ⟨⟨hs, h₂, _⟩, h⟩
    exact ⟨h₂, hs, by linarith⟩
  · rintro ⟨h₂, hs, h⟩
    exact ⟨⟨hs, h₂, hs⟩, by linarith⟩

/-- The radical test at exponent two cuts off at exactly `√3 - 1`. -/
theorem radicalTest_loads_two_iff {t : ℝ} (ht : 0 ≤ t) :
    RadicalTest (loads 1 1 t) 2 ↔ t ≤ Real.sqrt 3 - 1 := by
  rw [elongated_test_iff]
  have hs := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  have hsNonneg := Real.sqrt_nonneg 3
  norm_num
  constructor
  · rintro ⟨hle, h⟩
    have hrad := Real.sq_sqrt (show 0 ≤ 4 - (1 + t) ^ 2 by nlinarith)
    nlinarith [Real.sqrt_nonneg (4 - (1 + t) ^ 2)]
  · intro h
    have hslt : Real.sqrt 3 ≤ 2 := by nlinarith
    have hsq : (1 + t) ^ 2 ≤ 3 := by
      nlinarith [sq_le_sq' (show -Real.sqrt 3 ≤ 1 + t by linarith)
        (show 1 + t ≤ Real.sqrt 3 by linarith)]
    have hrad := Real.sq_sqrt (show 0 ≤ 4 - (1 + t) ^ 2 by linarith)
    exact ⟨by linarith, by nlinarith [Real.sqrt_nonneg (4 - (1 + t) ^ 2)]⟩

private theorem normalized_summand_strict {m L K : ℝ}
    (hm : 0 < m) (hmL : m ≤ L) (hLK : L < K) :
    Real.sqrt (L ^ 2 - m ^ 2) / L < Real.sqrt (K ^ 2 - m ^ 2) / K := by
  have hL := hm.trans_le hmL
  have hK := hL.trans hLK
  have normalize (x : ℝ) (hx : 0 < x) :
      Real.sqrt (x ^ 2 - m ^ 2) / x = Real.sqrt (1 - (m / x) ^ 2) := by
    rw [show 1 - (m / x) ^ 2 = (x ^ 2 - m ^ 2) / x ^ 2 by field_simp]
    rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hx.le]
  rw [normalize L hL, normalize K hK]
  have hratio : m / K < m / L := div_lt_div_of_pos_left hm hL hLK
  have hmax : m / L ≤ 1 := (div_le_one hL).2 hmL
  have hnonneg : 0 ≤ m / K := by positivity
  apply Real.sqrt_lt_sqrt
  · nlinarith [sq_le_sq' (show -(1 : ℝ) ≤ m / L by linarith) hmax]
  · nlinarith [sq_lt_sq' (show -(m / L) < m / K by linarith) hratio]

/-- At and above `√3 - 1`, the closed-form expression in (6.2) is the least
real number admitted by the radical test. -/
theorem isLeast_radicalTest_elongated {t : ℝ} (ht : Real.sqrt 3 - 1 ≤ t) :
    IsLeast {L : ℝ | RadicalTest (loads 1 1 t) L}
      (t * (t + 2) / Real.sqrt (t ^ 2 + 2 * t - 1)) := by
  let s := 1 + t
  let u := Real.sqrt (s ^ 2 - 2)
  have hsq3 := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  have hroot : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs : Real.sqrt 3 ≤ s := by dsimp [s]; linarith
  have hs₀ : 0 < s := (Real.sqrt_pos.2 (by norm_num : 0 < (3 : ℝ))).trans_le hs
  have hs3 : 3 ≤ s ^ 2 := by nlinarith [sq_le_sq' (show -s ≤ Real.sqrt 3 by linarith) hs]
  have hu₂ : u ^ 2 = s ^ 2 - 2 := Real.sq_sqrt (by linarith)
  have hu : 1 ≤ u := by
    nlinarith only [hu₂, hs3, show 0 ≤ u from Real.sqrt_nonneg _]
  have hu₀ : 0 < u := by linarith
  have huv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu₀.ne'
  have hv₀ : 0 < u⁻¹ := inv_pos.mpr hu₀
  have hv : u⁻¹ ≤ u := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) hv₀.le]
  let K := u + u⁻¹
  have hformula : t * (t + 2) / Real.sqrt (t ^ 2 + 2 * t - 1) = K := by
    rw [show t ^ 2 + 2 * t - 1 = s ^ 2 - 2 by dsimp [s]; ring]
    change t * (t + 2) / u = u + u⁻¹
    apply (div_eq_iff hu₀.ne').mpr
    dsimp [s] at hu₂
    nlinarith only [hu₂, huv]
  rw [hformula]
  have hK₀ : 0 < K := add_pos hu₀ hv₀
  have hK₂ : K ^ 2 - 2 ^ 2 = (u - u⁻¹) ^ 2 := by dsimp [K]; nlinarith only [huv]
  have hKs : K ^ 2 - s ^ 2 = (u⁻¹) ^ 2 := by dsimp [K]; nlinarith only [hu₂, huv]
  have hKtwo : 2 ≤ K := le_of_sq_le_sq (by linarith only [hK₂, sq_nonneg (u - u⁻¹)]) hK₀.le
  have hsK : s ≤ K := le_of_sq_le_sq (by linarith only [hKs, sq_nonneg (u⁻¹)]) hK₀.le
  have h₁ : Real.sqrt (K ^ 2 - 2 ^ 2) = u - u⁻¹ := by
    rw [hK₂, Real.sqrt_sq (sub_nonneg.mpr hv)]
  have h₂ : Real.sqrt (K ^ 2 - s ^ 2) = u⁻¹ := by
    rw [hKs, Real.sqrt_sq hv₀.le]
  have heq : K = Real.sqrt (K ^ 2 - 2 ^ 2) + 2 * Real.sqrt (K ^ 2 - s ^ 2) := by
    rw [h₁, h₂]
    dsimp [K]
    ring
  constructor
  · exact (elongated_test_iff ..).2 ⟨hKtwo, hsK, heq.le⟩
  · intro L hL
    obtain ⟨hLtwo, hsL, hsum⟩ := (elongated_test_iff ..).1 hL
    change L ≤ Real.sqrt (L ^ 2 - 2 ^ 2) + 2 * Real.sqrt (L ^ 2 - s ^ 2) at hsum
    by_contra! hLK
    have hL₀ : 0 < L := by linarith
    have hl := (le_div_iff₀ hL₀).2 (show 1 * L ≤ _ by simpa using hsum)
    have hk := (div_eq_iff hK₀.ne').2 (show _ = 1 * K by simpa using heq.symm)
    rw [add_div, mul_div_assoc] at hl hk
    linarith [normalized_summand_strict (by norm_num : (0 : ℝ) < 2) hLtwo hLK,
      normalized_summand_strict hs₀ hsL hLK]

/-- The complete solution of the radical inequality at elongated weights. -/
theorem radicalTest_elongated_iff {t L : ℝ} (ht : 0 ≤ t) :
    RadicalTest (loads 1 1 t) L ↔
      (if t ≤ Real.sqrt 3 - 1 then 2 else t * (t + 2) / Real.sqrt (t ^ 2 + 2 * t - 1)) ≤ L := by
  have hm : ∀ i, 0 ≤ loads 1 1 t i := by
    intro i
    fin_cases i <;> simp [loads] <;> linarith
  split_ifs with hc
  · exact ⟨fun h => ((elongated_test_iff ..).1 h).1,
      fun h => ((radicalTest_loads_two_iff ht).2 hc).mono hm h⟩
  · have hmin := isLeast_radicalTest_elongated (le_of_lt (lt_of_not_ge hc))
    exact ⟨fun h => hmin.2 h, fun h => hmin.1.mono hm h⟩

/-- With an aspect at least one, the threshold strictly exceeds the largest flattening. -/
theorem flattening_lt_elongated_threshold {t : ℝ} (ht : 1 ≤ t) :
    1 + t < t * (t + 2) / Real.sqrt (t ^ 2 + 2 * t - 1) := by
  have harg : 0 < t ^ 2 + 2 * t - 1 := by nlinarith [sq_nonneg t]
  apply (lt_div_iff₀ (Real.sqrt_pos.2 harg)).2
  have hs := Real.sq_sqrt harg.le
  have hsq : ((1 + t) * Real.sqrt (t ^ 2 + 2 * t - 1)) ^ 2 < (t * (t + 2)) ^ 2 := by
    rw [mul_pow, hs]
    ring_nf
    linarith
  nlinarith [mul_nonneg (show 0 ≤ t by linarith) (show 0 ≤ t + 2 by linarith),
    mul_nonneg (show 0 ≤ 1 + t by linarith) (Real.sqrt_nonneg (t ^ 2 + 2 * t - 1))]

/-- The dual exponent attached to the arithmetic exponent at weights `(1,1,t)`. -/
def dualExponent (ω : ℝ → ℝ) : ℝ :=
  sSup {t : ℝ | t ∈ Set.Icc 0 1 ∧ ω t = 2}

/-- The rectangular radical test implies the upper bound for the dual exponent. -/
theorem dualExponent_le_of_radicalTest {ω : ℝ → ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, RadicalTest (loads 1 1 t) (ω t)) :
    dualExponent ω ≤ Real.sqrt 3 - 1 := by
  unfold dualExponent
  rcases Set.eq_empty_or_nonempty {t : ℝ | t ∈ Set.Icc 0 1 ∧ ω t = 2} with hEmpty | hNonempty
  · rw [hEmpty, Real.sSup_empty]
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ)), Real.sqrt_nonneg 3]
  · apply csSup_le hNonempty
    rintro t ⟨ht, hω⟩
    exact (radicalTest_loads_two_iff ht.1).1 (hω ▸ h t ht)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
