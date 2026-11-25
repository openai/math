import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-! Infimum lemmas for the exact rank exponent. The concrete definition in
`RankExponent` uses the actual rank of square complex matrix tensors. -/

namespace OAI.LinearAlgebra.TensorSpectrum

def rankExponentSet (R : ℕ → ℕ) : Set ℝ :=
  {q | ∃ d : ℕ, 2 ≤ d ∧ q = Real.log (R d : ℝ) / Real.log (d : ℝ)}

noncomputable def rankExponent (R : ℕ → ℕ) : ℝ := sInf (rankExponentSet R)

theorem rankExponentSet_nonempty (R : ℕ → ℕ) : (rankExponentSet R).Nonempty :=
  ⟨_, 2, le_rfl, rfl⟩

theorem two_le_logRank {R : ℕ → ℕ} (hR : ∀ d, d ^ 2 ≤ R d)
    {d : ℕ} (hd : 2 ≤ d) :
    (2 : ℝ) ≤ Real.log (R d : ℝ) / Real.log (d : ℝ) := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hd0 : (0 : ℝ) < d := lt_trans zero_lt_one hd1
  have hbound : (d : ℝ) ^ 2 ≤ R d := by exact_mod_cast hR d
  have hlog := Real.log_le_log (pow_pos hd0 2) hbound
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos hd1)).mpr (by simpa using hlog)

theorem rankExponentSet_bddBelow {R : ℕ → ℕ} (hR : ∀ d, d ^ 2 ≤ R d) :
    BddBelow (rankExponentSet R) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  exact two_le_logRank hR hd

theorem two_le_rankExponent {R : ℕ → ℕ} (hR : ∀ d, d ^ 2 ≤ R d) :
    2 ≤ rankExponent R := by
  apply le_csInf (rankExponentSet_nonempty R)
  rintro _ ⟨d, hd, rfl⟩
  exact two_le_logRank hR hd

theorem rankExponent_le_logRank {R : ℕ → ℕ} (hR : ∀ d, d ^ 2 ≤ R d)
    {d : ℕ} (hd : 2 ≤ d) :
    rankExponent R ≤ Real.log (R d : ℝ) / Real.log (d : ℝ) :=
  csInf_le (rankExponentSet_bddBelow hR) ⟨d, hd, rfl⟩

theorem rankExponent_le_three {R : ℕ → ℕ} (hR : ∀ d, d ^ 2 ≤ R d)
    (hupper : ∀ d, R d ≤ d ^ 3) : rankExponent R ≤ 3 := by
  have hlow : (0 : ℝ) < R 2 := by
    have h := hR 2
    exact_mod_cast (show 0 < R 2 by omega)
  have hbound : (R 2 : ℝ) ≤ (2 : ℝ) ^ 3 := by exact_mod_cast hupper 2
  have hlog := Real.log_le_log hlow hbound
  rw [Real.log_pow] at hlog
  have hquot : Real.log (R 2 : ℝ) / Real.log 2 ≤ (3 : ℝ) :=
    (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
      (by simpa using hlog)
  exact (rankExponent_le_logRank hR (d := 2) le_rfl).trans hquot

/-- The infimum gives a lower bound for every individual exact rank. -/
theorem rpow_rankExponent_le_rank {R : ℕ → ℕ} (hR : ∀ d, d ^ 2 ≤ R d)
    {d : ℕ} (hd : 2 ≤ d) :
    (d : ℝ) ^ rankExponent R ≤ R d := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hd0 : (0 : ℝ) < d := lt_trans zero_lt_one hd1
  have hbound : (d : ℝ) ^ 2 ≤ R d := by exact_mod_cast hR d
  have hRpos : (0 : ℝ) < R d := (pow_pos hd0 2).trans_le hbound
  apply (Real.rpow_le_iff_le_log hd0 hRpos).mpr
  exact (le_div_iff₀ (Real.log_pos hd1)).mp (rankExponent_le_logRank hR hd)

/-- Positive slack supplies a finite block; the infimum need not be attained. -/
theorem exists_rank_lt_rpow {R : ℕ → ℕ} (_hR : ∀ d, d ^ 2 ≤ R d)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℕ, 2 ≤ u ∧ (R u : ℝ) < (u : ℝ) ^ (rankExponent R + δ) := by
  obtain ⟨q, hq, hlt⟩ := exists_lt_of_csInf_lt (rankExponentSet_nonempty R)
    (show sInf (rankExponentSet R) < rankExponent R + δ by
      change rankExponent R < rankExponent R + δ
      linarith)
  obtain ⟨u, hu, rfl⟩ := hq
  have hu1 : (1 : ℝ) < u := by exact_mod_cast (show 1 < u by omega)
  have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
  refine ⟨u, hu, Real.lt_rpow_of_log_lt hu0 ?_⟩
  exact (div_lt_iff₀ (Real.log_pos hu1)).mp hlt

end OAI.LinearAlgebra.TensorSpectrum
