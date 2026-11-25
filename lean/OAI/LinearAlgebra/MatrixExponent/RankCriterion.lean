import OAI.LinearAlgebra.MatrixExponent.Bilinearize
import OAI.LinearAlgebra.MatrixExponent.Flattening
import OAI.LinearAlgebra.MatrixExponent.Growth
import OAI.LinearAlgebra.MatrixExponent.Specialization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Strict savings and finite specialization

The factor two in bilinearization is absorbed before changing fields.
Only one finite decomposition needs to be specialized.
-/

namespace OAI.LinearAlgebra.MatrixExponent
open Filter

variable {F : Type*} [Field F] {a b : ℝ} {n r : ℕ}

private theorem small_rank (h : Admissible F a) (hab : a < b) :
    ∃ n r : ℕ, 2 ≤ n ∧ RankLE (Rat F n) n r ∧ (r : ℝ) < (n : ℝ) ^ b := by
  let ε := (b - a) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, _, hC⟩ := h ε hε
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hp⟩ := ((eventually_ge_atTop 2).and (ht.eventually_gt_atTop (2 * C))).exists
  obtain ⟨m, hm, hcost⟩ := hC n (by omega)
  refine ⟨n, 2 * m, hn, bilinearize hm, ?_⟩
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    ((2 * m : ℕ) : ℝ) ≤ (2 * C) * (n : ℝ) ^ (a + ε) := by push_cast; linarith
    _ < (n : ℝ) ^ ε * (n : ℝ) ^ (a + ε) :=
      mul_lt_mul_of_pos_right hp (Real.rpow_pos_of_pos hn0 _)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hn0, show ε + (a + ε) = b by dsimp [ε]; ring]

private theorem rank_area (hr : RankLE F n r) : (n : ℝ) ^ (2 : ℝ) ≤ (r : ℝ) := by
  rw [Real.rpow_two]
  exact_mod_cast rank_lower hr

theorem two_le_admissible (h : Admissible F a) : 2 ≤ a := by
  by_contra! hlt
  obtain ⟨n, r, _, hr, hp⟩ := small_rank h hlt
  exact (rank_area hr).not_gt hp

theorem two_le_omega (F : Type*) [Field F] : 2 ≤ omega F :=
  le_csInf ⟨3, admissible_three F⟩ (fun _ h => two_le_admissible h)

theorem omega_le_of_admissible (h : Admissible F a) : omega F ≤ a :=
  csInf_le ⟨2, fun _ h' => two_le_admissible h'⟩ h

theorem omega_le_of_rank {s : ℝ} (hn : 2 ≤ n) (hr : RankLE F n r)
    (hrs : (r : ℝ) ≤ (n : ℝ) ^ s) : omega F ≤ s := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast hn
  exact omega_le_of_admissible (admissible_of_rank hn hr
    ((Real.rpow_le_rpow_left_iff hn1).mp ((rank_area hr).trans hrs)) hrs)

theorem omega_lt_of_rank (hn : 2 ≤ n) (hr : RankLE F n r)
    (hrs : (r : ℝ) < (n : ℝ) ^ b) : omega F < b := by
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast hn
  have hr0 : 0 < (r : ℝ) := (Real.rpow_pos_of_pos (by linarith) _).trans_le (rank_area hr)
  let s := Real.log (r : ℝ) / Real.log (n : ℝ)
  have hs : (n : ℝ) ^ s = r := by
    rw [Real.rpow_def_of_pos (by linarith), show Real.log (n : ℝ) * s = Real.log (r : ℝ) by
      dsimp [s]; exact mul_div_cancel₀ _ (Real.log_pos hn1).ne', Real.exp_log hr0]
  exact (omega_le_of_rank hn hr hs.ge).trans_lt ((Real.rpow_lt_rpow_left_iff hn1).mp
    (hs.trans_lt hrs))

theorem rank_of_omega_lt (h : omega F < b) :
    ∃ n r : ℕ, 2 ≤ n ∧ RankLE (Rat F n) n r ∧ (r : ℝ) < (n : ℝ) ^ b := by
  obtain ⟨a, ha, hab⟩ := exists_lt_of_csInf_lt ⟨3, admissible_three F⟩ h
  exact small_rank ha hab

/-- The finite specialization lemma of Section 2, with an arbitrary strict threshold. -/
theorem finite_specialization (h : omega F < b) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), omega k < b := by
  obtain ⟨n, r, hn, hr, hrs⟩ := rank_of_omega_lt h
  obtain ⟨k, hk, hf, hkr⟩ := specializeRank hr
  exact ⟨k, hk, hf, omega_lt_of_rank hn hkr hrs⟩

end OAI.LinearAlgebra.MatrixExponent
