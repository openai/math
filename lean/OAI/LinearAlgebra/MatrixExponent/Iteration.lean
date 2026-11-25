import OAI.LinearAlgebra.MatrixExponent.ListBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Iterating compression at one list width -/

namespace OAI.LinearAlgebra.MatrixExponent
open Filter

private theorem clog_bounds {w : ℕ} (hw : 2 ≤ w) :
    w ≤ Nat.clog 2 (listBits w) ∧ Nat.clog 2 (listBits w) ≤ w ^ 2 := by
  have h : 2 * w ≤ 2 ^ w := by
    induction w, hw using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  constructor
  · have hh := Nat.clog_mono_right 2
      (show 2 ^ w ≤ listBits w from Nat.le_mul_of_pos_left _ (by omega))
    rwa [Nat.clog_pow 2 w (by decide)] at hh
  · apply le_trans (b := w + w) _ (by nlinarith)
    apply Nat.clog_le_of_le_pow
    rw [listBits, pow_add]
    exact Nat.mul_le_mul_right _ h

private theorem large {b : ℝ} (hb : 0 < b) (C : ℝ) :
    ∀ᶠ w : ℕ in atTop, 2 ≤ w ∧ C ≤ (w : ℝ) ∧ 4 ≤ (w : ℝ) ^ b ∧
      (w : ℝ) ^ (3 : ℝ) ≤ (listBits w : ℝ) ^ (1 / 40 : ℝ) := by
  have ht : Tendsto (fun w : ℕ => (w : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he := isLittleO_rpow_exp_pos_mul_atTop 3 (by positivity : 0 < Real.log 2 / 40)
  filter_upwards [eventually_ge_atTop 2, ht.eventually_ge_atTop C,
    ((tendsto_rpow_atTop hb).comp ht).eventually_ge_atTop 4,
    ht.eventually he.eventuallyLE] with w hw hC hb' he'
  refine ⟨hw, hC, hb', ?_⟩
  calc
    (w : ℝ) ^ (3 : ℝ) ≤ Real.exp (Real.log 2 / 40 * w) := by
      simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ (w : ℝ) ^ (3 : ℝ)),
        Real.norm_of_nonneg (Real.exp_nonneg _)] using he'
    _ = ((2 : ℝ) ^ w) ^ (1 / 40 : ℝ) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact_mod_cast (show 2 ^ w ≤ listBits w from Nat.le_mul_of_pos_left _ (by omega))

/-- The lower bound lets us absorb the additive term into the contraction at
*each* step. This avoids estimating a geometric sum at the last step. -/
private theorem absorb {w h e m γ σ b : ℝ} (hw : 1 ≤ w)
    (hh : w ≤ h) (hh' : h ≤ w ^ 2) (hm : 0 ≤ m) (he : 0 ≤ e)
    (hlarge : 4 ≤ w ^ b) (hb : 0 < b) (hg : 2 * b ≤ γ) (hs : 2 * b ≤ σ / 2)
    (hlower : e * w ^ σ ≤ 3 * m) :
    m * h ^ (-γ) + e * h ^ (σ / 4) ≤ m * w ^ (-b) := by
  have hw' : 0 < w := zero_lt_one.trans_le hw
  have hleft : m * h ^ (-γ) ≤ m * w ^ (-(2 * b)) :=
    mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_nonpos hw' hh (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hw (neg_le_neg hg))) hm
  have hright : e * h ^ (σ / 4) ≤ 3 * m * w ^ (-(2 * b)) := by
    calc
      _ ≤ e * (w ^ 2) ^ (σ / 4) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hw'.le.trans hh) hh' (by linarith)) he
      _ = (e * w ^ σ) * w ^ (-(σ / 2)) := by
        rw [← Real.rpow_natCast_mul hw'.le, mul_assoc, ← Real.rpow_add hw']
        congr 2
        ring
      _ ≤ 3 * m * w ^ (-(σ / 2)) := mul_le_mul_of_nonneg_right hlower (by positivity)
      _ ≤ 3 * m * w ^ (-(2 * b)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hw (neg_le_neg hs))
          (by positivity)
  calc
    _ ≤ 4 * (m * w ^ (-(2 * b))) := by linarith
    _ ≤ w ^ b * (m * w ^ (-(2 * b))) := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = m * w ^ (-b) := by
      rw [mul_left_comm, ← Real.rpow_add hw', show b + -(2 * b) = -b by ring]

/-- Fix a number of iterations before choosing the width. The total number
of copies and the size per bit each cost at most an extra exponent of 1/40. -/
theorem incompatible {P : ℕ → ℕ → ℕ → Prop}
    (seed : Seed P) (lower : ManyList P) (compress : Compression P) : False := by
  obtain ⟨C, hseed⟩ := seed
  obtain ⟨σ, hs, hlower⟩ := lower
  obtain ⟨γ, hg, hcompress⟩ := compress (σ / 4) (by positivity)
  let b := min γ (σ / 2) / 2
  have hb : 0 < b := half_pos (lt_min hg (half_pos hs))
  have hbg : 2 * b ≤ γ := by dsimp [b]; linarith [min_le_left γ (σ / 2)]
  have hbs : 2 * b ≤ σ / 2 := by dsimp [b]; linarith [min_le_right γ (σ / 2)]
  obtain ⟨J, hJ⟩ := exists_nat_gt (3 / b)
  have hstop : 3 < (J : ℝ) * b := (div_lt_iff₀ hb).mp hJ
  have hJpos : 0 < (J : ℝ) := lt_trans (by positivity) hJ
  let δ := (1 / 40 : ℝ) / J
  have hδ : 0 < δ := div_pos (by norm_num) hJpos
  obtain ⟨w, ⟨hw, hC, hbpow, hcube⟩, ⟨m₀, h₀, hm₀⟩, hl, hc⟩ :=
    ((large hb C).and (hseed.and (hlower.and (hcompress δ hδ)))).exists
  let n := listBits w
  let h : ℝ := Nat.clog 2 n
  have hh : (w : ℝ) ≤ h := by unfold h; exact_mod_cast (clog_bounds hw).1
  have hh' : h ≤ (w : ℝ) ^ 2 := by unfold h; exact_mod_cast (clog_bounds hw).2
  have hw₁ : 1 ≤ (w : ℝ) := by exact_mod_cast (by omega : 1 ≤ w)
  have hw₀ : 0 < (w : ℝ) := zero_lt_one.trans_le hw₁
  have hn : 0 < n := by unfold n listBits; positivity
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁
  have copies {j t : ℕ} (hj : j ≤ J) (ht : (t : ℝ) ≤ (n : ℝ) ^ ((j : ℝ) * δ)) :
      (t : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) := by
    apply ht.trans (Real.rpow_le_rpow_of_exponent_le hn₁ ?_)
    calc
      _ ≤ (J : ℝ) * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ.le
      _ = 1 / 40 := by unfold δ; field_simp
  have within {t : ℕ} (ht : (t : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ)) : t ≤ n := by
    have h : (n : ℝ) ^ (1 / 40 : ℝ) ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (1 / 40 : ℝ) ≤ 1)
    exact_mod_cast ht.trans h
  have iterate (j : ℕ) (hj : j ≤ J) :
      ∃ t m : ℕ, 1 ≤ t ∧ P w t m ∧ (t : ℝ) ≤ (n : ℝ) ^ ((j : ℝ) * δ) ∧
        (m : ℝ) ≤ (t : ℝ) * n * (w : ℝ) ^ (3 - j * b) := by
    induction j with
    | zero =>
      refine ⟨1, m₀, le_rfl, h₀, by simp, ?_⟩
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, sub_zero, one_mul]
      calc
        _ ≤ C * (n : ℝ) * (w : ℝ) ^ 2 := hm₀
        _ ≤ (w : ℝ) * n * (w : ℝ) ^ 2 := by gcongr
        _ = (n : ℝ) * (w : ℝ) ^ (3 : ℝ) := by norm_num; ring
    | succ j ih =>
      have hj' : j ≤ J := Nat.le_of_succ_le hj
      obtain ⟨t, m, ht, hp, htj, hmj⟩ := ih hj'
      have ht' := copies hj' htj
      have hl' := hl t m ht (within ht') hp
      have hper : (w : ℝ) ^ (3 - j * b) ≤ (n : ℝ) ^ (1 / 40 : ℝ) :=
        (Real.rpow_le_rpow_of_exponent_le hw₁ (sub_le_self _ (by positivity))).trans hcube
      have hsize : (m : ℝ) ≤ (n : ℝ) ^ (21 / 20 : ℝ) := by
        calc
          _ ≤ (t : ℝ) * n * (w : ℝ) ^ (3 - j * b) := hmj
          _ ≤ (n : ℝ) ^ (1 / 40 : ℝ) * n * (n : ℝ) ^ (1 / 40 : ℝ) :=
            mul_le_mul (mul_le_mul_of_nonneg_right ht' hn₀.le) hper (by positivity) (by positivity)
          _ = (n : ℝ) ^ (21 / 20 : ℝ) := by
            rw [show (21 / 20 : ℝ) = 1 / 40 + 1 + 1 / 40 by norm_num,
              Real.rpow_add hn₀, Real.rpow_add hn₀, Real.rpow_one]
      obtain ⟨d, m', hd, hdδ, hp', hm'⟩ := hc t m ht hp hsize
      refine ⟨t * d, m', Nat.mul_pos ht hd, hp', ?_, ?_⟩
      · rw [Nat.cast_mul, Nat.cast_succ, add_mul, one_mul, Real.rpow_add hn₀]
        exact mul_le_mul htj hdδ (by positivity) (by positivity)
      · calc
          _ ≤ (d : ℝ) * ((m : ℝ) * h ^ (-γ) + t * (n : ℝ) * h ^ (σ / 4)) := hm'
          _ ≤ (d : ℝ) * ((m : ℝ) * (w : ℝ) ^ (-b)) :=
            mul_le_mul_of_nonneg_left
              (absorb hw₁ hh hh' (by positivity) (by positivity) hbpow hb hbg hbs hl'.le)
              (by positivity)
          _ ≤ (d : ℝ) * ((t : ℝ) * n * (w : ℝ) ^ (3 - j * b) * (w : ℝ) ^ (-b)) := by gcongr
          _ = ((t * d : ℕ) : ℝ) * n * (w : ℝ) ^ (3 - (j.succ : ℝ) * b) := by
            rw [Nat.cast_mul, Nat.cast_succ, show 3 - ((j : ℝ) + 1) * b =
              (3 - (j : ℝ) * b) + -b by ring, Real.rpow_add hw₀]
            ring
  obtain ⟨t, m, ht, hp, htJ, hmJ⟩ := iterate J le_rfl
  apply (hl t m ht (within (copies le_rfl htJ)) hp).not_ge
  have hfinal : (m : ℝ) ≤ (t : ℝ) * n := by
    apply hmJ.trans
    exact mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos hw₁ (by linarith))
  have hthree : 3 ≤ (w : ℝ) ^ σ := (by linarith : 3 ≤ (w : ℝ) ^ b).trans
    (Real.rpow_le_rpow_of_exponent_le hw₁ (by linarith))
  calc
    3 * (m : ℝ) = (m : ℝ) * 3 := mul_comm _ _
    _ ≤ (t : ℝ) * n * (w : ℝ) ^ σ := mul_le_mul hfinal hthree (by norm_num) (by positivity)

end OAI.LinearAlgebra.MatrixExponent
