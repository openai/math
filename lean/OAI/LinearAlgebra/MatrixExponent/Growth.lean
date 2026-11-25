import OAI.LinearAlgebra.MatrixExponent.BlockRecursion
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Bounds
import Mathlib.Data.Nat.Log

/-!
# From a fixed block to every dimension

Positive exponent slack pays for linear combinations even when the
block rank equals the largest of the input and output areas.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

private theorem bound_powers {r A D : ℕ} {cost : ℕ → ℕ} {t : ℝ}
    (hA : A ≤ r) (hr : (r : ℝ) < t)
    (ha : ∀ j, cost (j + 1) ≤ r * cost j + D * A ^ j) :
    ∃ M : ℝ, 0 < M ∧ ∀ j, (cost j : ℝ) ≤ M * t ^ j := by
  have ht : 0 < t := (Nat.cast_nonneg _).trans_lt hr
  let M := max ((cost 0 : ℝ) + 1) ((D : ℝ) / (t - r))
  have hbase : (cost 0 : ℝ) < M := lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)
  have hstep : (r : ℝ) * M + D ≤ M * t := by
    have h : (D : ℝ) ≤ M * (t - r) :=
      (div_le_iff₀ (sub_pos.mpr hr)).mp (le_max_right _ _)
    linarith
  refine ⟨M, (Nat.cast_nonneg _).trans_lt hbase, ?_⟩
  intro j
  induction j with
  | zero => simpa using hbase.le
  | succ j ih =>
    have harea : (A : ℝ) ^ j ≤ t ^ j :=
      pow_le_pow_left₀ (by positivity) ((Nat.cast_le.mpr hA).trans hr.le) _
    calc
      (cost (j + 1) : ℝ) ≤ (r : ℝ) * cost j + D * (A : ℝ) ^ j := by exact_mod_cast ha j
      _ ≤ (r : ℝ) * (M * t ^ j) + D * t ^ j := by gcongr
      _ = ((r : ℝ) * M + D) * t ^ j := by ring
      _ ≤ (M * t) * t ^ j := mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = M * t ^ (j + 1) := by rw [pow_succ', mul_assoc]

theorem side_pow {n i : ℕ} {a : ℝ} (hi : side n a ≤ i) (p : ℕ) :
    side (n ^ p) a ≤ i ^ p := by
  apply Nat.ceil_le.mpr
  rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity),
    mul_comm, Real.rpow_mul_natCast (by positivity)]
  exact pow_le_pow_left₀ (by positivity) (Nat.ceil_le.mp hi) _

/-- A block whose three side lengths dominate the prescribed dimensions
at a single base `n` suffices at all dimensions. -/
theorem integral_of_rank {F : Type*} [CommRing F] {n i j k r : ℕ} {a b c s : ℝ}
    (hn : 2 ≤ n) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hi : side n a ≤ i) (hj : side n b ≤ j) (hk : side n c ≤ k)
    (hr : Integral.Rank F i j k r) (hA : max (i * j) (max (i * k) (j * k)) ≤ r) (hrs : (r : ℝ) ≤ (n : ℝ) ^ s) :
    Integral.Admissible F a b c s := by
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hi₀ := (side_pos (by omega) a).trans_le hi
  have hj₀ := (side_pos (by omega) b).trans_le hj
  have hs : 0 ≤ s := by
    apply (Real.rpow_le_rpow_left_iff hn₁).mp
    rw [Real.rpow_zero]
    exact le_trans (by exact_mod_cast (Nat.mul_pos hi₀ hj₀).trans_le ((le_max_left _ _).trans hA)) hrs
  intro ε hε
  have hr' : (r : ℝ) < (n : ℝ) ^ (s + ε) :=
    hrs.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hn₁ (lt_add_of_pos_right s hε))
  obtain ⟨D, cost, hstep, hpad⟩ := integral_power_cost hr
  obtain ⟨M, hM, hbound⟩ := bound_powers hA hr' hstep
  refine ⟨M * (n : ℝ) ^ (s + ε), by positivity, ?_⟩
  intro m hm
  let p := Nat.log n m + 1
  have hlo : m ≤ n ^ p := (Nat.lt_pow_succ_log_self (by omega : 1 < n) m).le
  have hhi : n ^ p ≤ n * m := by
    rw [show p = Nat.log n m + 1 from rfl, pow_succ']
    exact Nat.mul_le_mul_left n (Nat.pow_log_le_self n (by omega))
  have pad {a : ℝ} {i : ℕ} (ha : 0 ≤ a) (hi : side n a ≤ i) : side m a ≤ i ^ p :=
    (Nat.ceil_mono (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlo) ha)).trans
      (side_pow hi p)
  obtain ⟨t, ht, hcost⟩ := hpad p _ _ _ (pad ha hi) (pad hb hj) (pad hc hk)
  refine ⟨t, ht, ?_⟩
  calc
    (t : ℝ) ≤ (cost p : ℝ) := by exact_mod_cast hcost
    _ ≤ M * ((n : ℝ) ^ (s + ε)) ^ p := hbound p
    _ = M * ((n : ℝ) ^ p) ^ (s + ε) := by
      rw [← Real.rpow_mul_natCast (by positivity), ← Real.rpow_natCast_mul (by positivity),
        mul_comm (s + ε)]
    _ ≤ M * ((n : ℝ) * m) ^ (s + ε) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hhi) (by linarith)) hM.le
    _ = M * (n : ℝ) ^ (s + ε) * (m : ℝ) ^ (s + ε) := by
      rw [Real.mul_rpow (by positivity) (by positivity), mul_assoc]

theorem admissible_of_rank {F : Type*} [Field F] {n i j k r : ℕ} {a b c s : ℝ}
    (hn : 2 ≤ n) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hi : side n a ≤ i) (hj : side n b ≤ j) (hk : side n c ≤ k)
    (hr : RankLE F i j k r) (hrs : (r : ℝ) ≤ (n : ℝ) ^ s) :
    Admissible F a b c s := by
  have hi₀ := (side_pos (by omega) a).trans_le hi
  have hj₀ := (side_pos (by omega) b).trans_le hj
  have hk₀ := (side_pos (by omega) c).trans_le hk
  have hA : max (i * j) (max (i * k) (j * k)) ≤ r :=
    max_le (hr.area hk₀) (max_le (hr.transpose.cycle.area hj₀) (hr.cycle.area hi₀))
  exact (integral_of_rank hn ha hb hc hi hj hk hr hA hrs).field (RingHom.id F)

end OAI.LinearAlgebra.MatrixExponent.Rectangle

namespace OAI.LinearAlgebra.MatrixExponent

theorem admissible_of_rank {F : Type*} [Field F] {n r : ℕ} {s : ℝ}
    (hn : 2 ≤ n) (hr : RankLE F n r) (_hs : 2 ≤ s) (hrs : (r : ℝ) ≤ (n : ℝ) ^ s) :
    Admissible F s := by
  have h := Rectangle.admissible_of_rank hn zero_le_one zero_le_one zero_le_one
    (Rectangle.side_one n).le (Rectangle.side_one n).le (Rectangle.side_one n).le hr hrs
  simp only [Rectangle.Admissible, Rectangle.side_one] at h
  exact h

theorem admissible_three (F : Type*) [Field F] : Admissible F 3 :=
  admissible_of_rank (by decide) (Rectangle.rank_volume F 2 2 2) (by norm_num) (by norm_num)

end OAI.LinearAlgebra.MatrixExponent
