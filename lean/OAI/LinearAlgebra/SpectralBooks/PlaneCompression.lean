import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Iterating the compression of spherical maps

In the Tree case of the circuit dichotomy, each network compression replaces
the size bound `N` by `max 1 (N / a)`. Its table width satisfies
`w' ≤ 10 w + B log(2N)`. Here we count all successive table-building gates,
including the last contraction, and recover the exponent `log_a 10` in the
planar network bound used to exclude Tree.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- The remaining vertex bound after `j` compression rounds. -/
def compressedVertexBound (a N j : ℕ) : ℕ := max 1 (N / a ^ j)

theorem compressedVertexBound_succ {a : ℕ} (ha : 1 < a) (N j : ℕ) :
    compressedVertexBound a N (j+1) = max 1 (compressedVertexBound a N j / a) := by
  unfold compressedVertexBound
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  by_cases h : N / a ^ j = 0
  · simp [h, Nat.div_eq_of_lt ha]
  · rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr h)]

theorem compressedVertexBound_clog {a : ℕ} (ha : 1 < a) (N : ℕ) :
    compressedVertexBound a N (Nat.clog a N) = 1 :=
  max_eq_left (Nat.div_le_of_le_mul (by simpa using Nat.le_pow_clog ha N))

private theorem ten_pow_rounds_le {a N : ℕ} (ha : 1 < a) (hN : 1 ≤ N) :
    (10:ℝ)^Nat.clog a N ≤ 10 * (N:ℝ)^Real.logb a 10 := by
  have ha' : (1:ℝ) < a := by exact_mod_cast ha
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have h := Nat.ceil_lt_add_one (Real.logb_nonneg ha' hN')
  rw [Real.natCeil_logb_natCast] at h
  calc
    _ = (10:ℝ) ^ ((Nat.clog a N:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (10:ℝ) ^ (Real.logb a N + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h.le
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 10), Real.rpow_one, mul_comm]
      congr 1
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 10),
        Real.rpow_def_of_pos (zero_lt_one.trans_le hN')]
      congr 1
      unfold Real.logb
      ring

/-- Adding a fixed width charge once makes the accumulated width geometric. -/
private theorem compressedWidth {w : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) {L : ℕ}
    (hu : ∀ i, i < L → w (i+1) ≤ 10 * w i + B) (j : ℕ) (hj : j ≤ L) :
    w j + B ≤ (10:ℝ)^j * (w 0 + B) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := hu j (by omega)
    have g := ih (by omega)
    rw [pow_succ]
    linarith only [h, g, hB]

/-- Uniform constants in the width and gate estimates give a uniform
`2 ^ (C * N^(log_a 10) * log(2N))` upper bound after all rounds. The last
entry of `cost` accounts for contraction at the one-vertex bound. -/
theorem iterated_compression_size {a N : ℕ} (ha : 1 < a) (hN : 1 ≤ N)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w cost : ℕ → ℝ)
    (init : w 0 ≤ B * Real.log (2*N))
    (width : ∀ j, j < Nat.clog a N → w (j+1) ≤ 10 * w j + B * Real.log (2*N))
    (gates : ∀ j, j ≤ Nat.clog a N → cost j ≤ (2:ℝ)^(A * (w j + Real.log (2*N)))) :
    ∑ j ∈ Finset.range (Nat.clog a N + 1), cost j ≤
      (2:ℝ)^((10 / Real.log 2 + A * (20*B + 1)) * ((N:ℝ)^Real.logb a 10 * Real.log (2*N))) := by
  let L := Nat.clog a N
  let P := (N:ℝ)^Real.logb a 10
  let b := Real.log (2*N)
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : Real.log 2 ≤ b := Real.log_le_log (by norm_num) (show (2:ℝ) ≤ 2*N by linarith)
  have hP : 1 ≤ P := Real.one_le_rpow hN' (Real.logb_nonneg (by exact_mod_cast ha) (by norm_num))
  have hL := ten_pow_rounds_le ha hN
  change (10:ℝ)^L ≤ 10 * P at hL
  have hmax (j : ℕ) (hj : j ≤ L) : w j + b ≤ (20*B + 1) * (P*b) := by
    have hc := compressedWidth (mul_nonneg hB (hlog.le.trans hb)) width j hj
    have hi : (10:ℝ)^j ≤ 10*P := (pow_le_pow_right₀ (by norm_num) hj).trans hL
    have hh : (10:ℝ)^j * (w 0 + B*b) ≤ (10*P) * (2*B*b) := by
      apply (mul_le_mul_of_nonneg_left (show w 0 + B*b ≤ 2*B*b by linarith [init]) (by positivity)).trans
      exact mul_le_mul_of_nonneg_right hi (mul_nonneg (by positivity) (hlog.le.trans hb))
    change w j + B*b ≤ (10:ℝ)^j * (w 0 + B*b) at hc
    have hPb : b ≤ P*b := le_mul_of_one_le_left (hlog.le.trans hb) hP
    linarith only [hc, hh, hPb, mul_nonneg hB (hlog.le.trans hb)]
  let G := (2:ℝ) ^ (A * ((20*B + 1)*(P*b)))
  have allcost (j : ℕ) (hj : j < L+1) : cost j ≤ G :=
    (gates j (by omega)).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (hmax j (by omega)) hA))
  have hround : (L : ℝ) ≤ 10 / Real.log 2 * (P*b) := by
    have hn : (L:ℝ) ≤ (10:ℝ)^L := by exact_mod_cast (Nat.lt_pow_self (a := 10) (n := L) (by decide)).le
    apply (hn.trans hL).trans
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 10 * P by positivity)
    apply (le_div_iff₀ hlog).mpr at hh
    convert hh using 1
    ring
  calc
    _ ≤ ∑ _j ∈ Finset.range (L+1), G :=
      Finset.sum_le_sum fun j hj => allcost j (Finset.mem_range.mp hj)
    _ = ((L+1 : ℕ) : ℝ) * G := by simp
    _ ≤ (2:ℝ) ^ (L:ℝ) * G := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
      rw [Real.rpow_natCast]
      exact_mod_cast (show L+1 ≤ 2^L from Nat.lt_two_pow_self)
    _ ≤ (2:ℝ) ^ (10 / Real.log 2 * (P*b)) * G := by
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hround)
        (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by
      dsimp only [G]
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      change _ = (10 / Real.log 2 + A * (20*B+1)) * (P*b)
      ring

/-- A one-step table-building bound iterates to the planar network estimate.
`cost n w` is the cost of computing the scalar sum with vertex bound `n` and
width `w`. It may share every intermediate table entry wherever it is used. -/
theorem planar_size_of_compression_step {a N W : ℕ} (ha : 1 < a) (hN : 1 ≤ N) (hW : 0 < W)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (cost : ℕ → ℕ → ℝ)
    (initial : (W : ℝ) ≤ B * Real.log (2*N))
    (base : ∀ w : ℕ, 0 < w → cost 1 w ≤ (2:ℝ)^(A * (w + Real.log 2)))
    (step : ∀ n w : ℕ, 1 < n → 0 < w → ∃ w' : ℕ, 0 < w' ∧
      (w' : ℝ) ≤ 10*w + B * Real.log (2*n) ∧
      cost n w ≤ (2:ℝ)^(A * (w + Real.log (2*n))) + cost (max 1 (n/a)) w') :
    cost N W ≤ (2:ℝ)^((10 / Real.log 2 + A * (20*B + 1)) *
      ((N:ℝ)^Real.logb a 10 * Real.log (2*N))) := by
  let n := compressedVertexBound a N
  have hpos (j : ℕ) : 1 ≤ n j := le_max_left _ _
  have hle (j : ℕ) : n j ≤ N := max_le hN (Nat.div_le_self _ _)
  have hlog (j : ℕ) : Real.log (2*n j) ≤ Real.log (2*N) :=
    Real.log_le_log (by positivity [show (0:ℝ) < n j by exact_mod_cast hpos j]) (by
      gcongr
      exact hle j)
  have hlogN : 0 ≤ Real.log (2*N) :=
    Real.log_nonneg (by
      have : (1:ℝ) ≤ N := by exact_mod_cast hN
      linarith)
  let Width := {w : ℕ // 0 < w}
  have hs (j : ℕ) (w : Width) : ∃ v : Width, (v.val : ℝ) ≤ 10 * w.val + B * Real.log (2*N) ∧
      cost (n j) w.val ≤ (2:ℝ)^(A * (w.val + Real.log (2*N))) + cost (n (j+1)) v.val := by
    by_cases hj : 1 < n j
    · obtain ⟨v, hvpos, hv, hc⟩ := step (n j) w.val hj w.property
      refine ⟨⟨v, hvpos⟩, hv.trans (add_le_add_right (mul_le_mul_of_nonneg_left (hlog j) hB) _), hc.trans ?_⟩
      rw [show n (j+1) = max 1 (n j / a) from compressedVertexBound_succ ha N j]
      gcongr
      · norm_num
      · exact hle j
    · have heq : n j = 1 := le_antisymm (by omega) (hpos j)
      have heq' : n (j+1) = 1 := by
        rw [show n (j+1) = max 1 (n j / a) from compressedVertexBound_succ ha N j, heq, Nat.div_eq_of_lt ha]
        rfl
      refine ⟨w, ?_, ?_⟩
      · nlinarith only [mul_nonneg hB hlogN, Nat.cast_nonneg (α := ℝ) w.val]
      · rw [heq, heq']
        linarith only [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (A * (w.val + Real.log (2*N)))]
  choose next hw hc using hs
  let v (j : ℕ) : Width := Nat.rec (motive := fun _ => Width) ⟨W,hW⟩ next j
  let w (j : ℕ) : ℕ := (v j).val
  let G (j : ℕ) := (2:ℝ)^(A * (w j + Real.log (2*N)))
  have hc' (j : ℕ) : cost (n j) (w j) ≤ G j + cost (n (j+1)) (w (j+1)) := hc j (v j)
  have total (j : ℕ) : cost N W ≤ ∑ i ∈ Finset.range j, G i + cost (n j) (w j) := by
    induction j with
    | zero => simp [n, compressedVertexBound, w, v, max_eq_right hN]
    | succ j ih =>
      have h := hc' j
      rw [Finset.sum_range_succ]
      linarith only [h, ih]
  let L := Nat.clog a N
  have hbase : cost (n L) (w L) ≤ G L := by
    rw [show n L = 1 from compressedVertexBound_clog ha N]
    apply (base _ (v L).property).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_left _ hA
    apply add_le_add_right
    apply Real.log_le_log (by norm_num)
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  calc
    _ ≤ ∑ i ∈ Finset.range L, G i + G L := (total L).trans (add_le_add_right hbase _)
    _ = ∑ i ∈ Finset.range (L+1), G i := (Finset.sum_range_succ ..).symm
    _ ≤ _ := iterated_compression_size ha hN A B hA hB (fun j => w j) G initial
      (fun j _ => hw j (v j)) (fun _ _ => le_rfl)

end SpectralBooks
end LinearAlgebra
end OAI
