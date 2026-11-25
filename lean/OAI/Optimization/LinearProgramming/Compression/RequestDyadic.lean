import OAI.Optimization.LinearProgramming.Compression.RequestGrid
import OAI.Optimization.LinearProgramming.Compression.CommitProgram

/-! Exact floor decoding of the homogeneous dyadic search for a minor-request residual.
The half-open interval convention preserves equality at any tested grid boundary. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open _root_.OAI.Optimization.LinearProgramming.Lattice
open scoped BigOperators

/-- The query for equality takes the upper half, so the right endpoint stays strict. -/
theorem dyadicSearch_halfOpen {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (x : Fin p → ℝ) (ho : ∀ row, oracle row = true ↔ 0 ≤ formValue row x)
    (hl : -(formValue b x) ≤ formValue a x) (hu : formValue a x < formValue b x) (k : ℕ) :
    let n := (dyadicSearch oracle a b k).numerator
    ((n : ℝ)-1)*formValue b x ≤ (2:ℝ)^k*formValue a x ∧
      (2:ℝ)^k*formValue a x < ((n : ℝ)+1)*formValue b x := by
  induction k with
  | zero => simpa [dyadicSearch] using And.intro hl hu
  | succ k ih =>
    let n := (dyadicSearch oracle a b k).numerator
    change ((n : ℝ)-1)*formValue b x ≤ _ ∧ _ < ((n : ℝ)+1)*formValue b x at ih
    rcases ih with ⟨hlow,hhigh⟩
    let row := dyadicQuery a b k n
    have hrow := ho row
    rw [show formValue row x = _ from dyadicQuery_value a b x k n] at hrow
    by_cases h : oracle row = true
    · have hb := hrow.mp h
      change let t := 2*n+(if oracle row then (1:ℤ) else -1);
        ((t : ℝ)-1)*formValue b x ≤ _ ∧ _ < ((t : ℝ)+1)*formValue b x
      simp only [h, ↓reduceIte, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, pow_succ]
      constructor <;> nlinarith only [hb,hhigh]
    · have hb := lt_of_not_ge (fun h' => h (hrow.mpr h'))
      have hf := Bool.eq_false_iff.mpr h
      change let t := 2*n+(if oracle row then (1:ℤ) else -1);
        ((t : ℝ)-1)*formValue b x ≤ _ ∧ _ < ((t : ℝ)+1)*formValue b x
      simp [hf, pow_succ]
      constructor <;> nlinarith only [hb,hlow]

private theorem dyadicSearch_odd_midpoint {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (k : ℕ) : ∃ t : ℤ, (dyadicSearch oracle a b (k+1)).numerator = 2*t+1 := by
  let n := (dyadicSearch oracle a b k).numerator
  change ∃ t, 2*n+(if oracle (dyadicQuery a b k n) then 1 else -1) = _
  by_cases h : oracle (dyadicQuery a b k n) = true
  · exact ⟨n, by simp [h]⟩
  · exact ⟨n-1, by simp [h]; omega⟩

/-- Interpret an exact sign decision tree as a floor routine on an integral half-open
interval of power-of-two length. All quantities used to decode the floor are integers. -/
theorem floor_from_dyadicSearch {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ)
    (x : Fin p → ℝ) (ho : ∀ row, oracle row = true ↔ 0 ≤ formValue row x)
    (k : ℕ) (lo : ℤ) (t C : ℝ) (hC : 0 < C)
    (hlo : (lo : ℝ) ≤ t) (hhi : t < lo + (2:ℝ)^(k+1))
    (ha : formValue a x = C * (2*(t-lo)-(2:ℝ)^(k+1)))
    (hb : formValue b x = C * (2:ℝ)^(k+1)) :
    ⌊t⌋ = lo + ((dyadicSearch oracle a b (k+1)).numerator + (2:ℤ)^(k+1)-1)/2 := by
  let W := (2:ℝ)^(k+1)
  have hW : 0 < W := by positivity
  obtain ⟨hc0,hc1⟩ := dyadicSearch_halfOpen oracle a b x ho
    (by rw [ha,hb]; nlinarith only [mul_nonneg hC.le (sub_nonneg.mpr hlo)])
    (by rw [ha,hb]; nlinarith only [mul_pos hC (sub_pos.mpr hhi)]) (k+1)
  let n := (dyadicSearch oracle a b (k+1)).numerator
  have hint : ((n:ℝ)-1) ≤ 2*(t-lo)-W ∧ 2*(t-lo)-W < ((n:ℝ)+1) := by
    have he : formValue b x = C*W := hb
    have he' : formValue a x = C*(2*(t-lo)-W) := ha
    rw [he,he'] at hc0 hc1
    change ((n:ℝ)-1)*(C*W) ≤ W*(C*(2*(t-lo)-W)) at hc0
    change W*(C*(2*(t-lo)-W)) < ((n:ℝ)+1)*(C*W) at hc1
    have hpos := mul_pos hC hW
    constructor
    · apply (mul_le_mul_iff_of_pos_right hpos).mp
      linarith only [hc0]
    · apply (mul_lt_mul_iff_of_pos_right hpos).mp
      linarith only [hc1]
  obtain ⟨m, hm⟩ := dyadicSearch_odd_midpoint oracle a b k
  change n = 2*m+1 at hm
  rw [hm] at hint
  have he : ((2*m+1)+(2:ℤ)^(k+1)-1)/2 = m+(2:ℤ)^k := by rw [pow_succ]; omega
  change ⌊t⌋ = lo+(n+(2:ℤ)^(k+1)-1)/2
  rw [hm, he]
  apply Int.floor_eq_iff.mpr
  dsimp [W] at hint
  rw [pow_succ] at hint
  push_cast at hint ⊢
  constructor <;> linarith only [hint.1,hint.2]

/-- Homogeneous query rows comparing the scaled residual to dyadic subdivision points.
The last coordinate of the input to these rows is one. -/
def requestDyadicRows {d : ℕ} (z : Fin d → ℤ) (last : Fin d) (q : ℕ) (lo W : ℤ) :
    (Fin (d+1) → ℤ) × (Fin (d+1) → ℤ) :=
  let s : ℤ := if 0 < z last then 1 else -1
  (Fin.snoc (fun i => (2*q : ℤ)*s*z i) (-(2*lo+W)*|z last|),
   Fin.snoc (fun _ => 0) (W*|z last|))

private theorem requestDyadicRows_eval {d : ℕ} (v : Fin d → ℝ) (z : Fin d → ℤ)
    (last : Fin d) (hn : z last ≠ 0) (q : ℕ) (lo W : ℤ) :
    let rows := requestDyadicRows z last q lo W
    let x := Fin.snoc v 1
    formValue rows.1 x = |(z last : ℝ)| * (2*((q:ℝ)*(requestForm v z/(z last:ℝ))-lo)-W) ∧
      formValue rows.2 x = |(z last : ℝ)| * (W:ℝ) := by
  dsimp only
  have hne : (z last : ℝ) ≠ 0 := by exact_mod_cast hn
  have hcoeff (s : ℤ) :
    (∑ i, ((((2*(q:ℤ))*s*z i : ℤ) : ℝ) * v i)) = (2*(q:ℝ))*(s:ℝ)*requestForm v z := by
    simp only [requestForm, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Finset.mul_sum, mul_assoc]
  simp only [requestDyadicRows, formValue, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Int.cast_zero, zero_mul, Finset.sum_const_zero, zero_add, mul_one]
  rw [hcoeff]
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_abs]
  constructor
  · by_cases hz : 0 < z last
    · have hz' : 0 < (z last : ℝ) := by exact_mod_cast hz
      rw [ite_eq_left hz, Int.cast_one, abs_of_pos hz']
      field_simp
      ring
    · have hz' : (z last : ℝ) < 0 := by exact_mod_cast lt_of_le_of_ne (le_of_not_gt hz) hn
      rw [ite_eq_right hz, Int.cast_neg, Int.cast_one, abs_of_neg hz']
      field_simp
      ring
  · ring

/-- Exact agreement between the residual integer from the actual request and the decoded
midpoint returned by the compiled homogeneous sign-query bisection. -/
theorem requestGridRun_eq_dyadicSearch {d : ℕ} (v : Fin d → ℝ)
    (neg : (Fin d → ℤ) → ℤ → Bool) (ho : ∀ z c, neg z c = true ↔ requestForm v z+c<0)
    (z : Fin d → ℤ) (last : Fin d) (hn : z last ≠ 0) (q K : ℕ)
    (hr : |requestForm v z/(z last : ℝ)| ≤ K) :
    let lo := -(K*q : ℤ)
    let k := (2*K*q).log2
    let W := (2:ℤ)^(k+1)
    let rows := requestDyadicRows z last q lo W
    let m := (dyadicSearch (affineCommitReply neg) rows.1 rows.2 (k+1)).numerator
    (requestGridRun neg z last q K).1 = lo+(m+W-1)/2 := by
  intro lo k W rows m
  rw [requestGridRun_correct _ _ ho _ _ hn _ _ hr]
  let t := (q:ℝ)*(requestForm v z/(z last:ℝ))
  obtain ⟨hl,hu⟩ := abs_le.mp hr
  have hq : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hlo := mul_le_mul_of_nonneg_left hl hq
  have hhi := mul_le_mul_of_nonneg_left hu hq
  have hp : (2:ℝ)*K*q < 2^(k+1) := by exact_mod_cast (Nat.lt_log2_self (n:=2*K*q))
  obtain ⟨ha,hb⟩ := requestDyadicRows_eval v z last hn q lo W
  have hcast : (W:ℝ) = 2^(k+1) := by simp [W]
  rw [hcast] at ha hb
  apply floor_from_dyadicSearch (affineCommitReply neg) rows.1 rows.2 (Fin.snoc v 1)
    (affineCommitReply_correct v neg ho) k lo t |(z last:ℝ)| (abs_pos.mpr (by exact_mod_cast hn))
  · dsimp [t,lo]; push_cast; linarith only [hlo]
  · dsimp [t,lo]; push_cast; linarith only [hhi,hp]
  · exact ha
  · exact hb

end Compression
end LinearProgramming
end Optimization
end OAI
