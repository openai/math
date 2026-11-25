import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionWeightCost
import OAI.Optimization.LinearProgramming.PriceGame.TrialWeightArithmetic
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionSize

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

theorem Computation.AllOutputs.guarded {N : ℕ} {α : Type*} {P : α → Prop}
    {p : Computation N α} (h : p.AllOutputs P) : p.Guarded (fun _ => True) P := by
  induction h with
  | pure ha => exact ha
  | ask _ ih => exact ⟨True.intro, ih⟩

theorem Computation.guarded_and {N : ℕ} {α : Type*} {Q : Query N → Prop}
    {P R : α → Prop} {p : Computation N α} (hp : p.Guarded Q P) (hr : p.Guarded Q R) :
    p.Guarded Q (fun a => P a ∧ R a) := by
  induction p with
  | pure => exact ⟨hp, hr⟩
  | ask q k ih => exact ⟨hp.1, fun b => ih b (hp.2 b) (hr.2 b)⟩

namespace TrialExecution

open Moment States.Mass Finset

variable {N ne r l : ℕ}

/-- The cached score of each child adds its value, in bits, to its deeper expert's magnitude. -/
theorem incomingDeep_cap (experts : Fin ne → Expert N) (w : Weights ne)
    {Q b : ℕ} (h : WeightInputCap Q b w) (S : ℕ) {j : ℕ}
    (xs : Fin j → Call N ne r l) (hc : ∀ i e, callScore (xs i) e ≤ S) :
    WeightInputCap Q (b + j*S) (incomingDeep experts w xs) := by
  refine ⟨incomingDeep_den_dvd experts w Q h.den xs, ?_⟩
  intro e
  have hsum : (∑ k ∈ range j, probeAt (fun i => callScore (xs i)) k e) ≤ j*S := by
    calc
      _ ≤ ∑ _k ∈ range j, S := sum_le_sum fun k hk => by
        have ht := mem_range.mp hk
        simpa [probeAt, ht] using hc ⟨k,ht⟩ e
      _ = _ := by simp
  have hm : deepPartQ (mask experts l) w e ≤ (2 : ℚ)^b := by
    unfold deepPartQ
    split
    · positivity
    · exact h.upper e
  unfold incomingDeep deepWeightQ
  rw [pow_add]
  exact mul_le_mul hm (pow_le_pow_right₀ (by norm_num) hsum) (by positivity) (by positivity)

/-- Bounds all deeper input registers, including their common denominator, after every
prefix of an adaptive schedule. Child heights, hence scores, are guaranteed for every reply. -/
theorem schedule_deepWeightCap (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (hchild : ∀ y dw hdw, (child y dw hdw).AllOutputs (fun c => c.val.trace.height ≤ depth N))
    {Q b : ℕ} (h : WeightInputCap Q b w) (hN : 0 < N) (n : ℕ) :
    (runSchedule (fun _ xs c => StepOK experts w xs c)
      (executeStep experts solve w hw history path child) n).Guarded
      (fun _ => True) (fun xs => ∀ t (ht : t ≤ n), WeightInputCap Q (b+t*(2*N)^274)
        (incomingDeep experts w (takePrefix xs.val t ht))) := by
  have heights := runSchedule_all (fun _ xs c => StepOK experts w xs c)
    (executeStep experts solve w hw history path child)
    (fun c => c.child.trace.height ≤ depth N) n (fun j _ xs =>
      executeStep_all_child_height experts solve w hw history path child (depth N) hchild j xs)
  apply Computation.guarded_mono heights.guarded (fun _ _ => True.intro)
  intro xs hs t ht
  apply incomingDeep_cap experts w h
  intro i e
  let j : Fin n := ⟨i.val, lt_of_lt_of_le i.isLt ht⟩
  let out : Certified (N:=N) (r:=r) (l:=l+1) (incomingDeep experts w («prefix» xs.val j)) :=
    ⟨(xs.val j).child, (xs.property j).admissible⟩
  have hh : out.val.trace.height ≤ Nat.log 2 N + 1 := by
    simpa only [out, depth, Nat.log2_eq_log_two] using hs j
  exact certified_score_le_public _ out hN hh e

/-- Replaying a completed prefix of local probes yields the reduced numerator and
denominator encoding used on the RAM. The masks can set arbitrary incoming weights to zero. -/
theorem LocalWeightBudget.ratBits {Q b d r t : ℕ} {w L : Weights ne}
    (h : LocalWeightBudget Q r t w L) (hQ : 0 < Q) (hcap : Q ≤ 2^d)
    (hw : ∀ e, w e ≤ (2 : ℚ)^b) (hL : ∀ e, 0 ≤ L e) (e : Fin ne) :
    RAM.ratBits (L e) ≤ 3 + (b + r) + 2*(d + learningRateBits*r) := by
  let Q' := Q * etaQ.den ^ min t r
  have hQ' : 0 < Q' := Nat.mul_pos hQ (pow_pos etaQ.den_pos _)
  have hm : |L e| ≤ (2 : ℚ) ^ (b + r) := by
    rw [abs_of_nonneg (hL e), pow_add, mul_comm]
    calc
      L e ≤ 2 ^ min t r * w e := h.upper e
      _ ≤ 2 ^ min t r * 2 ^ b := mul_le_mul_of_nonneg_left (hw e) (by positivity)
      _ ≤ 2 ^ r * 2 ^ b := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.min_le_right t r)) (by positivity)
  exact (dyadic_encoding_bounds _ Q' (b+r) (d+learningRateBits*r) hQ'
    (local_denominator_dyadic_bound Q d r t hcap) (h.den e) hm).2.2

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
