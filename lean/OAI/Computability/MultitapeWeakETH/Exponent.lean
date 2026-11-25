import OAI.Computability.MultitapeWeakETH.Machine
import OAI.Computability.NearSquareRoot.Asymptotic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Exact full products and the infimum of achievable exponents -/

namespace OAI.Computability.MultitapeWeakETH

open IntegerMultiplication NearSquareRoot Filter

private theorem reverse_bit (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (bitValue w.reverse).testBit j = w[j] := by
  induction w generalizing j with
  | nil => simp at hj
  | cons b w ih =>
    have step : bitValue (b::w).reverse = Nat.bit b (bitValue w.reverse) := by
      cases b <;> simp [bitValue, List.foldl_append, Nat.bit_val]
    rw [step]
    cases j with
    | zero => simp
    | succ j => simpa only [Nat.testBit_bit_succ, List.getElem_cons_succ] using ih j (by simpa using hj)

theorem writes_low_of_full (M : Machine) {n : ℕ} (x y : Word n) (z : List Bool) (cfg : Config M)
    (offset : M.offset n = n) (whole : TM.whole M.blank (z.map M.bit) (cfg.tape M.output))
    (len : z.length = 2*n) (value : bitValue z = bitValue (List.ofFn x)*bitValue (List.ofFn y)) :
    writes M cfg (lowProduct x y) := by
  intro i
  have hj : n - 1 - i.val < z.reverse.length := by rw [List.length_reverse,len]; omega
  have bit := reverse_bit z.reverse (n-1-i.val) hj
  rw [List.reverse_reverse, List.getElem_reverse] at bit
  have idx : z.length - 1 - (n-1-i.val) = n+i.val := by rw [len]; omega
  have inRange : n+i.val < z.length := by rw [len]; omega
  change (cfg.tape M.output).absolute _ = M.bit ((bitValue (List.ofFn x) *
    bitValue (List.ofFn y)).testBit _)
  rw [← value, bit, offset, ← Nat.cast_add]
  rw [show (cfg.tape M.output).absolute = _ from whole]
  simp only [TM.Tape.absolute, TM.Tape.loaded, sub_zero, List.getElem?_map,
    List.getElem?_eq_getElem inRange, Option.map_some, Option.getD_some, idx]

/-- Exact halting runs for every positive width with a common worst-case clock.
The rule has no random choices and the physical I/O is that of NearRoot. -/
def ExactClock (W : ℕ → ℕ) : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (bit : Bool → A) (sep blank : A) (inp out : I) (start : Q) (rule : TM.Rule A Q I),
    Function.Injective bit ∧ (∀ b, bit b ≠ sep ∧ bit b ≠ blank) ∧ sep ≠ blank ∧
    ∀ n : ℕ, 0 < n → ∀ x y : Word n, ∃ t ≤ W n, ∃ cfg z,
      Trace (TM.advance rule) (initialConfig start inp bit sep blank (List.ofFn x) (List.ofFn y))
        t cfg ∧ TM.advance rule cfg = none ∧ TM.whole blank (z.map bit) (cfg.tape out) ∧
      z.length = 2*n ∧ bitValue z = bitValue (List.ofFn x)*bitValue (List.ofFn y)

private theorem iterate_of_trace {X : Type*} {step : X → Option X} {a z : X} {t : ℕ}
    (path : Trace step a t z) : (fun s : Option X => s.bind step)^[t] (some a) = some z := by
  induction path with
  | nil => rfl
  | cons h _ ih => rw [Nat.add_comm, Function.iterate_succ_apply]; simpa [h] using ih

theorem exact_clock_lower (main : MainStatement) {W : ℕ → ℕ} (machine : ExactClock W) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c * scale n ≤ W n := by
  classical
  obtain ⟨A,Q,I,fA,fQ,fI,bit,sep,blank,inp,out,start,rule,inj,marks,distinct,paths⟩ := machine
  let M : Machine := ⟨A,Q,I,Unit,bit,inj,sep,blank,marks,distinct,inp,out,Nat.cast,start,
    fun _ => rule,fun _ => true,none⟩
  obtain ⟨c,hc,N,lower⟩ := (main M).1
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  let law : CoinLaw M (W n) :=
    ⟨fun _ => 1,fun _ => zero_le_one,by change (∑ _ : Fin (W n+1) → Unit, (1:ℝ)) = 1; simp⟩
  apply lower n (by omega) (W n)
  refine ⟨law, ?_⟩
  have every (seed : Fin (W n+1) → M.Choice) (x y : Word n) :
      timely M (W n) seed x y (lowProduct x y) := by
    obtain ⟨t,ht,cfg,z,path,halt,whole,len,value⟩ := paths n (by omega) x y
    refine ⟨t,ht,cfg,?_,halt,rfl,writes_low_of_full M x y z cfg rfl whole len value⟩
    have run_it (k : ℕ) :
        run M (fun j => seed ⟨min j (W n),Nat.lt_succ_of_le (min_le_right ..)⟩) (initial M x y) k =
          (fun s : Option (Config M) => s.bind (TM.advance rule))^[k] (some (initial M x y)) := by
      induction k with
      | zero => rfl
      | succ k ih => rw [run, ih, Function.iterate_succ_apply']
    exact (run_it t).trans (iterate_of_trace path)
  have allSeeds (seed : Fin (W n+1) → M.Choice) : accurateDensity M n (W n) seed = 1 := by
    have good (x y : Word n) := every seed x y
    have event (x y : Word n) : ∃ z, timely M (W n) seed x y z ∧
        100 * errors z (lowProduct x y) ≤ n :=
      ⟨_, good x y, by simp [errors]⟩
    simp [accurateDensity, density, event]
  have one : success M n (W n) law = 1 := by simp only [success, allSeeds, mul_one, law.total]
  rw [one]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num))

def Achievable (r : ℝ) : Prop := ∃ W : ℕ → ℕ, ExactClock W ∧ ∃ C : ℝ, 0 < C ∧
  ∀ᶠ n in atTop, (W n : ℝ) ≤ C * n * logScale n ^ r

theorem achievable_above_half (upper : UniformMultiplicationSpec) {r : ℝ} (hr : 1/2 < r) :
    Achievable r := by
  obtain ⟨A,Q,I,fA,fQ,fI,bit,sep,blank,inp,out,start,rule,W,S,inj,marks,distinct,bound,paths⟩ := upper
  refine ⟨W,⟨A,Q,I,fA,fQ,fI,bit,sep,blank,inp,out,start,rule,inj,marks,distinct,?_⟩,?_⟩
  · intro n hn x y
    obtain ⟨t,cfg,z,path,halt,whole,len,value,ht,_⟩ :=
      paths n hn (List.ofFn x) (List.ofFn y) (List.length_ofFn ..) (List.length_ofFn ..)
    exact ⟨t,ht,cfg,z,path,halt,whole,len,value⟩
  · obtain ⟨C,hC,time⟩ := bound (r-1/2) (sub_pos.mpr hr)
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [add_sub_cancel_left, add_sub_cancel, logScale, add_sub_cancel_right,
      show (1:ℝ)/2 + (r-1/2) = r by ring] using time n hn

theorem optimal_exponent (main : MainStatement) (upper : UniformMultiplicationSpec) :
    IsGLB {r | Achievable r} (1/2 : ℝ) := by
  constructor
  · rintro r ⟨W,exactW,C,hC,time⟩
    by_contra! small
    obtain ⟨c,hc,lower⟩ := exact_clock_lower main exactW
    have powGrow := (tendsto_rpow_atTop (sub_pos.mpr small)).comp tendsto_logScale
    have logGrow := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    obtain ⟨n,lo,hi,big,logLarge,positive⟩ := (lower.and (time.and
      ((powGrow.eventually_gt_atTop (2*C/c)).and
        ((logGrow.eventually_ge_atTop 1).and (eventually_ge_atTop 1))))).exists
    have hn : (0:ℝ) < n := by exact_mod_cast positive
    change 1 ≤ Real.log n at logLarge
    have hscale : 0 < logScale n := by unfold logScale; linarith
    have cmp : logScale n ^ (1/2:ℝ) ≤ 2 * Real.sqrt (Real.logb 2 n) := by
      rw [← Real.sqrt_eq_rpow]
      have hlog : Real.log n ≤ Real.logb 2 n := by
        rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
        exact mul_le_of_le_one_right (by linarith) (le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num)))
      have base : logScale n ≤ 4 * Real.logb 2 n := by unfold logScale; linarith
      convert Real.sqrt_le_sqrt base using 1
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
        show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    have both : c * Real.sqrt (Real.logb 2 n) ≤ C * logScale n ^ r := by
      apply le_of_mul_le_mul_right (a := (n:ℝ))
      · unfold scale at lo
        nlinarith only [lo,hi]
      · exact hn
    change 2*C/c < logScale n ^ (1/2-r) at big
    rw [Real.rpow_sub hscale, div_lt_div_iff₀ hc (Real.rpow_pos_of_pos hscale r)] at big
    nlinarith only [both,big,mul_le_mul_of_nonneg_left cmp hc.le]
  · intro bound hbound
    by_contra! large
    obtain ⟨mid,hm,hm'⟩ := exists_between large
    exact (not_le.mpr hm') (hbound (achievable_above_half upper hm))

end OAI.Computability.MultitapeWeakETH
