import OAI.Optimization.LinearProgramming.PriceGame.TrialMarketDataBounds
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionStep
import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryGrid

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment Finset

variable {N ne r l : ℕ}

/-- A deeper expert is charged only by powers of two from completed child calls. -/
theorem incomingDeep_den_dvd (experts : Fin ne → Expert N) (w : Weights ne) (Q : ℕ)
    (hQ : ∀ e, (w e).den ∣ Q) {j : ℕ} (xs : Fin j → Call N ne r l) (e : Fin ne) :
    (incomingDeep experts w xs e).den ∣ Q := by
  have hden : (deepPartQ (mask experts l) w e).den ∣ Q := by
    unfold deepPartQ
    split <;> simp [hQ e]
  unfold incomingDeep deepWeightQ
  apply (Rat.mul_den_dvd _ _).trans
  let s := ∑ k ∈ range j, probeAt (fun i => callScore (xs i)) k e
  have hpow : ((2 : ℚ)^s).den = 1 := by
    have hcast : ((2 ^ s : ℕ) : ℚ) = (2 : ℚ) ^ s := by push_cast; rfl
    rw [← hcast]
    simp
  simpa only [← show s = ∑ k ∈ range j, probeAt (fun i => callScore (xs i)) k e from rfl,
    hpow, Nat.mul_one] using hden

theorem incomingLocal_snoc (experts : Fin ne → Expert N) (w : Weights ne)
    {j : ℕ} (xs : Fin j → Call N ne r l) (c : Call N ne r l) (e : Fin ne) :
    incomingLocal experts w (Fin.snoc xs c : Fin (j+1) → Call N ne r l) e =
      incomingLocal experts w xs e * (1 + etaQ * callGain c e) := by
  unfold incomingLocal
  rw [localWeightQ_succ]
  have hold := localWeightQ_congr_prefix etaQ (localPartQ (mask experts l) w)
    (g := probeAt (fun t => callGain ((Fin.snoc xs c : Fin (j+1) → Call N ne r l) t)))
    (g' := probeAt (fun t => callGain (xs t))) j e (by
      intro k hk
      simp only [probeAt, dite_eq_left hk, dite_eq_left (Nat.lt_succ_of_lt hk)]
      change callGain (Fin.snoc (α := fun _ : Fin (j+1) => Call N ne r l) xs c (Fin.castSucc (⟨k,hk⟩ : Fin j))) e = _
      rw [Fin.snoc_castSucc])
  have hlast : probeAt (fun t => callGain ((Fin.snoc xs c : Fin (j+1) → Call N ne r l) t)) j e =
      callGain c e := by
    simp only [probeAt, dite_eq_left (Nat.lt_succ_self _)]
    change callGain (Fin.snoc (α := fun _ : Fin (j+1) => Call N ne r l) xs c (Fin.last j)) e = _
    rw [Fin.snoc_last]
  rw [hold, hlast]

/-- The input weight grid is multiplied by just the learning-rate denominator per probe.
All final calls leave the local weights as they were. -/
structure LocalWeightBudget (Q r j : ℕ) (before after : Weights ne) : Prop where
  den : ∀ e, (after e).den ∣ Q * etaQ.den ^ min j r
  upper : ∀ e, after e ≤ (2 : ℚ) ^ min j r * before e

private theorem true_guarded {α : Type*} (p : Computation N α) :
    p.Guarded (fun _ => True) (fun _ => True) := by
  induction p with
  | pure => exact True.intro
  | ask q k ih => exact ⟨True.intro, ih⟩

private theorem probe_growth (v g : ℚ) (hv : 0 ≤ v) (hg : |g| ≤ 1) :
    v * (1 + etaQ * g) ≤ 2 * v := by
  have he : 0 ≤ etaQ := by unfold etaQ sigmaQ; positivity
  have hs : sigmaQ ≤ 1 := (div_le_one (by positivity : (0 : ℚ) < 2^272)).mpr
    (one_le_pow₀ (by norm_num))
  have hη : etaQ ≤ 1 := by unfold etaQ; linarith
  have hi := mul_le_mul_of_nonneg_left (abs_le.mp hg).2 he
  calc
    _ ≤ v * 2 := mul_le_mul_of_nonneg_left (by linarith) hv
    _ = _ := mul_comm _ _

private theorem step_localWeightBudget (experts : Fin ne → Expert N) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) (history : History N) (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (Q j : ℕ) (xs : Fin j → Call N ne r l)
    (h : LocalWeightBudget Q r j w (incomingLocal experts w xs)) :
    (executeStep experts (marketSolverAtCommonWeightUnit experts) w hw history path child j xs).Guarded
      (fun _ => True) (fun c => LocalWeightBudget Q r (j+1) w
        (incomingLocal experts w (Fin.snoc xs c.val : Fin (j+1) → Call N ne r l))) := by
  unfold executeStep
  dsimp only
  split
  · rename_i hj
    apply Computation.guarded_bind (true_guarded _)
    intro ch _
    apply Computation.guarded_map (true_guarded _)
    intro z _
    let L := incomingLocal experts w xs
    let A := marketSolverAtCommonWeightUnit experts l history L (incomingLocal_nonneg experts w hw xs)
    let c := probeReturn experts w history xs hj A ch z
    have hg (e : Fin ne) : callGain c.val e =
        gainQ (fun k i => A.fractions k (some i)) (sides experts) (fun i => labelSign (z i)) e := by
      simp [c, callGain, probeReturn]
    have hm : min (j+1) r = j+1 := Nat.min_eq_left (Nat.succ_le_of_lt hj)
    have hm0 : min j r = j := Nat.min_eq_left hj.le
    change LocalWeightBudget Q r (j+1) w (incomingLocal experts w (Fin.snoc xs c.val))
    constructor
    · intro e
      rw [incomingLocal_snoc, hm, hg e, pow_succ, ← Nat.mul_assoc]
      exact probeWeight_den_dvd experts history L (incomingLocal_nonneg experts w hw xs)
        etaQ z (Q * etaQ.den ^ j) (fun e => by simpa [L, hm0] using h.den e) e
    · intro e
      rw [incomingLocal_snoc, hm, pow_succ]
      have hv := incomingLocal_nonneg experts w hw xs e
      have hh := probe_growth (incomingLocal experts w xs e) (callGain c.val e) hv (c.val.data.bounded e)
      have hb := h.upper e
      rw [hm0] at hb
      linarith only [hh, mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℚ) ≤ 2),
        show (2 : ℚ) ^ j * 2 * w e = 2 * (2 ^ j * w e) by ring]
  · rename_i hj
    apply Computation.guarded_map (true_guarded _)
    intro ch _
    constructor <;> intro e <;> rw [incomingLocal_snoc]
    · simpa [callGain, finalReturn, Nat.min_eq_right (Nat.le_of_not_gt hj),
        Nat.min_eq_right (Nat.le_succ_of_le (Nat.le_of_not_gt hj))] using h.den e
    · simpa [callGain, finalReturn, Nat.min_eq_right (Nat.le_of_not_gt hj),
        Nat.min_eq_right (Nat.le_succ_of_le (Nat.le_of_not_gt hj))] using h.upper e

/-- Every prefix of an actual call schedule obeys the local weight bounds, even on
oracle branches with inconsistent replies. The child callback can be any computation. -/
theorem schedule_localWeightBudget (experts : Fin ne → Expert N) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) (history : History N) (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (Q : ℕ) (hQ : ∀ e, (w e).den ∣ Q) (n : ℕ) :
    (runSchedule (fun _ xs c => StepOK experts w xs c)
      (executeStep experts (marketSolverAtCommonWeightUnit experts) w hw history path child) n).Guarded
      (fun _ => True) (fun xs => ∀ t (ht : t ≤ n), LocalWeightBudget Q r t w
        (incomingLocal experts w (takePrefix xs.val t ht))) := by
  apply runSchedule_guarded_prefix _ _ _ _
    (fun j xs => ∀ t (ht : t ≤ j), LocalWeightBudget Q r t w
      (incomingLocal experts w (takePrefix xs.val t ht)))
  · intro t ht
    obtain rfl : t = 0 := by omega
    constructor <;> intro e <;> simp only [incomingLocal, localWeightQ_zero, Nat.zero_min,
      pow_zero, Nat.mul_one, one_mul, localPartQ]
    · split <;> simp [hQ e]
    · split <;> simp [hw e]
  · intro j _ xs IH
    have hp := IH j le_rfl
    have hsame : takePrefix xs.val j le_rfl = xs.val := rfl
    rw [hsame] at hp
    apply Computation.guarded_mono (step_localWeightBudget experts w hw history path child Q j xs.val hp)
      (fun _ h => h)
    intro x hx t ht
    by_cases heq : t = j + 1
    · subst t
      exact hx
    · have ht' : t ≤ j := by omega
      have hpre : takePrefix (snocSchedule _ xs x).val t ht = takePrefix xs.val t ht' := by
        funext k
        change Fin.snoc (α := fun _ : Fin (j+1) => Call N ne r l) xs.val x.val (Fin.castSucc (⟨k.val, k.isLt.trans_le ht'⟩ : Fin j)) = _
        rw [Fin.snoc_castSucc]
        rfl
      rw [hpre]
      exact IH t ht'

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
