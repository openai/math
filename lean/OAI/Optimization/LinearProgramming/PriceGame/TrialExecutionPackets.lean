import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionTypes
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionWeights

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment Finset

variable {N ne r l : ℕ}

theorem incomingDeep_nonneg (experts : Fin ne → Expert N) (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    {j : ℕ} (xs : Fin j → Call N ne r l) (e : Fin ne) : 0 ≤ incomingDeep experts w xs e := by
  unfold incomingDeep deepWeightQ
  apply mul_nonneg _ (by positivity)
  unfold deepPartQ
  split <;> simp [hw e]

theorem incomingLocal_nonneg (experts : Fin ne → Expert N) (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    {j : ℕ} (xs : Fin j → Call N ne r l) (e : Fin ne) : 0 ≤ incomingLocal experts w xs e := by
  apply mul_nonneg
  · unfold localPartQ
    split <;> simp [hw e]
  · apply prod_nonneg
    intro t ht
    have hj := mem_range.mp ht
    have hb := (xs ⟨t,hj⟩).data.bounded e
    have hlo : -(1 : ℚ) ≤ (xs ⟨t,hj⟩).data.gain[e] := (abs_le.mp hb).1
    have he : 0 ≤ etaQ := by unfold etaQ sigmaQ; positivity
    have hle : etaQ ≤ 1 := by
      have hp : (1 : ℚ) ≤ 2 ^ 272 := one_le_pow₀ (by norm_num)
      have hs : sigmaQ ≤ 1 := (div_le_one (by positivity : (0:ℚ) < 2^272)).mpr hp
      unfold etaQ
      linarith
    simp only [probeAt, dite_eq_left hj, callGain]
    nlinarith [mul_nonneg he (show 0 ≤ (xs ⟨t,hj⟩).data.gain[e] + 1 by linarith)]

theorem market_mass_le (experts : Fin ne → Expert N) (history : History N) (w : Weights ne)
    (A : MarketAnswer experts l history w) (e : Fin ne) : ∑ i, A.fractions e (some i) ≤ 1 := by
  have h := A.balanced.unit e
  rw [Fintype.sum_option] at h
  linarith [A.balanced.nonneg e none]

theorem marketGain_abs_le (experts : Fin ne → Expert N) (history : History N) (w : Weights ne)
    (A : MarketAnswer experts l history w) (labels : Vertex N l → Bool) (e : Fin ne) :
    |gainQ (fun e i => A.fractions e (some i)) (sides experts) (fun i => labelSign (labels i)) e| ≤ 1 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simpa only [abs_mul, abs_of_nonneg (A.balanced.nonneg _ _), sides_abs, labelSign_abs, mul_one]
    using market_mass_le experts history w A e

def probeReturn (experts : Fin ne → Expert N) (w : Weights ne) (history : History N)
    {j : ℕ} (xs : Fin j → Call N ne r l)
    (hj : j < r) (A : MarketAnswer experts l history (incomingLocal experts w xs))
    (ch : Certified (N:=N) (r:=r) (l:=l+1) (incomingDeep experts w xs))
    (label : Vertex N l → Bool) : {c : Call N ne r l // StepOK experts w xs c} := by
  let allocation := fun e i => A.fractions e (some i)
  let gains := Vector.ofFn (gainQ allocation (sides experts) (fun i => labelSign (label i)))
  let data : RoundData N ne l := {
    baseline := A.prices
    mapped := States.parentPrices A.prices ch.val.prices
    childPrices := ch.val.prices
    alloc := allocation
    labels := label
    gain := gains
    market := some ⟨experts, history, incomingLocal experts w xs, A⟩
    represents := by
      intro S hS
      apply Option.some.inj at hS
      subst S
      exact ⟨rfl, rfl⟩
    bounded := by
      intro e
      simpa [gains, allocation] using
        marketGain_abs_le experts history (incomingLocal experts w xs) A label e }
  refine ⟨⟨data, ch.val⟩, ?_⟩
  exact {
    admissible := ch.property
    nonneg := fun e i => A.balanced.nonneg e (some i)
    mass := market_mass_le experts history (incomingLocal experts w xs) A
    gain_eq := by intro e; simp [data, gains]
    probeMarket := fun _ => ⟨⟨experts, history, incomingLocal experts w xs, A⟩, rfl, rfl, rfl⟩
    finalMarket := fun h => (Nat.not_le_of_lt hj h).elim
    clears := fun _ i => A.balanced.clears i }

def finalReturn (experts : Fin ne → Expert N) (w : Weights ne) {j : ℕ}
    (xs : Fin j → Call N ne r l) (hj : r ≤ j) (y : Prices N l)
    (ch : Certified (N:=N) (r:=r) (l:=l+1) (incomingDeep experts w xs)) :
    {c : Call N ne r l // StepOK experts w xs c} := by
  let data : RoundData N ne l := {
    baseline := y
    mapped := States.parentPrices y ch.val.prices
    childPrices := ch.val.prices
    alloc := fun _ _ => 0
    labels := fun _ => false
    gain := Vector.replicate ne 0
    market := none
    represents := by intro S h; cases h
    bounded := by intro e; simp }
  refine ⟨⟨data, ch.val⟩, ?_⟩
  exact {
    admissible := ch.property
    nonneg := fun _ _ => le_rfl
    mass := by intro e; simp [data]
    gain_eq := by intro e; simp [data, gainQ]
    probeMarket := fun h => (Nat.not_lt_of_ge hj h).elim
    finalMarket := fun _ => rfl
    clears := by intro _ i; simp [data] }

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
