import OAI.Optimization.LinearProgramming.PriceGame.FixedShareActualBounds
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionComplexity

/-! Public size invariants of the whole campaign on arbitrary adaptive answers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

open Finset

/-- All-output invariant for replaying the actual sequence of trial calls. The
extension beyond the end of the finite output is arbitrary. -/
theorem trialLoop_all_replay_steps {N : ℕ} (candidates : List (Probe N) → List (Expert N))
    (trial : Population N → Computation N (RoundResult N))
    (P : Population N → RoundResult N → Prop) (hp : ∀ p, Computation.AllOutputs (P p) (trial p))
    (T : ℕ) (p : Population N) :
    Computation.AllOutputs (fun xs => ∀ out : ℕ → RoundResult N,
      (∀ i : Fin T, out i.val = xs i) → ∀ k < T, P (replay candidates p out k) (out k))
      (trialLoop candidates trial T p) := by
  induction T generalizing p with
  | zero => exact .pure (by intro _ _ k hk; omega)
  | succ T ih =>
    rw [trialLoop]
    apply (hp p).bind
    intro first hfirst
    apply (ih (p.advance candidates first)).map
    intro tail htail out hout k hk
    have hz : out 0 = first := by simpa using hout (0 : Fin (T+1))
    cases k with
    | zero => simpa [replay, hz] using hfirst
    | succ k =>
      rw [replay_succ_first, hz]
      apply htail (fun j => out (j+1)) _ k (by omega)
      intro i
      simpa using hout i.succ

namespace Campaign
open Learning

/-- Query count of the full adaptive outer driver. Work performed inside market
clearings and on the generated catalogue is accounted for separately. -/
theorem strategy_height_explicit {N : ℕ} (R T : ℕ) (anchor : Fin N) (markets : AvailableMarkets N) :
    (strategy R T anchor markets).height ≤ T * (2*(N+1))^605 :=
  (strategy_height ..).trans (Nat.mul_le_mul_left T (TrialExecution.queryBound_polynomial N))

/-- The moment and log bounds used in sizing an outer update. Both concern public output data. -/
structure PublicRoundBounds {N : ℕ} (p : Population N) (o : RoundResult N) : Prop where
  moment : (∑ j ∈ p.ids, (p.weight j : ℝ) * (2 : ℝ) ^ o.scores j) ≤
    (2 : ℝ)^Moment.tau * ∑ j ∈ p.ids, (p.weight j : ℝ)
  observations : o.observations.length ≤ Pool.probeBudget N

theorem runRound_all_public_bounds {N : ℕ} (anchor : Fin N) (R : ℕ)
    (markets : AvailableMarkets N) (p : Population N) :
    Computation.AllOutputs (PublicRoundBounds p) (runRound R markets p) := by
  have hlog : Computation.AllOutputs
      (fun o : TrialExecution.Certified (N:=N) (r:=Moment.probes) (l:=0) (populationWeights p) =>
        o.val.log.length ≤ TrialExecution.probeLogBound Moment.probes (States.Mass.depth N))
      (TrialExecution.run R (populationExperts p) (markets _) (populationWeights p) p.nonnegative) := by
    unfold TrialExecution.run
    exact TrialExecution.execute_log_length Moment.probes R (populationExperts p) (markets _)
      (States.Mass.depth N) 0 .root (fun _ _ => 0) (populationWeights p) p.nonnegative
  unfold runRound
  apply hlog.map (resultOf p)
  intro o ho
  refine ⟨?_, ho.trans (TrialExecution.probeLogBound_le_probeBudget N (Nat.zero_lt_of_lt anchor.isLt))⟩
  rw [Population.ids, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simpa [resultOf, readScore, Population.weight, Population.lookup, populationWeights]
    using! TrialExecution.cached_moment (populationWeights p) p.nonnegative o

/-- Every actual trial produced from a public starting state satisfies the two
resource invariants, even when the answers disagree with every hidden instance. -/
theorem all_replay_bounds {N : ℕ} (anchor : Fin N) (R T : ℕ) (markets : AvailableMarkets N) :
    Computation.AllOutputs (fun xs => ∀ out : ℕ → RoundResult N,
      (∀ i : Fin T, out i.val = xs i) →
      ∀ k < T, PublicRoundBounds (population R out k) (out k))
      (trialLoop (Pool.batch N R) (runRound R markets) T (Population.start (Pool.batch N R))) :=
  trialLoop_all_replay_steps _ _ _ (runRound_all_public_bounds anchor R markets) _ _

/-- Catalogue size including the post-trial state. No expert ranking or hidden
instance enters the estimate. -/
theorem population_length_of_observations {N : ℕ} (anchor : Fin N) (R T : ℕ)
    (out : ℕ → RoundResult N) (hobs : ∀ k < T, (out k).observations.length ≤ Pool.probeBudget N)
    (t : ℕ) (ht : t ≤ T) :
    (population R out t).experts.length ≤ ((N + R.size + 1) * (T+1)) ^ Pool.catalogueExponent := by
  have hseen (i : ℕ) (hi : i ≤ T) : (seenProbes out i).length ≤ i * Pool.probeBudget N := by
    induction i with
    | zero => simp [seenProbes]
    | succ i ih => simpa [seenProbes, Nat.succ_mul] using
        Nat.add_le_add (ih (by omega)) (hobs i (by omega))
  rw [population_entries]
  apply (Catalog.length_mono (fun i => Pool.batch N R (seenProbes out i)) (Nat.succ_le_succ ht)).trans
  have hN : 0 < N := Nat.zero_lt_of_lt anchor.isLt
  apply Pool.catalogue_size_power N R _ _ hN (by omega) (by omega) (Nat.succ_pos T)
  intro i hi
  exact (hseen i (by omega)).trans (Nat.mul_le_mul_right _ hi.le)

/-- A uniform bit cap for catalogue counts, including the list made by the last update. -/
def catalogueBits (N R T : ℕ) : ℕ :=
  ((N + R.size + 1).size + (T+1).size) * Pool.catalogueExponent

private theorem product_pow_le_binary (a b k : ℕ) : (a*b)^k ≤ 2^((a.size+b.size)*k) := by
  calc
    _ ≤ ((2 ^ a.size) * (2 ^ b.size))^k := Nat.pow_le_pow_left
      (Nat.mul_le_mul (Nat.lt_size_self a).le (Nat.lt_size_self b).le) k
    _ = _ := by rw [← pow_add, ← pow_mul]

theorem population_length_le_pow_two {N : ℕ} (anchor : Fin N) (R T : ℕ)
    (out : ℕ → RoundResult N) (hobs : ∀ k < T, (out k).observations.length ≤ Pool.probeBudget N)
    (t : ℕ) (ht : t ≤ T) : (population R out t).experts.length ≤ 2 ^ catalogueBits N R T := by
  exact (population_length_of_observations anchor R T out hobs t ht).trans
    (product_pow_le_binary (N+R.size+1) (T+1) Pool.catalogueExponent)

/-- The outer-state inputs for the bound on every market call in an executed trial. -/
theorem population_guard_of_round_bounds {N : ℕ} (anchor : Fin N) (R T : ℕ) (out : ℕ → RoundResult N)
    (hs : ∀ k < T, PublicRoundBounds (population R out k) (out k))
    (t : ℕ) (ht : t ≤ T) (i : Fin (population R out t).experts.length) :
    let b := catalogueBits N R T
    let q := populationWeights (population R out t) i
    let D := populationDenominator R out t
    0 < D ∧ D ≤ 2^(b+(6+b)*t) ∧ q.den ∣ D ∧ 0 ≤ q ∧ q ≤ (2 : ℚ)^t ∧
      q.den ≤ 2^(b+(6+b)*t) ∧ q.num.natAbs ≤ 2^(t+b+(6+b)*t) := by
  let b := catalogueBits N R T
  let D := populationDenominator R out t
  let q := populationWeights (population R out t) i
  have hD : 0 < D := populationDenominator_pos anchor R out t
  have hcap := population_length_le_pow_two anchor R T out (fun k hk => (hs k hk).observations) t ht
  have hDb : D ≤ 2^(b+(6+b)*t) := populationDenominator_le R out t b hcap
  have hd : q.den ∣ D := population_weight_den_dvd R out t i
  have hnn : 0 ≤ q := (population R out t).nonnegative i
  have hq : q ≤ (2:ℚ)^t := (population_weight_le_sum R out t i).trans
    (population_total_le_of_moments anchor R out t (fun k hk => (hs k (hk.trans_le ht)).moment))
  have hq' : |q| ≤ ((2^t : ℕ) : ℚ) := by rw [abs_of_nonneg hnn]; exact_mod_cast hq
  have hnum := Moment.rat_num_abs_le_of_den_dvd q (2^t) D hD hq' hd
  refine ⟨hD,hDb,hd,hnn,hq,(Nat.le_of_dvd hD hd).trans hDb,hnum.trans ?_⟩
  rw [Nat.add_assoc, pow_add]
  exact Nat.mul_le_mul_left _ hDb

/-- The guard on a stored weight of the original campaign executed with arbitrary
history-dependent replies. The extension `out` can hold any values after trial `T`. -/
theorem run_population_guard {N : ℕ} (anchor : Fin N) (R T : ℕ) (markets : AvailableMarkets N)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool))
    (out : ℕ → RoundResult N) (hx : ∀ j : Fin T, out j.val =
      ((trialLoop (Pool.batch N R) (runRound R markets) T (Population.start (Pool.batch N R))).run reply history) j)
    (t : ℕ) (ht : t ≤ T) (i : Fin (population R out t).experts.length) :
    let b := catalogueBits N R T
    let q := populationWeights (population R out t) i
    let D := populationDenominator R out t
    0 < D ∧ D ≤ 2^(b+(6+b)*t) ∧ q.den ∣ D ∧ 0 ≤ q ∧ q ≤ (2 : ℚ)^t ∧
      q.den ≤ 2^(b+(6+b)*t) ∧ q.num.natAbs ≤ 2^(t+b+(6+b)*t) :=
  population_guard_of_round_bounds anchor R T out
    ((all_replay_bounds anchor R T markets).run reply history out hx) t ht i

end Campaign
end PriceGame
end LinearProgramming
end Optimization
end OAI
