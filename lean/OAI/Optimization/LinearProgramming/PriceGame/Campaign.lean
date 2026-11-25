import OAI.Optimization.LinearProgramming.PriceGame.Schedule
import OAI.Optimization.LinearProgramming.PriceGame.LearningPool
import OAI.Optimization.LinearProgramming.PriceGame.FixedShareScore
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecution

/-! The price-recovery campaign. The expert pool, all price calls, scores, weights and
votes below are computed from the public input and the label transcript. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Campaign

open Finset States.Mass Learning

def anchorSkeleton {N : ℕ} (a : Fin N) (positive : Bool) : Skeleton N :=
  ⟨⟨0, Nat.zero_lt_succ _⟩, positive, (fun _ => a), none⟩

/-- The transformed costs used in the analysis. Values at inactive indices never constrain a reply. -/
def priorityInt {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor) (i : Fin N) : ℤ :=
  (R : ℤ) + 1 - (h.cost i : ℕ)

theorem priority_box {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor) (i : Fin N) :
    1 ≤ priorityInt h i ∧ priorityInt h i ≤ (R : ℤ) + 1 := by
  have hi := (h.cost i).isLt
  dsimp [priorityInt]
  omega

theorem batch_ne_nil {N : ℕ} (R : ℕ) (anchor : Fin N) (ps : List (Probe N)) :
    Pool.batch N R ps ≠ [] :=
  List.ne_nil_of_mem (Pool.selected_mem_batch R (anchorSkeleton anchor true) ps (fun _ => 1)
    (fun _ => ⟨le_rfl, by omega⟩))

abbrev population {N : ℕ} (R : ℕ) (out : ℕ → RoundResult N) (t : ℕ) :=
  replay (Pool.batch N R) (Population.start (Pool.batch N R)) out t

theorem population_entries {N : ℕ} (R : ℕ) (out : ℕ → RoundResult N) (t : ℕ) :
    (population R out t).experts = Catalog.entries (fun u => Pool.batch N R (seenProbes out u)) (t+1) := by
  rw [replay_entries]
  induction t with
  | zero => simp [expectedEntries, Catalog.entries, seenProbes]
  | succ t ih => simp only [expectedEntries, Catalog.entries, ih]

theorem population_nonempty {N : ℕ} (anchor : Fin N) (R : ℕ) (out : ℕ → RoundResult N) (t : ℕ) :
    (population R out t).ids.Nonempty := by
  suffices h : 0 < (population R out t).experts.length from ⟨0, mem_range.mpr h⟩
  rw [population_entries, Catalog.entries, List.length_append]
  have hm := List.length_pos_iff.mpr (batch_ne_nil R anchor (seenProbes out t))
  omega

abbrev AvailableMarkets (N : ℕ) :=
  ∀ {ne : ℕ} (experts : Fin ne → Expert N), TrialExecution.MarketSolver experts

def populationExperts {N : ℕ} (p : Population N) (i : Fin p.experts.length) : Expert N :=
  p.experts[i]

def populationWeights {N : ℕ} (p : Population N) (i : Fin p.experts.length) : ℚ :=
  p.weights[i]

def readScore {n : ℕ} (v : Vector ℕ n) (j : ℕ) : ℕ :=
  if h : j < n then v[j] else 0

def resultOf {N : ℕ} (p : Population N)
    (o : TrialExecution.Certified (N:=N) (r:=Moment.probes) (l:=0) (populationWeights p)) :
    RoundResult N :=
  ⟨o.val.prices, readScore o.val.scores, o.val.log⟩

/-- A real call to the recursive trial with the current pool in stable ID order. -/
def runRound {N : ℕ} (R : ℕ) (markets : AvailableMarkets N) (p : Population N) :
    Computation N (RoundResult N) :=
  (TrialExecution.run R (populationExperts p) (markets (populationExperts p))
    (populationWeights p) p.nonnegative).map (resultOf p)

theorem round_height {N : ℕ} (R : ℕ) (markets : AvailableMarkets N) (p : Population N) :
    (runRound R markets p).height ≤ TrialExecution.queryBound N Moment.probes (depth N) 0 := by
  simpa [runRound] using TrialExecution.run_height_le R (populationExperts p)
    (markets (populationExperts p)) (populationWeights p) p.nonnegative

theorem round_moment {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (markets : AvailableMarkets N) (p : Population N) (out : RoundResult N)
    (hr : Computation.Reaches h (runRound R markets p) out) :
    (∑ i ∈ p.ids, (p.weight i : ℝ) * 2 ^ out.scores i) ≤
      (2 : ℝ) ^ Moment.tau * ∑ i ∈ p.ids, (p.weight i : ℝ) := by
  obtain ⟨o, _, rfl⟩ := (Computation.reaches_map_iff ..).mp hr
  rw [Population.ids, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simpa [resultOf, readScore, Population.weight, Population.lookup, populationWeights]
    using! TrialExecution.cached_moment (populationWeights p) p.nonnegative o

/-- The explicit recursive price strategy. All free subprocedures here are public market clearings. -/
def strategy {N : ℕ} (R T : ℕ) (anchor : Fin N) (markets : AvailableMarkets N) : Tree N :=
  trialStrategy (Pool.batch N R) (runRound R markets) T anchor

/-- Run the binary-scaling transshipment using the least common denominator of the current weights. -/
def referenceStrategy {N : ℕ} (R T : ℕ) (anchor : Fin N) : Tree N :=
  strategy R T anchor (fun xs => TrialExecution.marketSolverAtCommonWeightUnit xs)

theorem strategy_height {N : ℕ} (R T : ℕ) (anchor : Fin N) (markets : AvailableMarkets N) :
    (strategy R T anchor markets).height ≤ T * TrialExecution.queryBound N Moment.probes (depth N) 0 :=
  trialStrategy_height _ _ _ _ (round_height R markets) _

theorem score_budget {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (markets : AvailableMarkets N) (out : ℕ → RoundResult N) (T a n M e : ℕ)
    (hr : ValidRun (Pool.batch N R) (runRound R markets) h T
      (Population.start (Pool.batch N R)) (fun i => out i.val))
    (ht : a + n ≤ T) (he : e ∈ (population R out a).ids)
    (hM : (population R out a).ids.card ≤ M) :
    ∑ i ∈ range n, ((out (a+i)).scores e : ℝ) ≤
      (1/8 : ℝ) * n + Real.logb 2 (64 * (M : ℝ)) := by
  let lists := fun k => (population R out k).ids
  let scores := fun k => (out k).scores
  have hmom (i : ℕ) (hi : i < n) :
      ∑ j ∈ lists (a+i), (rootWeights lists scores (a+i) j : ℝ) * 2 ^ scores (a+i) j ≤
      (2 : ℝ) ^ Moment.tau * (rootTotal lists scores (a+i) : ℝ) := by
    have hr' := (validRun_iff_steps ..).mp hr (a+i) (by omega)
    have hh := round_moment h markets (population R out (a+i)) (out (a+i)) hr'
    have hw : (population R out (a+i)).weight = rootWeights lists scores (a+i) :=
      replay_weight_eq ..
    unfold rootTotal
    rw [← hw]
    push_cast
    exact hh
  have hb := rootWeights_interval_score_bound lists scores a n M e
    (fun k _ => population_nonempty anchor R out k) (fun k _ => replay_ids_grow _ _ _ k)
    he hM hmom
  have hτ : Moment.tau = 1 / (2 : ℝ)^275 := by
    unfold Moment.tau Moment.sigma
    rw [div_div, show 275 = 272 + 3 by decide, pow_add, show (2 : ℝ)^(3:ℕ)=8 by norm_num]
  have hγ : Moment.tau + Real.logb 2 (1 / (1 - (1 / 64 : ℝ))) ≤ 1/8 := by
    rw [hτ]
    exact source_gamma_bound.le
  rw [show (M:ℝ) / (1/64 : ℝ) = 64 * M by ring] at hb
  exact hb.trans (add_le_add (mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg n)) le_rfl)

/-- Failure of the actual root prices for the hidden data. -/
def failedTrial {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor) (out : RoundResult N) : Bool :=
  decide (∃ i ∈ h.active, h.signedPrice (out.prices i) < (R + 1 : ℚ) - (h.cost i : ℕ))

theorem succeeds_of_not_failed {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (out : RoundResult N) (hf : failedTrial h out = false) (i : Fin N) (hi : i ∈ h.active) :
    (R + 1 : ℚ) - (h.cost i : ℕ) ≤ h.signedPrice (out.prices i) := by
  by_contra! hh
  have h' : failedTrial h out = true := by
    unfold failedTrial
    exact decide_eq_true ⟨i, hi, hh⟩
  simp_all

/-- The score budget for the actual execution bounds failures on a contiguous good interval.
The expert distribution is indexed by skeleton, so it can retain multiplicities in the
catalogue without changing weights between two trials of the same interval. -/
theorem charged_segment_bound {I : Type*} [Fintype I] {N R : ℕ} {anchor : Fin N}
    (h : Hidden N R anchor) (markets : AvailableMarkets N) (out : ℕ → RoundResult N) (T a n M : ℕ)
    (hr : ValidRun (Pool.batch N R) (runRound R markets) h T
      (Population.start (Pool.batch N R)) (fun i => out i.val))
    (ht : a + n ≤ T) (hM : (population R out a).ids.card ≤ M)
    (id : I → ℕ) (present : ∀ s, id s ∈ (population R out a).ids)
    (weight : I → ℚ) (nonnegative : ∀ s, 0 ≤ weight s) (mass_le : ∑ s, weight s ≤ 1)
    (charge : ∀ j < n, failedTrial h (out (a+j)) = true →
      1 ≤ ∑ s, weight s * ((out (a+j)).scores (id s) : ℚ)) :
    ∑ j ∈ range n, (if failedTrial h (out (a+j)) then (1 : ℝ) else 0) ≤
      (1/8 : ℝ) * n + Real.logb 2 (64 * (M : ℝ)) := by
  have hm : (1 : ℝ) ≤ M := by
    exact_mod_cast (show 1 ≤ M from (population_nonempty anchor R out a).card_pos.trans_le hM)
  have hb : 0 ≤ (1/8 : ℝ) * n + Real.logb 2 (64 * (M : ℝ)) := by
    apply add_nonneg (by positivity) (Real.logb_nonneg (by norm_num) (by nlinarith))
  apply charged_interval_bound (range n) (univ : Finset I)
    (fun j => failedTrial h (out (a+j)))
    (fun j s => ((out (a+j)).scores (id s) : ℝ)) (fun s => (weight s : ℝ)) hb
    (fun s _ => Rat.cast_nonneg.mpr (nonnegative s))
  · exact_mod_cast mass_le
  · intro j hj
    cases hh : failedTrial h (out (a+j)) with
    | false =>
      simpa using (sum_nonneg (s:=univ) fun (s : I) _ =>
        mul_nonneg (Rat.cast_nonneg.mpr (nonnegative s) : (0:ℝ) ≤ weight s)
          (Nat.cast_nonneg ((out (a+j)).scores (id s)) : (0:ℝ) ≤ _))
    | true =>
      simpa using (show (1 : ℝ) ≤ ∑ s, (weight s : ℝ) * ((out (a+j)).scores (id s) : ℝ) by
        exact_mod_cast charge j (mem_range.mp hj) hh)
  · intro e _
    exact score_budget h markets out T a n M (id e) hr ht (present e) hM

end Campaign
end PriceGame
end LinearProgramming
end Optimization
end OAI
