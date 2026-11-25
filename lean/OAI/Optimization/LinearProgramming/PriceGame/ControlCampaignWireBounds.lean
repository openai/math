import OAI.Optimization.LinearProgramming.PriceGame.TrialWireBound
import OAI.Optimization.LinearProgramming.PriceGame.TrialLogDepth
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingPopulation
import OAI.Optimization.LinearProgramming.PriceGame.ControlSession

/-! Uniform bounds for all prices and all earlier price rows in an adaptive campaign. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

universe u

namespace Computation

theorem Guarded.andOutputs {N : ℕ} {A : Type u} {Q : Query N → Prop} {P S : A → Prop}
    {p : Computation N A} (hp : p.Guarded Q P) (hs : AllOutputs S p) :
    p.Guarded Q (fun x => P x ∧ S x) := by
  induction hs with
  | pure hx => exact ⟨hp, hx⟩
  | ask hs ih => exact ⟨hp.1, fun b => ih b (hp.2 b)⟩

end Computation

namespace Control.Wire

open Learning Campaign States.Mass TrialExecution

attribute [local irreducible] Moment.probes runRound runReference run execute

def campaignPriceBits (N R T : ℕ) : ℕ :=
  trialPriceBits N (expertCount N R T) R Bits.commonDenominator

/-- Everything needed to charge the complete probe record, including each earlier row. -/
def RoundFits {N : ℕ} (B : ℕ) (o : RoundResult N) : Prop :=
  (∀ i, RAM.ratBits (o.prices i) ≤ B) ∧
    ∀ p ∈ o.observations, ProbeBits B p ∧ p.level < depth N

private def HasPrefix {N : ℕ} (R k : ℕ) (p : Population N) : Prop :=
  ∃ old : ℕ → RoundResult N, p = population R old k ∧
    ∀ i < k, (old i).observations.length ≤ Pool.probeBudget N

theorem population_congr {N : ℕ} (R : ℕ) {old new : ℕ → RoundResult N}
    (k : ℕ) (agree : ∀ i < k, old i = new i) : population R old k = population R new k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (population R old k).advance _ (old k) = (population R new k).advance _ (new k)
    rw [ih (fun i hi => agree i (by omega)), agree k (by omega)]

private theorem extendPrefix {N R k : ℕ} {p : Population N} (hp : HasPrefix R k p)
    (o : RoundResult N) (ho : o.observations.length ≤ Pool.probeBudget N) :
    HasPrefix R (k+1) (p.advance (Pool.batch N R) o) := by
  obtain ⟨past,rfl,hp⟩ := hp
  let next := Function.update past k o
  have eqOld (i) (hi : i < k) : past i = next i :=
    (Function.update_of_ne (by omega : i ≠ k) o past).symm
  have eqNew : next k = o := Function.update_self ..
  refine ⟨next, ?_, ?_⟩
  · change (population R past k).advance _ o = (population R next k).advance _ (next k)
    rw [population_congr R k eqOld, eqNew]
  · intro i hi
    by_cases h : i = k
    · subst i; simpa only [eqNew] using ho
    · rw [← eqOld i (by omega)]
      exact hp i (by omega)

private abbrev markets (N : ℕ) : AvailableMarkets N :=
  fun es => marketSolverAtCommonWeightUnit es

private theorem oneRoundGuarded {N : ℕ} (a : Fin N) (R T k : ℕ) (hk : k ≤ T)
    (p : Population N) (prior : HasPrefix R k p) :
    (runRound R (markets N) p).Guarded (PricesBounded (campaignPriceBits N R T))
      (fun o => RoundFits (campaignPriceBits N R T) o ∧ PublicRoundBounds p o) := by
  obtain ⟨past,eqPast,hpast⟩ := prior
  have hcount : p.experts.length ≤ expertCount N R T := by
    rw [eqPast]
    refine (population_length_of_observations a R k past hpast k le_rfl).trans ?_
    unfold expertCount
    gcongr
  have hraw : RawBox Bits.commonDenominator R (populationExperts p) := by
    intro e i _
    apply Pool.catalogue_entry_grid (hist := seenProbes past) (T := k+1)
    rw [← population_entries, ← eqPast]
    exact List.getElem_mem ..
  have hb := runReference_bits_guarded a.pos hcount Bits.commonDenominator R
    Bits.commonDenominator_pos (populationExperts p) hraw (populationWeights p) p.nonnegative
  have hd := runReference_log_depth R (populationExperts p) (populationWeights p) p.nonnegative
  have project : runRound R (markets N) p =
      (runReference R (populationExperts p) (populationWeights p) p.nonnegative).map (resultOf p) := by
    unfold runRound runReference
    rfl
  apply Computation.Guarded.andOutputs (S := PublicRoundBounds p)
  · rw [project]
    apply Computation.guarded_map (hb.andOutputs hd)
    intro o ho
    exact ⟨ho.1.1, fun pr hpr => ⟨ho.1.2 pr hpr, ho.2 pr hpr⟩⟩
  · exact runRound_all_public_bounds a R _ p

/-- One actual public history prefix suffices to certify every branch of the next round. -/
theorem oneRound_prices_with_history {N : ℕ} (a : Fin N) (R T : ℕ) (old : ℕ → RoundResult N)
    (k : ℕ) (hk : k ≤ T) (hs : ∀ j < k, (old j).observations.length ≤ Pool.probeBudget N) :
    let p := population R old k
    (runRound R (fun es => marketSolverAtCommonWeightUnit es) p).Guarded
      (PricesBounded (campaignPriceBits N R T))
      (fun o => RoundFits (campaignPriceBits N R T) o ∧ PublicRoundBounds p o) :=
  oneRoundGuarded a R T k hk _ ⟨old,rfl,hs⟩

private theorem loopGuardedFrom {N : ℕ} (a : Fin N) (R T n k : ℕ) (hk : k+n ≤ T)
    (p : Population N) (prior : HasPrefix R k p) :
    (trialLoop (Pool.batch N R) (runRound R (markets N)) n p).Guarded
      (PricesBounded (campaignPriceBits N R T))
      (fun xs => ∀ j : Fin n, RoundFits (campaignPriceBits N R T) (xs j)) := by
  induction n generalizing k p with
  | zero => exact fun j => j.elim0
  | succ n ih =>
    rw [trialLoop]
    apply Computation.guarded_bind (oneRoundGuarded a R T k (by omega) p prior)
    intro o ho
    apply Computation.guarded_map (ih (k+1) (by omega) _ (extendPrefix prior o ho.2.observations))
    intro xs hx j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact ho.1
    · exact hx i

/-- All queries, all returned root prices, and all complete probe histories satisfy one public
bit cap on both branches of every actual query. -/
theorem campaignLoop_guarded {N : ℕ} (a : Fin N) (R T : ℕ) :
    (trialLoop (Pool.batch N R) (runRound R (fun es => marketSolverAtCommonWeightUnit es)) T
      (Population.start (Pool.batch N R))).Guarded (PricesBounded (campaignPriceBits N R T))
      (fun xs => ∀ j : Fin T, RoundFits (campaignPriceBits N R T) (xs j)) := by
  apply loopGuardedFrom a R T T 0 (by omega)
  exact ⟨fun _ => ⟨fun _ => 0, fun _ => 0, []⟩, rfl, fun _ h => by omega⟩

private theorem of_to_tree {N : ℕ} (p : Computation N Bool) : Computation.ofTree p.toTree = p := by
  induction p with
  | pure => rfl
  | ask q next ih =>
    change Computation.ask q (fun b => Computation.ofTree (next b).toTree) = Computation.ask q next
    rw [show (fun b => Computation.ofTree (next b).toTree) = next from funext ih]

/-- The same cap follows the native public solver through both tree conversions and majority. -/
theorem campaignSolver_all_prices (trials : ℕ → ℕ → ℕ) (i : PublicInput) :
    (campaignSolver trials i).AllQueries
      (PricesBounded (campaignPriceBits i.goods i.range (trials i.goods i.range))) := by
  unfold campaignSolver Campaign.strategy trialStrategy
  rw [of_to_tree]
  exact Computation.allQueries_map _ (campaignLoop_guarded i.anchor i.range _).allQueries _

end Control.Wire

end PriceGame
end LinearProgramming
end Optimization
end OAI
