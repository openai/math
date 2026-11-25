import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryTraces
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionSize
import OAI.Optimization.LinearProgramming.PriceGame.Campaign

/-! # The outer score guard accepts every physically emitted trial

The estimate holds along both branches of every label request, including transcripts
that are inconsistent with every hidden instance.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

variable {N : ℕ} {α : Type*}

/-- A particular finite oracle transcript inherits any guarantee proved on every
branch of the underlying computation. -/
theorem Emits.of_allOutputs {p : Computation N α} {tr a} {P : α → Prop}
    (emits : Emits p tr a) (all : Computation.AllOutputs P p) : P a := by
  induction emits with
  | pure a => cases all with | pure ha => exact ha
  | ask b _ ih => cases all with | ask hs => exact ih (hs b)

/-- Any score in the actual serialized output lies within the fixed public cap. Reading
past the recorded end returns zero under the packed control convention. -/
theorem runRound_packed_score_le (R : ℕ) (markets : Campaign.AvailableMarkets N) (p : Population N)
    (hn : 0 < N) {tr : List (PackedQuery × Bool)} {round : RoundResult N}
    (emits : Emits (Campaign.runRound R markets p) tr round) (i : ℕ) :
    (packRound p.experts.length round).scores[i]?.getD 0 ≤ (2*N)^274 := by
  unfold Campaign.runRound at emits
  obtain ⟨out,he,rfl⟩ := emits.map_inv
  have all := TrialExecution.execute_all_trace_height Moment.probes R (Campaign.populationExperts p)
    (markets (Campaign.populationExperts p)) (States.Mass.depth N) 0 .root (fun _ _ => 0)
    (Campaign.populationWeights p) p.nonnegative
  have hheight : out.val.trace.height ≤ States.Mass.depth N := he.of_allOutputs all
  by_cases hi : i < p.experts.length
  · let j : Fin p.experts.length := ⟨i,hi⟩
    have hs := TrialExecution.certified_score_le_public (Campaign.populationWeights p) out hn
      (by simpa only [States.Mass.depth,Nat.log2_eq_log_two] using hheight) j
    simpa [packRound,Campaign.resultOf,Campaign.readScore,List.getElem?_ofFn,hi,j] using hs
  · simp [packRound,hi]

/-- Reachable outer cursor weights and emitted score arrays satisfy the clipping guard. -/
theorem runRound_scoreGuard (R : ℕ) (markets : Campaign.AvailableMarkets N) (p : Population N)
    (hn : 0 < N) {tr : List (PackedQuery × Bool)} {round : RoundResult N}
    (emits : Emits (Campaign.runRound R markets p) tr round) :
    ∀ i < (packPopulation p).weights.length,
      (packRound p.experts.length round).scores[i]?.getD 0 ≤ (2*N)^274 :=
  fun i _ => runRound_packed_score_le R markets p hn emits i

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
