import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignDriver
import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryTraces
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionComplexity
import OAI.Optimization.LinearProgramming.PriceGame.Complexity

/-! # Exact campaign transcripts on the outer/inner data-only program counter -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

open TrialExecution

set_option exponentiation.threshold 1024
set_option maxRecDepth 4096

variable {N : ℕ}

def commonMarkets (N : ℕ) : Campaign.AvailableMarkets N :=
  fun experts => TrialExecution.marketSolverAtCommonWeightUnit experts

def sourceCursor (R total left : ℕ) (a : Fin N) (p : Population N) (positive : ℕ) : CampaignCursor :=
  ⟨N,R,a.val,total,left,stateOf p positive⟩

theorem finish_sourceCursor (R T n : ℕ) (a : Fin N) (p : Population N)
    (positive : ℕ) (r : RoundResult N) :
    finishRound (sourceCursor R T (n+1) a p positive) (packRound p.experts.length r) =
    sourceCursor R T n a (p.advance (Learning.Pool.batch N R) r) (positive + vote a r) := by
  simp [finishRound,sourceCursor,acceptRound_eq]

theorem code_rootInput (R T n : ℕ) (a : Fin N) (p : Population N) (positive : ℕ) :
    rootInput (sourceCursor R T n a p positive) =
      Trial.codeInput 0 (N:=N) (fun _ _ => 0) (Campaign.populationWeights p) := by
  have weights : p.weights.toList = List.ofFn (Campaign.populationWeights p) := by
    apply List.ext_getElem <;> simp [Campaign.populationWeights]
  simp [rootInput,sourceCursor,stateOf,packPopulation,Trial.codeInput,packHistory,weights]

theorem packed_roster (p : Population N) :
    List.ofFn (fun e => packExpert (Campaign.populationExperts p e)) = (packPopulation p).experts := by
  apply List.ext_getElem <;> simp [packPopulation,Campaign.populationExperts]

theorem packed_resultOf (p : Population N)
    (o : Certified (N:=N) (r:=Moment.probes) (l:=0) (Campaign.populationWeights p)) :
    Trial.codeOutput o.val = packRound p.experts.length (Campaign.resultOf p o) := by
  have hprice : packTable N 0 o.val.prices = List.ofFn o.val.prices :=
    packTable_zero N o.val.prices
  have hscore (v : Vector ℕ p.experts.length) :
      v.toList = List.ofFn (fun i : Fin p.experts.length => Campaign.readScore v i.val) := by
    apply List.ext_getElem <;> simp [Campaign.readScore]
  change PackedRound.mk (packTable N 0 o.val.prices) o.val.scores.toList _ =
    PackedRound.mk (List.ofFn o.val.prices) (List.ofFn fun i : Fin p.experts.length => Campaign.readScore o.val.scores i.val) _
  rw [hprice,hscore]
  rfl

/-- This is the transcript contract of the actual recursive LCM-market compiler,
at a single root round; it makes no assumptions about the validity of the replies. -/
def RoundCompilation (N R : ℕ) : Prop :=
  ∀ (p : Population N) (tr : List (PackedQuery × Bool)) (out : RoundResult N),
    Trial.Emits (Campaign.runRound R (commonMarkets N) p) tr out →
    Trial.Evaluates (Trial.packetKernel feedbackPrefix N R Moment.probes (packPopulation p).experts)
      (2*Moment.probes) (.node (States.Mass.depth N)
        (Trial.codeInput 0 (N:=N) (fun _ _ => 0) (Campaign.populationWeights p)))
      tr (packRound p.experts.length out)

/-- The recursive compilation theorem is stated before the round's summary map.
Its actual root price and cached score order are preserved by the summary. -/
theorem roundCompilation_of_root (R : ℕ)
    (compiled : ∀ {ne : ℕ} (experts : Fin ne → Expert N) (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
      (tr : List (PackedQuery × Bool)) (out : Certified (N:=N) (r:=Moment.probes) (l:=0) w),
      Trial.Emits (TrialExecution.run R experts (marketSolverAtCommonWeightUnit experts) w hw) tr out →
      Trial.Evaluates (Trial.packetKernel feedbackPrefix N R Moment.probes (List.ofFn fun e => packExpert (experts e)))
        (2*Moment.probes) (.node (States.Mass.depth N) (Trial.codeInput 0 (N:=N) (fun _ _ => 0) w))
        tr (Trial.codeOutput out.val)) : RoundCompilation N R := by
  intro p tr out hr
  obtain ⟨receipt,run,rfl⟩ := hr.map_inv
  have h := compiled (Campaign.populationExperts p) (Campaign.populationWeights p) p.nonnegative tr receipt run
  rwa [packed_roster,packed_resultOf] at h

private theorem stream_branch (R T : ℕ) (compiled : RoundCompilation N R) (a : Fin N)
    (left : ℕ) (p : Population N) (positive : ℕ) {tr bit}
    (hr : Trial.Emits (stream (Learning.Pool.batch N R) (Campaign.runRound R (commonMarkets N)) a T left p positive) tr bit) :
    ∃ last, Complete (sourceCursor R T left a p positive) tr last ∧
      decide (last.total < 2*last.state.positiveVotes) = bit := by
  induction left generalizing p positive tr bit with
  | zero =>
    cases hr
    exact ⟨_,.finish _ rfl,rfl⟩
  | succ n ih =>
    rw [stream] at hr
    obtain ⟨before,round,after,rfl,hBefore,hAfter⟩ := hr.bind_inv
    obtain ⟨last,hLast,hBit⟩ := ih _ _ hAfter
    refine ⟨last,.round (c := sourceCursor R T (n+1) a p positive) (out := packRound p.experts.length round)
      (Nat.zero_lt_succ _) ?_ ?_,hBit⟩
    · rw [code_rootInput]
      exact compiled p before round hBefore
    · rwa [finish_sourceCursor]

theorem ofTree_toTree (p : Computation N Bool) : Computation.ofTree p.toTree = p := by
  induction p with
  | pure a => rfl
  | ask q next ih => simp [Computation.toTree,Computation.ofTree,ih]

/-- Every actual branch of the paper's adaptive campaign executes on the combined
first-order loop and stack with exactly the same designated queries in order and
the same final bit. The fixed-share update and learning history run on packed data. -/
theorem complete_of_strategy {R T : ℕ} (compiled : RoundCompilation N R) (a : Fin N) {tr bit}
    (hr : Trial.Emits (Computation.ofTree (Campaign.strategy R T a (commonMarkets N))) tr bit) :
    ∃ last, Complete (startCampaign N R a.val T) tr last ∧
      decide (last.total < 2*last.state.positiveVotes) = bit := by
  rw [← stream_eq_strategy, ofTree_toTree] at hr
  obtain ⟨last,complete,finished⟩ := stream_branch R T compiled a _ _ _ hr
  have eq : startCampaign N R a.val T = sourceCursor R T T a (.start (Learning.Pool.batch N R)) 0 := by
    unfold sourceCursor
    exact congrArg (fun st => CampaignCursor.mk N R a.val T T st) (startCampaign_state N R a.val T)
  exact ⟨last,eq ▸ complete,finished⟩

theorem exact_control_steps {R T : ℕ} (compiled : RoundCompilation N R) (a : Fin N) {tr bit}
    (hr : Trial.Emits (Computation.ofTree (Campaign.strategy R T a (commonMarkets N))) tr bit) :
    ∃ last, Steps (.campaign (startCampaign N R a.val T)) tr
        (T*(Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + 2)+tr.length) (.campaign last) ∧
      step (.campaign last) = .halt bit := by
  obtain ⟨last,run,done⟩ := complete_of_strategy compiled a hr
  exact ⟨last,run.steps,done ▸ run.final⟩


/-- Public cap on high-level controller transitions before a source branch terminates.
The per-round term counts the explicit trial stack, the two outer transitions, and
the actual query bound. Numeric packet construction has its own bit-cost estimates. -/
def controlClock (N T : ℕ) : ℕ :=
  T * (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + 2) +
    T * TrialExecution.queryBound N Moment.probes (States.Mass.depth N) 0 + 1

private theorem nodeTicks_le_nodeCount (b d : ℕ) :
    Trial.nodeTicks b d + 3 ≤ 5 * Complexity.nodeCount b d := by
  induction d with
  | zero => simp [Trial.nodeTicks, Complexity.nodeCount]
  | succ d ih =>
    calc
      _ = 5 + b * (Trial.nodeTicks b d + 3) := by rw [Trial.nodeTicks]; omega
      _ ≤ 5 + b * (5 * Complexity.nodeCount b d) := Nat.add_le_add_left (Nat.mul_le_mul_left b ih) _
      _ = 5 * Complexity.nodeCount b (d+1) := by rw [Complexity.nodeCount]; ring

/-- The controller clock is a polynomial in the trial count and dimension and does
not inspect the adaptive computation or its unseen branches. -/
theorem controlClock_polynomial (T N : ℕ) (hN : 0 < N) :
    controlClock N T ≤ T * (5*(2*N)^602 + (2*(N+1))^605) + 1 := by
  have hn := nodeTicks_le_nodeCount (2*Moment.probes) (States.Mass.depth N)
  have hcount : Complexity.nodeCount (2*Moment.probes) (States.Mass.depth N) ≤ (2*N)^602 :=
    Complexity.trial_nodes_le N hN
  have hs := hn.trans (Nat.mul_le_mul_left 5 hcount)
  have hroot : Trial.nodeTicks (2*Moment.probes) (States.Mass.depth N) + 2 ≤ 5*(2*N)^602 := by omega
  unfold controlClock
  calc
    _ ≤ T*(5*(2*N)^602) + T*(2*(N+1))^605 + 1 :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left T hroot)
        (Nat.mul_le_mul_left T (TrialExecution.queryBound_polynomial N))) 1
    _ = _ := by rw [Nat.mul_add T (5*(2*N)^602) ((2*(N+1))^605)]

theorem emits_length_public {α : Type*} {p : Computation N α} {tr a} (e : Trial.Emits p tr a) :
    tr.length ≤ p.height := by
  induction e with
  | pure => exact Nat.zero_le _
  | @ask q k tr a b run ih =>
    apply Nat.succ_le_succ
    cases b
    · exact ih.trans (Nat.le_max_left ..)
    · exact ih.trans (Nat.le_max_right ..)

theorem poll_some_mono {n m : ℕ} {p : PC} {event : Boundary} (found : poll n p = some event)
    (budget : n ≤ m) : poll m p = some event := by
  induction n generalizing m p with
  | zero => cases found
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases hs : step p with
      | proceed next =>
        simp only [poll, hs] at found ⊢
        exact ih found (by omega)
      | ask q f t => simpa only [poll, hs] using found
      | halt b => simpa only [poll, hs] using found

/-- The public dimension clock suffices for a data-only dispatch on every actual
source branch. The resulting observable is exactly its first price query, or its
true final answer when that source branch asks no questions. -/
theorem first_boundary_with_clock {R T : ℕ} (compiled : RoundCompilation N R) (a : Fin N)
    {tr bit} (hr : Trial.Emits (Computation.ofTree (Campaign.strategy R T a (commonMarkets N))) tr bit) :
    ∃ event, poll (controlClock N T) (.campaign (startCampaign N R a.val T)) = some event ∧
      visibleFirst tr bit event := by
  obtain ⟨last,hsteps,done⟩ := exact_control_steps compiled a hr
  obtain ⟨event,found,visible⟩ := hsteps.first_boundary done
  refine ⟨event,poll_some_mono found ?_,visible⟩
  have hq : tr.length ≤ T * TrialExecution.queryBound N Moment.probes (States.Mass.depth N) 0 := by
    apply (emits_length_public hr).trans
    rw [← Computation.height_toTree, Computation.toTree_ofTree]
    exact Campaign.strategy_height ..
  exact Nat.succ_le_succ (Nat.add_le_add_left hq _)

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
