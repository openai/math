import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionSchedule
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionTypes
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionWeights

/-! Assembly of one internal price-game node from the actual sequential schedule
of probes and final calls. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment Finset

variable {N ne r l : ℕ}

def probeIndex (i : Fin r) : Fin (2 * r) := ⟨i.val, by omega⟩
def finalIndex (i : Fin r) : Fin (2 * r) := ⟨r + i.val, by omega⟩

abbrev NodeRun (experts : Fin ne → Expert N) (w : Weights ne) (r l : ℕ) :=
  Schedule (fun j xs c => @StepOK N ne r l j experts w xs c) (2 * r)

def scheduleGain (xs : Fin (2 * r) → Call N ne r l) (j : Fin r) :
    Fin ne → ℚ := callGain (xs (probeIndex j))

def scheduleChildren (xs : Fin (2 * r) → Call N ne r l) (j : Fin (2 * r)) :
    Trial (Fin ne) r := (xs j).child.trace

def nodeTrace (experts : Fin ne → Expert N) (xs : Fin (2 * r) → Call N ne r l) :
    Trial (Fin ne) r := .node (mask experts l) (scheduleGain xs) (scheduleChildren xs)

/-- Compute each integer once from the numeric gains and the children's cached integers. -/
def nodeScores (experts : Fin ne → Expert N) (xs : Fin (2 * r) → Call N ne r l) : Vector ℕ ne :=
  Vector.ofFn fun e => if mask experts l e then
    rationalScore scaleQ sigmaQ (meanQ r fun i => probeAt (scheduleGain xs) i e)
  else rationalScore scaleQ sigmaQ
    (meanQ (2 * r) fun i => (probeAt (fun j => callScore (xs j)) i e : ℕ))

theorem nodeScores_eq (experts : Fin ne → Expert N) (xs : Fin (2 * r) → Call N ne r l)
    (e : Fin ne) : (nodeScores experts xs)[e] = (nodeTrace experts xs).score scaleQ sigmaQ e := by
  have hc : (fun j => callScore (xs j)) =
      (fun j => (scheduleChildren xs j).score scaleQ sigmaQ) :=
    funext fun j => funext fun a => (xs j).child.scores_eq a
  simp [nodeScores, nodeTrace, Trial.score, hc]

/-- Replaying the first group up to this call uses exactly its incoming local weights. -/
theorem incomingLocal_schedule (experts : Fin ne → Expert N) (w : Weights ne)
    (xs : Fin (2 * r) → Call N ne r l) (j : Fin r) (e : Fin ne) :
    incomingLocal experts w («prefix» xs (probeIndex j)) e =
      localWeightQ etaQ (localPartQ (mask experts l) w) (probeAt (scheduleGain xs)) j e := by
  apply localWeightQ_congr_prefix
  intro i hi
  change i < j.val at hi
  simp [probeAt, «prefix», probeIndex, scheduleGain, hi, hi.trans j.isLt]

/-- Both groups pass the weights produced by all preceding child scores in the same node. -/
theorem incomingDeep_schedule (experts : Fin ne → Expert N) (w : Weights ne)
    (xs : Fin (2 * r) → Call N ne r l) (j : Fin (2 * r)) (e : Fin ne) :
    incomingDeep experts w («prefix» xs j) e =
      deepWeightQ (deepPartQ (mask experts l) w)
        (childScoreAt scaleQ sigmaQ (scheduleChildren xs)) j e := by
  apply deepWeightQ_congr_prefix
  intro i hi
  have hfull : i < 2 * r := hi.trans j.isLt
  simpa [probeAt, «prefix», callScore, childScoreAt, scheduleChildren, hi, hfull] using
    (xs ⟨i, hfull⟩).child.scores_eq e

theorem nodeTrace_admissible (experts : Fin ne → Expert N) (w : Weights ne)
    (run : NodeRun experts w r l) :
    (nodeTrace experts run.val).Admissible scaleQ sigmaQ eta (fun e => (w e : ℝ)) := by
  rw [← etaQ_cast]
  apply Trial.node_admissible_of_rational_market scaleQ sigmaQ etaQ (mask experts l) w
    (scheduleGain run.val) (scheduleChildren run.val)
    (fun j => (run.val (probeIndex j)).data.alloc) (sides experts)
    (fun j i => labelSign ((run.val (probeIndex j)).data.labels i))
  · exact sides_abs experts
  · intro j i; exact labelSign_abs _
  · intro j e i; exact (run.property (probeIndex j)).nonneg e i
  · intro j e; exact (run.property (probeIndex j)).mass e
  · intro j e; exact (run.property (probeIndex j)).gain_eq e
  · intro j i
    simpa only [incomingLocal_schedule] using (run.property (probeIndex j)).clears j.isLt i
  · intro j
    simpa only [scheduleChildren, etaQ_cast, incomingDeep_schedule] using (run.property j).admissible

def nodeLog (history : History N) (xs : Fin (2 * r) → Call N ne r l) : List (Probe N) :=
  (List.ofFn fun j : Fin (2 * r) =>
    if j.val < r then ⟨l, (xs j).data.baseline, history⟩ :: (xs j).child.log
    else (xs j).child.log).flatten


theorem probe_mem_nodeLog (history : History N) (xs : Fin (2 * r) → Call N ne r l)
    (j : Fin r) : ⟨l, (xs (probeIndex j)).data.baseline, history⟩ ∈ nodeLog history xs := by
  unfold nodeLog
  apply List.mem_flatten_of_mem (List.mem_ofFn.mpr ⟨probeIndex j, rfl⟩)
  simp [probeIndex, j.isLt]

theorem childLog_subset_nodeLog (history : History N) (xs : Fin (2 * r) → Call N ne r l)
    (j : Fin (2 * r)) {p : Probe N} (hp : p ∈ (xs j).child.log) : p ∈ nodeLog history xs := by
  unfold nodeLog
  apply List.mem_flatten_of_mem (List.mem_ofFn.mpr ⟨j, rfl⟩)
  split
  · exact List.mem_cons_of_mem _ hp
  · exact hp

/-- Complete an internal node. Only final-call mapped prices are candidates for its
returned median; the history contains all probes at this node and its descendants. -/
def assemble (experts : Fin ne → Expert N) (history : History N) (w : Weights ne)
    (run : NodeRun experts w r l) : Certified (N := N) (r := r) (l := l) w :=
  ⟨{ prices := fun i => median fun j : Fin r => (run.val (finalIndex j)).data.mapped i
     trace := nodeTrace experts run.val
     receipt := .node l (fun j => (run.val j).data) (fun j => (run.val j).child.receipt)
     scores := nodeScores experts run.val
     scores_eq := nodeScores_eq experts run.val
     log := nodeLog history run.val }, nodeTrace_admissible experts w run⟩

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
