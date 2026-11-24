import OAI.Computability.VPVNP.LiveProgram
import OAI.Computability.VPVNP.LiveEvaluatorRAMSegmentCost
import OAI.Computability.VPVNP.LiveStageLinkPaths

/-!
# Cost of the evaluator stages in the linked live program

Starting at the first-tail router, the native trace initializes the evaluator
or gathers its incoming configuration, then prepares or gathers its outgoing
configuration and runs one transition. The bounds include framed operand
loads, the dispatcher tag read, and the transfer write. Header preparation
and the earlier live-mode router are outside this interval.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorTailCost

open LiveProgram BurstRAM

variable {w : ℕ}

/-- Raw prefix bit length, row width and row count are taken before choosing
the transcript capacity. The order-advice row has `clog 2 t` bits. -/
structure Parameters where
  /-- The advice prefix size used to bound the number of native packing calls. -/
  advice : ℕ
  /-- The number of exponent rows whose label ordinals and digits are prepared for the
  evaluator. -/
  rows : ℕ
  /-- The number of binary exponent digits per row. -/
  rowWidth : ℕ
  /-- The radius on either side of the head in each finite evaluator tape window. -/
  radius : ℕ
  /-- The number of bits packed into a native advice word. -/
  wordWidth : ℕ

/-- Total number of exponent digits across all label rows. -/
def Parameters.exponentBits (u : Parameters) := u.rows*u.rowWidth
/-- Length of the serialized runtime skeleton, including exponent payloads, width fields, and
delimiters. -/
def Parameters.runtimeBits (u : Parameters) := 2*u.exponentBits+6*u.rowWidth+4
/-- Number of words needed for the control state and both full radius-bounded tape windows. -/
def Parameters.configWords (u : Parameters) := 4*u.radius+3
/-- The linked cost allowance for one instruction-preparation call and the two windows'
cell-check calls. -/
def Parameters.transitionCost (u : Parameters) := 10+14*(2*u.radius+1)

/-- Number of cursors used to pack the length word, including its initial clear. -/
def Parameters.lengthPackCalls (u : Parameters) := u.wordWidth+1
/-- A call bound for packing the advice prefix into rounded-up word rows, including the
empty-prefix case. -/
def Parameters.prefixPackCalls (u : Parameters) :=
  max 1 (((u.advice+u.wordWidth-1)/u.wordWidth)*(u.wordWidth+1))
/-- A call bound for packing one binary ordinal per label, including each row's initial clear
and the empty-table case. -/
def Parameters.orderPackCalls (u : Parameters) := max 1 (u.rows*(Nat.clog 2 u.rows+1))

/-- The component stages that run between mode dispatch and termination. -/
def tailStages (first last empty : Bool) : List Stage :=
  [Stage.firstTail] ++
  (if first then [Stage.initialState] ++
    (if empty then [] else [Stage.prefixLength, Stage.adviceFrames, Stage.prefixPack, Stage.orderPack,
      Stage.prefixCopy, Stage.skeleton, Stage.scatter])
   else [Stage.oldGather]) ++ [Stage.last] ++
  (if last then [Stage.finalState] else [Stage.newGather]) ++ [Stage.transition]

/-- The linked cost of all the tail stages following mode dispatch. -/
def groupBound (u : Parameters) (first last empty : Bool) : ℕ :=
  let pack := 6*u.lengthPackCalls + 23 + 11*u.prefixPackCalls + 6*u.orderPackCalls
  let init := 4 + pack + 10*(max 1 u.advice) + 8*u.runtimeBits + 11*(max 1 u.exponentBits)
  let gather := (u.wordWidth+4)*u.configWords
  8 + u.transitionCost + 2*u.configWords +
    (if first then (if empty then 4 else init) else gather) + (if last then 4 else gather)

/-- The first component is the number of calls. The second is the cost
including probes but before operand loading and stage dispatch. -/
def rawBudget (u : Parameters) (s : Stage) : ℕ × ℕ :=
  match s.val with
  | 7 | 17 => (1, 3)
  | 8 | 18 => (1, 2)
  | 9 => (u.lengthPackCalls, 4*u.lengthPackCalls)
  | 10 => (1, 21)
  | 11 => (u.prefixPackCalls, 4*u.prefixPackCalls)
  | 12 => (u.orderPackCalls, 4*u.orderPackCalls)
  | 13 => (max 1 u.advice, 3*max 1 u.advice)
  | 14 => (u.runtimeBits, 2*u.runtimeBits)
  | 15 => (max 1 u.exponentBits, 4*max 1 u.exponentBits)
  | 16 | 19 => (u.configWords, (u.wordWidth+2)*u.configWords)
  | 20 => (u.configWords, u.transitionCost)
  | _ => (0, 0)

/-- Exactly the prefix pack, prefix copy, skeleton and scatter use operand
frames among these stages, with the arities of the tables in `LiveProgram.rows`. -/
def frameReads (s : Stage) : ℕ :=
  match s.val with
  | 11 | 13 | 15 => 5
  | 14 => 4
  | _ => 0

private def dispatchProbes (s : Stage) : ℕ := if s = Stage.firstTail ∨ s = Stage.last then 1 else 2

/-- Apply the two native report transformations at a stage boundary.
Each report retains the memory at its call entry for the frame read values. -/
def linked (p : UniversalMachine.Program) (tag frame : Word w) (s : Stage) (x : Memory w × Report w) : Report w :=
  LiveStageLink.linkedReport (next p) tag s (LiveStageLink.prependLog
    (CompressorRecords.Frame.loadEvents frame x.1 0 (frameReads s)) x.2)

private theorem linked_probes_le (p : UniversalMachine.Program) (tag frame : Word w) (s : Stage)
    (x : Memory w × Report w) :
    (linked p tag frame s x).probes ≤ x.2.probes + frameReads s + dispatchProbes s := by
  rw [linked, LiveStageLink.linkedReport_probes, (CompressorRecords.Frame.frame_cost ..).2.1]
  unfold dispatchProbes
  by_cases hr : s = Stage.firstTail ∨ s = Stage.last
  · rcases hr with rfl | rfl <;> simp [next, Stage.firstTail, Stage.last] <;> omega
  · rw [ite_eq_right hr]
    split <;> omega

theorem linked_stage_cost (p : UniversalMachine.Program) (tag frame : Word w) (s : Stage)
    (calls : List (Memory w × Report w)) :
    RAMBuckets.cost Report.probes (calls.map (linked p tag frame s)) ≤
      RAMBuckets.cost Report.probes (calls.map Prod.snd) + (frameReads s+dispatchProbes s)*calls.length := by
  induction calls with
  | nil => simp [RAMBuckets.cost]
  | cons x xs ih =>
    simp only [List.map_cons, List.length_cons, RAMBuckets.cost, Nat.mul_succ]
    have := linked_probes_le p tag frame s x
    omega

/-- Per-stage facts furnished by the component execution theorems. -/
def Bounded (u : Parameters) (s : Stage) (calls : List (Memory w × Report w)) : Prop :=
  calls.length ≤ (rawBudget u s).1 ∧ RAMBuckets.cost Report.probes (calls.map Prod.snd) ≤ (rawBudget u s).2

private def stageBudget (u : Parameters) (s : Stage) :=
  (rawBudget u s).2 + (frameReads s + dispatchProbes s)*(rawBudget u s).1

private theorem cost_list (p : UniversalMachine.Program) (u : Parameters) (tag : Word w)
    (frame : Stage → Word w) (calls : Stage → List (Memory w × Report w)) (ss : List Stage)
    (bounds : ∀ s ∈ ss, Bounded u s (calls s)) :
    RAMBuckets.cost Report.probes (ss.flatMap fun s => (calls s).map (linked p tag (frame s) s)) ≤
      (ss.map (stageBudget u)).sum := by
  induction ss with
  | nil => simp [RAMBuckets.cost]
  | cons s ss ih =>
    rw [List.flatMap_cons, RAMBuckets.cost_append, List.map_cons, List.sum_cons]
    apply Nat.add_le_add _ (ih fun i hi => bounds i (List.mem_cons_of_mem _ hi))
    obtain ⟨hl, hc⟩ := bounds s (List.mem_cons_self ..)
    exact (linked_stage_cost ..).trans (Nat.add_le_add hc (Nat.mul_le_mul_left _ hl))

private theorem budget_sum (u : Parameters) (first last empty : Bool) :
    ((tailStages first last empty).map (stageBudget u)).sum = groupBound u first last empty := by
  cases first <;> cases last <;> cases empty <;>
    simp [tailStages, stageBudget, groupBound, rawBudget, frameReads, dispatchProbes,
      Stage.firstTail, Stage.last, Stage.initialState, Stage.finalState, Stage.prefixLength, Stage.adviceFrames,
      Stage.prefixPack, Stage.orderPack, Stage.prefixCopy, Stage.skeleton, Stage.scatter,
      Stage.oldGather, Stage.newGather, Stage.transition] <;> ring

/-- A single symbolic RAM-cost bound for a first, interior, last, or sole
tail group. The hypothesis concerns its component traces. The conclusion
charges the framed reports and the real dispatcher/transfer reports. -/
theorem tail_group_cost (p : UniversalMachine.Program) (u : Parameters) (first last : Bool)
    (tag : Word w) (frame : Stage → Word w) (calls : Stage → List (Memory w × Report w))
    (bounds : ∀ s ∈ tailStages first last (decide (p.extra = 0)), Bounded u s (calls s)) :
    RAMBuckets.cost Report.probes ((tailStages first last (decide (p.extra = 0))).flatMap
      fun s => (calls s).map (linked p tag (frame s) s)) ≤ groupBound u first last (decide (p.extra = 0)) :=
  (cost_list p u tag frame calls _ bounds).trans_eq (budget_sum ..)

end LiveEvaluatorTailCost

end VPVNP
end Computability
end OAI
