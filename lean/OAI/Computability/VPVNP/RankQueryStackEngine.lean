import OAI.Computability.VPVNP.RankQueryStackFrames

/-!
# Return control for the physical determinant stack

The finite control dispatches a query, scans its summands and returns each
operand to the suspended parent. The result of a terminal descriptor and a
finished sum both enter the same return instruction. An empty direction history
signals that the root coefficient is ready. A nonempty history is restored
before the frame reader consumes the saved fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine

open RAMTape

/-- Live and historical frame registers, the result, one condition bit and the
scratch or persistent ports of the installed scalar and dispatch routines. -/
inductive Port (K : Type) where
  | frame (p : FrameStore.Port) | result | condition | aux (k : K)
  deriving DecidableEq, Fintype

/-- Each of the external calls returns normally and supplies its data on the
named ports. Describe emits a true condition for a scalar, scan for a completed
sum. Left and right children are placed in pending registers before the active
frame is pushed. -/
structure Actions (K : Type) where
  /-- Inspect the active query and initialize its scan or signal a scalar result. -/
  describe : FiniteRoutine (Port K)
  /-- Advance the sum scan, signaling completion or preparing the next left child. -/
  scan : FiniteRoutine (Port K)
  /-- Move a pending child query into the live frame after saving its parent. -/
  activate : FiniteRoutine (Port K)
  /-- Prepare the right child after the left factor's value returns. -/
  right : FiniteRoutine (Port K)
  /-- Add the product of the returned factors to the parent accumulator. -/
  multiplyAdd : FiniteRoutine (Port K)

/-- Subroutine calls of the stack evaluator, including frame saves and restores. -/
inductive Call where
  | describe | scan | save | restore | activate | right | multiplyAdd
  deriving DecidableEq

instance : Fintype Call := derive_fintype% _

variable {K : Type}

/-- Select the installed evaluator action or built-in frame routine for a call tag. -/
def Actions.callee (a : Actions K) : Call → FiniteRoutine (Port K)
  | .describe => a.describe
  | .scan => a.scan
  | .save => FrameStore.push.onPorts Port.frame
  | .restore => FrameStore.pop.onPorts Port.frame
  | .activate => a.activate
  | .right => a.right
  | .multiplyAdd => a.multiplyAdd

/-- Controller states for inspecting subroutine results, restoring the frame direction and
rejecting invalid signals. -/
inductive Admin where
  | described | scanned | returned | restoreTag (b : Bool) | direction | reject
  deriving DecidableEq, Fintype

/-- Physical engine state, either a controller state or a program counter inside an identified
subroutine. -/
abbrev State (a : Actions K) := Admin ⊕ ((i : Call) × (a.callee i).State)

/-- Enter the specified subroutine at its initial program counter. -/
def invoke (a : Actions K) (i : Call) : State a := .inr ⟨i, (a.callee i).body.entry⟩

private def after (a : Actions K) : Call → State a
  | .describe => .inl .described
  | .scan => .inl .scanned
  | .save => invoke a .activate
  | .restore => .inl .direction
  | .activate => invoke a .describe
  | .right => invoke a .save
  | .multiplyAdd => invoke a .scan

/-- Execute the installed evaluator actions and frame routines under the call-and-return
controller. -/
def routine (a : Actions K) : Routine (Port K) (State a) where
  entry := invoke a .describe
  code
    | .inr ⟨i, q⟩ => (a.callee i).body.install (fun j => .inr ⟨i,j⟩) (some (after a i)) q
    | .inl .described => .pop .condition (fun b => some (b.elim (.inl .reject) fun terminal =>
        if terminal then .inl .returned else invoke a .scan))
    | .inl .scanned => .pop .condition (fun b => some (b.elim (.inl .reject) fun finished =>
        if finished then .inl .returned else invoke a .save))
    | .inl .returned => .pop (.frame (.inr 0)) fun b => b.map (fun d => .inl (.restoreTag d))
    | .inl (.restoreTag b) => .push (.frame (.inr 0)) b (some (invoke a .restore))
    | .inl .direction => .pop (.frame (.inl 0)) (fun b => some (b.elim (.inl .reject) fun right =>
        if right then invoke a .multiplyAdd else invoke a .right))
    | .inl .reject => .halt false

/-- The outer program is finite as soon as its component programs are finite. -/
def machine (a : Actions K) : FiniteRoutine (Port K) := .ofRoutine (routine a)

variable [DecidableEq K]

theorem call_runs (a : Actions K) (i : Call) {t : ℕ} {s out : Stacks (Port K)}
    (h : (a.callee i).Runs t s out) :
    StackRuns (routine a).standalone t (some (invoke a i)) s (some (after a i)) out :=
  h.link (routine a) (fun j => .inr ⟨i,j⟩) _ (fun _ => rfl)

theorem described_step (a : Actions K) (s : Stacks (Port K)) (b : Bool) (hs : s .condition = [b]) :
    StackRuns (routine a).standalone 1 (some (.inl .described)) s
      (some (if b then .inl .returned else invoke a .scan)) (Function.update s .condition []) := by
  refine .cons (.pop rfl) ?_
  simp only [hs, List.head?_cons, List.tail_cons, Option.elim_some]
  exact .nil ..

theorem scanned_step (a : Actions K) (s : Stacks (Port K)) (b : Bool) (hs : s .condition = [b]) :
    StackRuns (routine a).standalone 1 (some (.inl .scanned)) s
      (some (if b then .inl .returned else invoke a .save)) (Function.update s .condition []) := by
  refine .cons (.pop rfl) ?_
  simp only [hs, List.head?_cons, List.tail_cons, Option.elim_some]
  exact .nil ..

/-- Test the direction history without changing the bit at its top. -/
theorem return_to_frame (a : Actions K) (s : Stacks (Port K)) (b : Bool) (tail : List Bool)
    (hs : s (.frame (.inr 0)) = b :: tail) :
    StackRuns (routine a).standalone 2 (some (.inl .returned)) s (some (invoke a .restore)) s := by
  refine .cons (.pop rfl) ?_
  simp only [hs, List.head?_cons, List.tail_cons, Option.map_some]
  refine .cons (.push rfl) ?_
  simp only [Function.update_self, Function.update_idem, ← hs, Function.update_eq_self]
  exact .nil ..

/-- The empty continuation stack returns the computed root scalar to the caller. -/
theorem return_to_caller (a : Actions K) (s : Stacks (Port K)) (hs : s (.frame (.inr 0)) = []) :
    StackRuns (routine a).standalone 1 (some (.inl .returned)) s none s := by
  refine .cons (.pop rfl) ?_
  simp only [hs, List.head?_nil, List.tail_nil, Option.map_none]
  rw [← hs, Function.update_eq_self]
  exact .nil ..

theorem direction_step (a : Actions K) (s : Stacks (Port K)) (b : Bool) (hs : s (.frame (.inl 0)) = [b]) :
    StackRuns (routine a).standalone 1 (some (.inl .direction)) s
      (some (if b then invoke a .multiplyAdd else invoke a .right))
      (Function.update s (.frame (.inl 0)) []) := by
  refine .cons (.pop rfl) ?_
  simp only [hs, List.head?_cons, List.tail_cons, Option.elim_some]
  exact .nil ..

end RankQuery.Stack.Engine

end VPVNP
end Computability
end OAI
