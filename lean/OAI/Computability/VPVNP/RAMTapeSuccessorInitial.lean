import OAI.Computability.VPVNP.RAMTapeWordOperands
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-!
# The public initial state at the first processor

After checking the incoming zero clamp, the first processor needs the public
initial word in its state register and a running flag. The word-copy scan
overwrites the destination while restoring the public word. The next two
instructions replace the top status bit and preserve the tail of that stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorInitial

open TapeWord

/-- Ports for copying the public initial word into the incoming state register and setting its
running bit. -/
inductive Port where
  | initial | state | running | sourceTmp | outTmp
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

private def copyPorts : ScanPort → Port
  | .left => .initial
  | .right => .sourceTmp
  | .tmp => .outTmp
  | .out => .state

private theorem copyPorts_injective : Function.Injective copyPorts := by
  intro i j h
  cases i <;> cases j <;> simp_all [copyPorts]

private def normal : Operand.State Unit → Bool
  | .done _ => true
  | _ => false

variable {K : Type}

private def copy (ports : Port → K) : FiniteRoutine K :=
  FiniteRoutine.ofStackCode (Operand.code Operand.copyBit) (ports ∘ copyPorts) (.clear ()) normal

private theorem copy_runs [DecidableEq K] {ports : Port → K} (hp : Function.Injective ports)
    (s : Stacks K) (hs : s (ports .sourceTmp) = []) (ho : s (ports .outTmp) = []) :
    (copy ports).Runs ((s (ports .state)).length + 7*(s (ports .initial)).length + 3) s
      (Function.update s (ports .state) (s (ports .initial))) := by
  refine FiniteRoutine.runs_ofStackCode_framed (hp.comp copyPorts_injective) (normal := normal)
    rfl rfl (fun q h => ?_) (Operand.copy_run _ _) ?_ ?_ ?_
  · cases q <;> first | rfl | contradiction
  · intro k
    cases k <;> first | rfl | exact hs | exact ho
  · intro k
    cases k <;> simp [copyPorts, scanStacks, Function.update, hp.eq_iff, hs, ho]
  · intro j hj
    exact Function.update_of_ne (Ne.symm (hj .out)) ..

private def setRunning (port : K) : FiniteRoutine K := FiniteRoutine.ofRoutine {
  entry := false
  code
    | false => .pop port fun _ => some true
    | true => .push port true none }

private theorem setRunning_runs [DecidableEq K] (port : K) (s : Stacks K) :
    (setRunning port).Runs 2 s (Function.update s port (true :: (s port).tail)) := by
  refine .cons (.pop rfl) (.cons (.push rfl) ?_)
  simp only [Function.update_self, Function.update_idem]
  exact .nil ..

/-- At an absent incoming edge, install the initial running configuration. -/
def normalize (ports : Port → K) : FiniteRoutine K :=
  (copy ports).followedBy (setRunning (ports .running))

/-- With two empty scratch stacks, normalization takes eight instructions per
word bit plus five fixed instructions, regardless of the old state and flag. -/
theorem normalize_runs [DecidableEq K] {ports : Port → K} (hp : Function.Injective ports)
    (s : Stacks K) {w : ℕ} (hs : s (ports .sourceTmp) = []) (ho : s (ports .outTmp) = [])
    (hi : (s (ports .initial)).length = w) (hd : (s (ports .state)).length = w) :
    (normalize ports).Runs (8*w+5) s (Function.update (Function.update s (ports .state)
      (s (ports .initial))) (ports .running) (true :: (s (ports .running)).tail)) := by
  have copied := copy_runs hp s hs ho
  have set := setRunning_runs (ports .running) (Function.update s (ports .state) (s (ports .initial)))
  have hne : ports .running ≠ ports .state := fun h => Port.noConfusion (hp h)
  rw [hi, hd] at copied
  rw [Function.update_of_ne hne] at set
  rw [show 8*w+5 = (w+7*w+3)+2 by omega]
  exact FiniteRoutine.Runs.followedBy copied set

end RAMTape.SuccessorInitial

end VPVNP
end Computability
end OAI
