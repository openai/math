import OAI.Computability.VPVNP.RAMTapeWordComparison
import OAI.Computability.VPVNP.RAMTapeWordOperands
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-!
# Read-only word comparisons in the outer site processor

The cumulative charge, its bounds, and the incoming or outgoing persistent
state are full-width words. Two operand copies are compared by a fixed table;
a comparison preserves both source words and returns its decision in one bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteTests

open TapeWord BurstRAM

/-- Full-width site fields for the bucket bounds, cumulative cost, global cap, persistent state
and the target cut's cost and state. -/
inductive WordField where
  | lower | cost | boundary | cap | state | targetCost | targetState
  deriving DecidableEq

instance : Fintype WordField := derive_fintype% _

/-- Flags indicating whether the incoming cut is running, whether a target cut is present and
whether that target is running. -/
inductive BitField where
  | running | hasTarget | targetRunning
  deriving DecidableEq

instance : Fintype BitField := derive_fintype% _

/-- Stack ports for decoded site fields, unused choices and verdict bits, together with the
operand and scratch stacks for read-only comparisons. -/
inductive Port where
  | word (f : WordField) | bit (f : BitField) | choices | verdict
  | left | right | tmp | out | sourceTmp | copyTmp
  deriving DecidableEq, Fintype

/-- Decoded site data on which entry, iteration and final checks operate, comprising
fixed-width words, status flags and the remaining choices. -/
structure Snapshot (w : ℕ) where
  /-- Fixed-width cost, bound and state words indexed by their role in the site checks. -/
  words : WordField → Word w
  /-- Boolean values of the running and target-status fields used to interpret the cut words. -/
  flags : BitField → Bool
  /-- Unconsumed private choice stream tested for exact exhaustion when the site closes. -/
  choices : List Bool

variable {w : ℕ}

/-- Encode each word as its bit string and each flag as a singleton stack, install the choices
and initialize the verdict and comparison scratch stacks to empty. -/
def Snapshot.bank (s : Snapshot w) : Stacks Port
  | .word f => wordBits (s.words f)
  | .bit f => [s.flags f]
  | .choices => s.choices
  | _ => []

private def copyPorts (src : WordField) (dest : Bool) : ScanPort → Port
  | .left => .word src
  | .right => .sourceTmp
  | .tmp => .copyTmp
  | .out => if dest then .right else .left

private theorem copy_inj (src : WordField) (dest : Bool) : Function.Injective (copyPorts src dest) := by
  intro i j h
  cases dest <;> cases i <;> cases j <;> simp_all [copyPorts]

private def normal : Operand.State Unit → Bool
  | .done _ => true
  | _ => false

private def copy (src : WordField) (dest : Bool) : FiniteRoutine Port :=
  FiniteRoutine.ofStackCode (Operand.code Operand.copyBit) (copyPorts src dest) (.clear ()) normal

private theorem copy_runs (src : WordField) (dest : Bool) (s : Stacks Port)
    (h₁ : s .sourceTmp = []) (h₂ : s .copyTmp = []) :
    let dst : Port := if dest then .right else .left
    (copy src dest).Runs ((s dst).length + 7*(s (.word src)).length + 3) s
      (Function.update s dst (s (.word src))) := by
  dsimp only
  refine FiniteRoutine.runs_ofStackCode_framed (copy_inj src dest) (normal := normal)
    rfl rfl (fun q h => ?_) (Operand.copy_run (s (.word src)) (s (if dest then .right else .left))) ?_ ?_ ?_
  · cases q <;> first | rfl | contradiction
  · intro k
    cases k <;> first | rfl | exact h₁ | exact h₂
  · intro k
    cases dest <;> cases k <;> simp [copyPorts, scanStacks, h₁, h₂]
  · intro k hk
    exact Function.update_of_ne (Ne.symm (hk .out)) ..

private def cmpPorts : ScanPort → Port
  | .left => .left | .right => .right | .tmp => .tmp | .out => .out

private theorem cmp_inj : Function.Injective cmpPorts := by
  intro i j h
  cases i <;> cases j <;> simp_all [cmpPorts]

private def scanFlag (op : Comparison.Op) : FiniteRoutine Port := FiniteRoutine.ofRoutine {
  entry := Comparison.State.scan (.left op.initial)
  code := fun
    | .done b => .push .left b none
    | q@(.scan _) => (Comparison.code op q).rename cmpPorts some }

/-- Return one test bit in the left scratch stack. Both source words remain
available, including when they name the same field. -/
def compare (op : Comparison.Op) (x y : WordField) : FiniteRoutine Port :=
  ((copy x false).followedBy (copy y true)).followedBy (scanFlag op)

theorem compare_runs (op : Comparison.Op) (x y : WordField) (s : Snapshot w) :
    (compare op x y).Runs (20*w+10) s.bank
      (Function.update s.bank .left [op.eval (s.words x) (s.words y)]) := by
  let s₁ := Function.update s.bank .left (wordBits (s.words x))
  let s₂ := Function.update s₁ .right (wordBits (s.words y))
  have first : (copy x false).Runs (7*w+3) s.bank s₁ := by
    simpa only [Bool.false_eq_true, ite_false, s₁, Snapshot.bank, length_wordBits, List.length_nil, Nat.zero_add] using
      copy_runs x false s.bank rfl rfl
  have second : (copy y true).Runs (7*w+3) s₁ s₂ := by
    have h := copy_runs y true s₁ rfl rfl
    change (copy y true).Runs (0 + 7*(wordBits (s.words y)).length+3) s₁ s₂ at h
    simpa only [length_wordBits, Nat.zero_add] using h
  have hc (q : Comparison.State) (hq : (Comparison.code op q).returns = false) :
      (scanFlag op).body.standalone (some q) = (Comparison.code op q).rename cmpPorts some := by
    cases q with
    | scan => rfl
    | done => contradiction
  have scan := (Comparison.word_run op (s.words x) (s.words y)).lift cmpPorts cmp_inj some s.bank hc
  have hi : installStacks cmpPorts s.bank (scanStacks (wordBits (s.words x)) (wordBits (s.words y)) [] []) = s₂ := by
    apply installStacks_frame cmp_inj
    · intro i; cases i <;> rfl
    · intro j hj
      exact (Function.update_of_ne (Ne.symm (hj .right)) ..).trans
        (Function.update_of_ne (Ne.symm (hj .left)) ..)
  have ho : installStacks cmpPorts s.bank (scanStacks [] [] [] []) = s.bank :=
    installStacks_eq cmp_inj s.bank _ (fun i => by cases i <;> rfl)
  rw [hi, ho] at scan
  let b := op.eval (s.words x) (s.words y)
  have push : StackRuns (scanFlag op).body.standalone 1 (some (.done b)) s.bank none
      (Function.update s.bank .left [b]) := .cons (.push rfl) (.nil ..)
  have hr : (scanFlag op).Runs ((6*w+3)+1) s₂ (Function.update s.bank .left [b]) := scan.trans push
  rw [show 20*w+10 = (7*w+3+(7*w+3)) + ((6*w+3)+1) by omega]
  exact FiniteRoutine.Runs.followedBy (FiniteRoutine.Runs.followedBy first second) hr

end RAMTape.SiteTests

end VPVNP
end Computability
end OAI
