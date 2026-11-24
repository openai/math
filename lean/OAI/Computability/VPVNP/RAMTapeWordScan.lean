import OAI.Computability.VPVNP.RAMTapeWord
import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Tactic.DeriveFintype

/-!
# Finite stack controls for binary word scans

The first pass pops matching bits of the operands, applies the one-bit
transition, and pushes each result onto a temporary stack. The second pass
reverses that stack onto the output. The same fixed table works at every word
width. Its final control remembers the carry, borrow, or other Boolean flag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord

open RAMTape

/-- The two operand stacks, reversed temporary result and final output stack for a binary word
scan. -/
inductive ScanPort where
  | left | right | tmp | out
  deriving DecidableEq

instance : Fintype ScanPort := derive_fintype% _

/-- Control for reading paired operand bits, carrying the Boolean flag, emitting a temporary
result and reversing it onto the output. -/
inductive ScanState where
  | left (flag : Bool)
  | right (flag bit : Bool)
  | emit (out flag : Bool)
  | restore (flag : Bool)
  | put (flag bit : Bool)
  | done (flag : Bool)
  | reject
  deriving DecidableEq, Fintype

/-- Run the one-bit operation on corresponding bits and return the result in word order with
the final flag in control. -/
def scanCode (step : Bool → Bool → Bool → Bool × Bool) : StackCode ScanPort ScanState
  | .left c => .pop .left (fun | none => .restore c | some b => .right c b)
  | .right c b => .pop .right (fun | none => .reject | some d => .emit (step c b d).1 (step c b d).2)
  | .emit bit c => .push .tmp bit (.left c)
  | .restore c => .pop .tmp (fun | none => .done c | some b => .put c b)
  | .put c bit => .push .out bit (.restore c)
  | .done _ => .halt true
  | .reject => .halt false

/-- Install the supplied bit lists on the left, right, temporary and output ports of the scan. -/
def scanStacks (x y tmp out : List Bool) : Stacks ScanPort
  | .left => x
  | .right => y
  | .tmp => tmp
  | .out => out

private theorem write_left (x y t o l : List Bool) :
    Function.update (scanStacks x y t o) .left l = scanStacks l y t o := by
  funext k; cases k <;> simp [Function.update, scanStacks]

private theorem write_right (x y t o l : List Bool) :
    Function.update (scanStacks x y t o) .right l = scanStacks x l t o := by
  funext k; cases k <;> simp [Function.update, scanStacks]

private theorem write_tmp (x y t o l : List Bool) :
    Function.update (scanStacks x y t o) .tmp l = scanStacks x y l o := by
  funext k; cases k <;> simp [Function.update, scanStacks]

private theorem write_out (x y t o l : List Bool) :
    Function.update (scanStacks x y t o) .out l = scanStacks x y t l := by
  funext k; cases k <;> simp [Function.update, scanStacks]

private theorem scan_first (step : Bool → Bool → Bool → Bool × Bool) (c : Bool)
    (x y t o : List Bool) (hlen : x.length = y.length) :
    StackRuns (scanCode step) (3 * x.length + 1) (.left c) (scanStacks x y t o)
      (.restore (scan step c x y).2) (scanStacks [] [] ((scan step c x y).1.reverse ++ t) o) := by
  induction x generalizing c y t with
  | nil =>
    have hy : y = [] := List.length_eq_zero_iff.mp hlen.symm
    subst y
    have hp : StackStep (scanCode step) (.left c) (scanStacks [] [] t o)
        (.restore c) (scanStacks [] [] t o) := by
      simpa [write_left, scanStacks] using (StackStep.pop (s := scanStacks [] [] t o)
        (show scanCode step (.left c) = _ from rfl))
    exact .cons hp (.nil ..)
  | cons b xs ih =>
    cases y with
    | nil => simp at hlen
    | cons d ys =>
      have hleft : StackStep (scanCode step) (.left c) (scanStacks (b :: xs) (d :: ys) t o)
          (.right c b) (scanStacks xs (d :: ys) t o) := by
        simpa [write_left, scanStacks] using (StackStep.pop (s := scanStacks (b :: xs) (d :: ys) t o)
          (show scanCode step (.left c) = _ from rfl))
      have hright : StackStep (scanCode step) (.right c b) (scanStacks xs (d :: ys) t o)
          (.emit (step c b d).1 (step c b d).2) (scanStacks xs ys t o) := by
        simpa [write_right, scanStacks] using (StackStep.pop (s := scanStacks xs (d :: ys) t o)
          (show scanCode step (.right c b) = _ from rfl))
      have hemit : StackStep (scanCode step) (.emit (step c b d).1 (step c b d).2) (scanStacks xs ys t o)
          (.left (step c b d).2) (scanStacks xs ys ((step c b d).1 :: t) o) := by
        simpa [write_tmp, scanStacks] using (StackStep.push (s := scanStacks xs ys t o)
          (show scanCode step (.emit (step c b d).1 (step c b d).2) = _ from rfl))
      simpa only [scan, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
        List.length_cons, Nat.mul_succ, Nat.add_assoc] using
          StackRuns.cons hleft (.cons hright (.cons hemit (ih _ _ _ (Nat.succ.inj hlen))))

private theorem scan_restore (step : Bool → Bool → Bool → Bool × Bool) (c : Bool)
    (t o : List Bool) :
    StackRuns (scanCode step) (2 * t.length + 1) (.restore c) (scanStacks [] [] t o)
      (.done c) (scanStacks [] [] [] (t.reverse ++ o)) := by
  induction t generalizing o with
  | nil =>
    have hpop : StackStep (scanCode step) (.restore c) (scanStacks [] [] [] o)
        (.done c) (scanStacks [] [] [] o) := by
      simpa [write_tmp, scanStacks] using (StackStep.pop (s := scanStacks [] [] [] o)
        (show scanCode step (.restore c) = _ from rfl))
    exact .cons hpop (.nil ..)
  | cons b t ih =>
    have hpop : StackStep (scanCode step) (.restore c) (scanStacks [] [] (b :: t) o)
        (.put c b) (scanStacks [] [] t o) := by
      simpa [write_tmp, scanStacks] using (StackStep.pop (s := scanStacks [] [] (b :: t) o)
        (show scanCode step (.restore c) = _ from rfl))
    have hpush : StackStep (scanCode step) (.put c b) (scanStacks [] [] t o)
        (.restore c) (scanStacks [] [] t (b :: o)) := by
      simpa [write_out, scanStacks] using (StackStep.push (s := scanStacks [] [] t o)
        (show scanCode step (.put c b) = _ from rfl))
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
      List.length_cons, Nat.mul_succ, Nat.add_assoc] using StackRuns.cons hpop (.cons hpush (ih _))

/-- Both inputs are consumed. The output stack receives the little-endian
result. The scratch stack is empty and the final flag is retained. -/
theorem scanRuns (step : Bool → Bool → Bool → Bool × Bool) (c : Bool)
    (x y o : List Bool) (hlen : x.length = y.length) :
    StackRuns (scanCode step) (5 * x.length + 2) (.left c) (scanStacks x y [] o)
      (.done (scan step c x y).2) (scanStacks [] [] [] ((scan step c x y).1 ++ o)) := by
  have hf := scan_first step c x y [] o hlen
  simp only [List.append_nil] at hf
  have hr := scan_restore step (scan step c x y).2 (scan step c x y).1.reverse o
  simp only [List.reverse_reverse, List.length_reverse, length_scan step c x y hlen] at hr
  convert hf.trans hr using 1
  omega

end TapeWord

end VPVNP
end Computability
end OAI
