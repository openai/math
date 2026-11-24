import OAI.Computability.VPVNP.RAMTapeInputPorts
import OAI.Computability.VPVNP.UniversalMachine

/-!
# Extracting the literal self-delimiting table prefix

A fixed stack control reads one unary length digit at a time. Each digit
supplies one counter marker, authorizing one payload bit after the zero
delimiter. It copies the entire field, including those length digits and
the delimiter, into the prefix stack in its original order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

/-- Control for reading the unary prefix length, zero delimiter, and the indicated payload
bits, then restoring the whole prefix in order. -/
inductive PrefixPhase
  | entry | saveDigit | countDigit | delimiter | nextBit | readBit | saveBit (bit : Bool)
  | restore | put (bit : Bool) | done | reject
  deriving DecidableEq, Fintype

/-- Length-independent stack instructions for the first field. A missing
delimiter or a truncated table sends control to rejection. -/
def prefixCode : StackCode InputPort PrefixPhase
  | .entry => .pop .input fun b => b.elim .reject fun digit => if digit then .saveDigit else .delimiter
  | .saveDigit => .push .tmp true .countDigit
  | .countDigit => .push .count true .entry
  | .delimiter => .push .tmp false .nextBit
  | .nextBit => .pop .count fun marker => marker.elim .restore fun _ => .readBit
  | .readBit => .pop .input fun b => b.elim .reject .saveBit
  | .saveBit bit => .push .tmp bit .nextBit
  | .restore => .pop .tmp fun b => b.elim .done .put
  | .put bit => .push .prefix bit .restore
  | .done => .halt true
  | .reject => .halt false

private def workStacks (base : Stacks InputPort) (bits tmp count result : List Bool) : Stacks InputPort
  | .input => bits
  | .tmp => tmp
  | .count => count
  | .prefix => result
  | k => base k

private theorem update_input (base : Stacks InputPort) (bits tmp count result new : List Bool) :
    Function.update (workStacks base bits tmp count result) .input new =
      workStacks base new tmp count result := by
  funext i
  cases i <;> simp [workStacks]

private theorem update_tmp (base : Stacks InputPort) (bits tmp count result new : List Bool) :
    Function.update (workStacks base bits tmp count result) .tmp new =
      workStacks base bits new count result := by
  funext i
  cases i <;> simp [workStacks]

private theorem update_count (base : Stacks InputPort) (bits tmp count result new : List Bool) :
    Function.update (workStacks base bits tmp count result) .count new =
      workStacks base bits tmp new result := by
  funext i
  cases i <;> simp [workStacks]

private theorem update_result (base : Stacks InputPort) (bits tmp count result new : List Bool) :
    Function.update (workStacks base bits tmp count result) .prefix new =
      workStacks base bits tmp count new := by
  funext i
  cases i <;> simp [workStacks]

local macro "prefix_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [workStacks, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, ↓reduceIte, Bool.false_eq_true,
    update_input, update_tmp, update_count, update_result])

private theorem digits_runs (base : Stacks InputPort) (n : ℕ) (rest tmp count result : List Bool) :
    StackRuns prefixCode (3*n+2) .entry
      (workStacks base (List.replicate n true ++ false :: rest) tmp count result)
      .nextBit (workStacks base rest (false :: (List.replicate n true ++ tmp))
        (List.replicate n true ++ count) result) := by
  induction n generalizing tmp count with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    prefix_step
    prefix_step
    exact .nil ..
  | succ n ih =>
    rw [show 3*(n+1)+2 = (3*n+2)+1+1+1 by omega]
    rw [List.replicate_succ, List.cons_append]
    prefix_step
    prefix_step
    prefix_step
    have hrep : true :: List.replicate n true = List.replicate n true ++ [true] := by
      rw [← List.replicate_succ, List.replicate_succ']
    simpa only [hrep, List.append_assoc, List.singleton_append] using ih (true :: tmp) (true :: count)

private theorem payload_runs (base : Stacks InputPort) (t rest tmp result : List Bool) :
    StackRuns prefixCode (3*t.length+1) .nextBit
      (workStacks base (t ++ rest) tmp (List.replicate t.length true) result)
      .restore (workStacks base rest (t.reverse ++ tmp) [] result) := by
  induction t generalizing tmp with
  | nil =>
    simp only [List.length_nil, List.reverse_nil, List.nil_append, List.replicate_zero, Nat.mul_zero,
      Nat.zero_add]
    prefix_step
    exact .nil ..
  | cons b t ih =>
    simp only [List.length_cons, List.cons_append, List.replicate_succ, List.reverse_cons,
      List.append_assoc]
    rw [show 3*(t.length+1)+1 = (3*t.length+1)+1+1+1 by omega]
    prefix_step
    prefix_step
    prefix_step
    exact ih (b :: tmp)

private theorem restore_runs (base : Stacks InputPort) (rest tmp result : List Bool) :
    StackRuns prefixCode (2*tmp.length+1) .restore (workStacks base rest tmp [] result)
      .done (workStacks base rest [] [] (tmp.reverse ++ result)) := by
  induction tmp generalizing result with
  | nil =>
    simp only [List.length_nil, List.reverse_nil, List.nil_append, Nat.mul_zero, Nat.zero_add]
    prefix_step
    exact .nil ..
  | cons b tmp ih =>
    simp only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [show 2*(tmp.length+1)+1 = (2*tmp.length+1)+1+1 by omega]
    prefix_step
    prefix_step
    exact ih (b :: result)

/-- The machine consumes precisely the self-delimiting table prefix. It leaves
the suffix at the input head, restores both scratch stacks and preserves the
values of every other port. The run length depends only on the table length. -/
theorem prefix_runs (s : Stacks InputPort) (t suffix : List Bool)
    (hin : s .input = (UniversalMachine.unary t.length ++ t) ++ suffix)
    (ht : s .tmp = []) (hc : s .count = []) (hp : s .prefix = []) :
    StackRuns prefixCode (10*t.length+6) .entry s .done
      (Function.update (Function.update s .input suffix) .prefix (UniversalMachine.unary t.length ++ t)) := by
  let digits := List.replicate t.length true
  have h₁ := digits_runs s t.length (t ++ suffix) [] [] []
  have h₂ := payload_runs s t suffix (false :: digits) []
  have h₃ := restore_runs s suffix (t.reverse ++ false :: digits) []
  simp only [List.append_nil] at h₁ h₃
  have h := (h₁.trans h₂).trans h₃
  have hs : workStacks s (digits ++ false :: (t ++ suffix)) [] [] [] = s := by
    funext i
    cases i <;> simp [workStacks, hin, ht, hc, hp, UniversalMachine.unary, digits, List.append_assoc]
  have he : workStacks s suffix [] [] (t.reverse ++ false :: digits).reverse =
      Function.update (Function.update s .input suffix) .prefix (UniversalMachine.unary t.length ++ t) := by
    funext i
    cases i <;> simp [workStacks, ht, hc, UniversalMachine.unary, digits]
  rw [hs, he] at h
  convert h using 1
  simp [digits]
  omega

end RAMTape

end VPVNP
end Computability
end OAI
