import OAI.Computability.VPVNP.RAMTapeSortDecision
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-! # Scanning and saving both words of one comparator field -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Sorter

/-- Comparator ports for the two operands, the reversible width counter, saved operand bits,
staging, output block and validity flags. -/
inductive Port where
  | left | right | width | widthBack | savedLeft | savedRight | tmp | next | valid
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Bit-stack contents while a pair of records is scanned, preserved and optionally copied into
the next sorting layer. -/
structure Bank where
  /-- Unread bits of the left record stream. -/
  left : List Bool
  /-- Unread bits of the right record stream. -/
  right : List Bool
  /-- Unary markers limiting the scan of one field to one machine word. -/
  width : List Bool
  /-- Consumed width markers kept for restoring the counter after a field scan. -/
  widthBack : List Bool
  /-- Left operand bits accumulated in reverse order during comparison. -/
  savedLeft : List Bool
  /-- Right operand bits accumulated in reverse order during comparison. -/
  savedRight : List Bool
  /-- Temporary stack used to stage a selected record during the move to the next block. -/
  tmp : List Bool
  /-- Stack accumulating the selected output records for the next sorting layer. -/
  next : List Bool
  /-- Stack of Boolean comparison and format verdicts retained for the final acceptance check. -/
  valid : List Bool

/-- Interpret the named comparator bank as a stack indexed by each physical comparator port. -/
def Bank.stacks (s : Bank) : Stacks Port
  | .left => s.left
  | .right => s.right
  | .width => s.width
  | .widthBack => s.widthBack
  | .savedLeft => s.savedLeft
  | .savedRight => s.savedRight
  | .tmp => s.tmp
  | .next => s.next
  | .valid => s.valid

/-- Replace the bit stack on a single comparator port while retaining the others. -/
def Bank.update (s : Bank) (i : Port) (l : List Bool) : Bank :=
  match i with
  | .left => {s with left := l}
  | .right => {s with right := l}
  | .width => {s with width := l}
  | .widthBack => {s with widthBack := l}
  | .savedLeft => {s with savedLeft := l}
  | .savedRight => {s with savedRight := l}
  | .tmp => {s with tmp := l}
  | .next => {s with next := l}
  | .valid => {s with valid := l}

theorem Bank.update_stacks (s : Bank) (i : Port) (l : List Bool) :
    Function.update s.stacks i l = (s.update i l).stacks := by
  funext j
  cases i <;> cases j <;> rfl

/-- Control for scanning one fixed-width field, comparing and saving its bits, and restoring
the unary width counter. -/
inductive FieldState where
  | tick (s : WordState) | readLeft (s : WordState) | readRight (s : WordState) (x : Bool)
  | saveLeft (s : WordState) (x y : Bool) | saveRight (s : WordState) (y : Bool)
  | mark (s : WordState) | rewind (s : WordState) | restore (s : WordState)
  | done (s : WordState) | reject
  deriving DecidableEq, Fintype

/-- Pop paired operand bits under the unary width counter, update their comparison summary,
save both words and restore the counter. -/
def fieldCode : StackCode Port FieldState
  | .tick s => .pop .width fun mark ↦ mark.elim (.rewind s) fun _ ↦ .readLeft s
  | .readLeft s => .pop .left fun x ↦ x.elim .reject (.readRight s)
  | .readRight s x => .pop .right fun y ↦ y.elim .reject fun b ↦ .saveLeft (s.step x b) x b
  | .saveLeft s x y => .push .savedLeft x (.saveRight s y)
  | .saveRight s y => .push .savedRight y (.mark s)
  | .mark s => .push .widthBack true (.tick s)
  | .rewind s => .pop .widthBack fun mark ↦ mark.elim (.done s) fun _ ↦ .restore s
  | .restore s => .push .width true (.rewind s)
  | .done _ => .halt true
  | .reject => .halt false

local macro "field_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [Bank.stacks, Bank.update_stacks, Bank.update, List.head?_cons, List.tail_cons,
    List.head?_nil, List.tail_nil, Option.elim_some, Option.elim_none])

private theorem readPair (s : WordState) (b : Bank) (x y : Bool) :
    StackRuns fieldCode 6 (.tick s)
      {b with width := true :: b.width, left := x :: b.left, right := y :: b.right}.stacks
      (.tick (s.step x y))
      {b with widthBack := true :: b.widthBack, savedLeft := x :: b.savedLeft, savedRight := y :: b.savedRight}.stacks := by
  field_step
  field_step
  field_step
  field_step
  field_step
  field_step
  exact .nil ..

private theorem collect (s : WordState) (b : Bank) (xs ys : List Bool) (n : ℕ)
    (h : xs.length = ys.length) :
    StackRuns fieldCode (6*xs.length+1) (.tick s)
      {b with left := xs ++ b.left, right := ys ++ b.right, width := List.replicate xs.length true, widthBack := List.replicate n true}.stacks (.rewind (Boundary.Field.fold WordState.step s xs ys))
      {b with width := [], widthBack := List.replicate (xs.length+n) true, savedLeft := xs.reverse ++ b.savedLeft, savedRight := ys.reverse ++ b.savedRight}.stacks := by
  induction xs generalizing s b ys n with
  | nil =>
    have he := List.length_eq_zero_iff.mp h.symm
    subst ys
    simp only [List.length_nil, List.replicate_zero, List.nil_append, List.reverse_nil, Nat.zero_add,
      Nat.mul_zero, Boundary.Field.fold]
    field_step; exact .nil ..
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      let c := {b with left := xs ++ b.left, right := ys ++ b.right, width := List.replicate xs.length true, widthBack := List.replicate n true}
      have hnext := ih (s.step x y) {b with savedLeft := x :: b.savedLeft, savedRight := y :: b.savedRight}
        ys (n+1) (Nat.succ.inj h)
      rw [List.replicate_succ (n := n)] at hnext
      simpa [c, List.replicate_succ, Boundary.Field.fold, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, List.reverse_cons, List.append_assoc] using (readPair s c x y).trans hnext

private theorem rewind (s : WordState) (b : Bank) (n : ℕ) :
    StackRuns fieldCode (2*n+1) (.rewind s) {b with widthBack := List.replicate n true}.stacks
      (.done s) {b with width := List.replicate n true ++ b.width, widthBack := []}.stacks := by
  induction n generalizing b with
  | zero =>
    simp only [List.replicate_zero, Nat.mul_zero, List.nil_append]
    field_step; exact .nil ..
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1+1)+1 by omega, List.replicate_succ]
    field_step; field_step
    have hr := ih {b with width := true :: b.width}
    rw [← List.singleton_append (x := true), ← List.append_assoc, ← List.replicate_succ'] at hr
    exact hr

/-- Both consumed operands remain available on the two saved stacks in
reverse order. The width counter is returned intact. -/
theorem field_runs (s : WordState) (b : Bank) (xs ys : List Bool) (h : xs.length = ys.length) :
    StackRuns fieldCode (8*xs.length+2) (.tick s)
      {b with left := xs ++ b.left, right := ys ++ b.right, width := List.replicate xs.length true, widthBack := []}.stacks (.done (Boundary.Field.fold WordState.step s xs ys))
      {b with width := List.replicate xs.length true, widthBack := [], savedLeft := xs.reverse ++ b.savedLeft, savedRight := ys.reverse ++ b.savedRight}.stacks := by
  have hc := collect s b xs ys 0 h
  let endState := Boundary.Field.fold WordState.step s xs ys
  have hr := rewind endState {b with width := [], savedLeft := xs.reverse ++ b.savedLeft, savedRight := ys.reverse ++ b.savedRight} xs.length
  simp only [Nat.add_zero, List.replicate_zero] at hc
  simp only [List.append_nil] at hr
  rw [show 8*xs.length+2 = (6*xs.length+1)+(2*xs.length+1) by omega]
  exact hc.trans hr

end RAMTape.Sorter

end VPVNP
end Computability
end OAI
