import OAI.Computability.VPVNP.EvaluatorRadixSpace
import Mathlib.Data.List.TakeDrop

/-!
# Selecting a digit from a packed bit stack

The offset and width are unary. Two loops move the skipped and selected bits
onto a saved stack. The second loop also copies the selected bits. Reversing
the two temporary stacks restores the input and emits the digit in its
original bit order. The same finite control works for every table size.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorDigitLookup

open RAMTape EvaluatorRadixDivision

/-- The source table, skip and width counters, and temporary and output stacks for extracting
one digit. -/
inductive Port where
  | src | offset | width | saved | revDigit | digit
  deriving DecidableEq

instance : Fintype Port :=
  ⟨{.src, .offset, .width, .saved, .revDigit, .digit}, by intro k; cases k <;> decide⟩

private def bank (data : List Bool) (offset width : ℕ) (saved revDigit out : List Bool) :
    Stacks Port
  | .src => data
  | .offset => List.replicate offset true
  | .width => List.replicate width true
  | .saved => saved
  | .revDigit => revDigit
  | .digit => out

/-- Initial lookup bank holding the table, unary offset and width, and incoming output stack,
with both reversal stacks empty. -/
def ready (data : List Bool) (offset width : ℕ) (out : List Bool) : Stacks Port :=
  bank data offset width [] [] out

private def skipBit : FiniteRoutine Port :=
  .ofRoutine (Routine.popCase .src (Routine.halt false) (Routine.push .saved false)
    (Routine.push .saved true))

private def copyBit : FiniteRoutine Port :=
  let pushBoth (b : Bool) := (Routine.push Port.saved b).followedBy (Routine.push .revDigit b)
  .ofRoutine (Routine.popCase .src (Routine.halt false) (pushBoth false) (pushBoth true))

private def consumeMarks (counter : Port) (body : FiniteRoutine Port) : FiniteRoutine Port :=
  .ofRoutine (Routine.popLoop counter (fun _ => true) (Routine.halt false) body.body)

/-- Select a bit interval, restore the table, and prepend the selected interval
to the digit stack. Malformed inputs that exhaust the source are rejected. -/
def lookupRoutine : FiniteRoutine Port :=
  (((consumeMarks .offset skipBit).followedBy (consumeMarks .width copyBit)).followedBy
    (reverseOnto .saved .src)).followedBy (reverseOnto .revDigit .digit)

/-- Instruction count for skipping the offset, extracting width bits, restoring the table and
prepending the digit to the output stack. -/
def lookupTicks (offset width : ℕ) := 5 * offset + 8 * width + 4

private theorem skipBit_runs (b : Bool) (xs : List Bool) (i w : ℕ) (s r out : List Bool) :
    skipBit.Runs 2 (bank (b :: xs) i w s r out) (bank xs i w (b :: s) r out) := by
  let a := bank xs i w s r out
  have ha : Function.update (bank (b :: xs) i w s r out) .src xs = a := by
    funext k; cases k <;> rfl
  have hb : Function.update a .saved (b :: a .saved) = bank xs i w (b :: s) r out := by
    funext k; cases k <;> rfl
  have push := Routine.runs_push .saved b a
  rw [hb] at push
  cases b
  · apply Routine.runs_popCase_false Port.src _ _ _ (s := bank (false :: xs) i w s r out) rfl
    rwa [ha]
  · apply Routine.runs_popCase_true Port.src _ _ _ (s := bank (true :: xs) i w s r out) rfl
    rwa [ha]

private theorem copyBit_runs (b : Bool) (xs : List Bool) (i w : ℕ) (s r out : List Bool) :
    copyBit.Runs 3 (bank (b :: xs) i w s r out) (bank xs i w (b :: s) (b :: r) out) := by
  let a := bank xs i w s r out
  let v := bank xs i w (b :: s) r out
  have ha : Function.update (bank (b :: xs) i w s r out) .src xs = a := by
    funext k; cases k <;> rfl
  have hv : Function.update a .saved (b :: a .saved) = v := by
    funext k; cases k <;> rfl
  have ho : Function.update v .revDigit (b :: v .revDigit) = bank xs i w (b :: s) (b :: r) out := by
    funext k; cases k <;> rfl
  have h₁ := Routine.runs_push .saved b a
  have h₂ := Routine.runs_push .revDigit b v
  rw [hv] at h₁
  rw [ho] at h₂
  have push := h₁.followedBy h₂
  cases b
  · apply Routine.runs_popCase_false Port.src _ _ _ (s := bank (false :: xs) i w s r out) rfl
    rwa [ha]
  · apply Routine.runs_popCase_true Port.src _ _ _ (s := bank (true :: xs) i w s r out) rfl
    rwa [ha]

private theorem skip_runs (pre tail : List Bool) (w : ℕ) (s r out : List Bool) :
    (consumeMarks .offset skipBit).Runs (3 * pre.length + 1)
      (bank (pre ++ tail) pre.length w s r out)
      (bank tail 0 w (pre.reverse ++ s) r out) := by
  induction pre generalizing s with
  | nil =>
    exact Routine.Runs.popLoop_empty Port.offset (fun _ => true) (Routine.halt false)
      skipBit.body (s := bank tail 0 w s r out) rfl
  | cons b pre ih =>
    let a := bank (b :: pre ++ tail) pre.length w s r out
    have ha : Function.update (bank ((b :: pre) ++ tail) (b :: pre).length w s r out)
        Port.offset (List.replicate pre.length true) = a := by
      funext k; cases k <;> rfl
    have h := Routine.Runs.popLoop_true_continue Port.offset (fun _ => true) (Routine.halt false)
      skipBit.body (s := bank ((b :: pre) ++ tail) (b :: pre).length w s r out)
      (List.replicate_succ ..) rfl (by rw [ha]; exact skipBit_runs ..) (ih (b :: s))
    simpa only [consumeMarks, FiniteRoutine.Runs, FiniteRoutine.ofRoutine, List.length_cons,
      Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append, show ∀ n : ℕ, n + 3 + 1 = 1 + 2 + (n + 1) by omega] using h

private theorem copy_runs (cell tail : List Bool) (s r out : List Bool) :
    (consumeMarks .width copyBit).Runs (4 * cell.length + 1)
      (bank (cell ++ tail) 0 cell.length s r out)
      (bank tail 0 0 (cell.reverse ++ s) (cell.reverse ++ r) out) := by
  induction cell generalizing s r with
  | nil =>
    exact Routine.Runs.popLoop_empty Port.width (fun _ => true) (Routine.halt false)
      copyBit.body (s := bank tail 0 0 s r out) rfl
  | cons b cell ih =>
    let a := bank (b :: cell ++ tail) 0 cell.length s r out
    have ha : Function.update (bank ((b :: cell) ++ tail) 0 (b :: cell).length s r out)
        Port.width (List.replicate cell.length true) = a := by
      funext k; cases k <;> rfl
    have h := Routine.Runs.popLoop_true_continue Port.width (fun _ => true) (Routine.halt false)
      copyBit.body (s := bank ((b :: cell) ++ tail) 0 (b :: cell).length s r out)
      (List.replicate_succ ..) rfl (by rw [ha]; exact copyBit_runs ..) (ih (b :: s) (b :: r))
    simpa only [consumeMarks, FiniteRoutine.Runs, FiniteRoutine.ofRoutine, List.length_cons,
      Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append, show ∀ n : ℕ, n + 4 + 1 = 1 + 3 + (n + 1) by omega] using h

/-- The returned table agrees bit-for-bit with the input. The two counters
and the two temporary stacks are empty after every successful lookup. -/
theorem lookupRoutine_runs (pre cell post out : List Bool) :
    lookupRoutine.Runs (lookupTicks pre.length cell.length)
      (ready (pre ++ cell ++ post) pre.length cell.length out)
      (ready (pre ++ cell ++ post) 0 0 (cell ++ out)) := by
  let a := bank (cell ++ post) 0 cell.length pre.reverse [] out
  let b := bank post 0 0 (cell.reverse ++ pre.reverse) cell.reverse out
  let c := bank (pre ++ cell ++ post) 0 0 [] cell.reverse out
  have h₁ : (consumeMarks .offset skipBit).Runs (3 * pre.length + 1)
      (ready (pre ++ cell ++ post) pre.length cell.length out) a := by
    simpa only [ready, List.append_assoc, List.append_nil, a] using
      skip_runs pre (cell ++ post) cell.length [] [] out
  have h₂ : (consumeMarks .width copyBit).Runs (4 * cell.length + 1) a b := by
    simpa only [a, b, List.append_nil] using copy_runs cell post pre.reverse [] out
  have h₃ := reverseOnto_runs (src := Port.saved) (dst := .src) (by decide) b c rfl
    (show pre ++ cell ++ post = (cell.reverse ++ pre.reverse).reverse ++ post by simp)
    (by intro k hk hk'; cases k <;> first | rfl | exact (hk rfl).elim | exact (hk' rfl).elim)
  have h₄ := reverseOnto_runs (src := Port.revDigit) (dst := .digit) (by decide) c
    (ready (pre ++ cell ++ post) 0 0 (cell ++ out)) rfl
    (show cell ++ out = cell.reverse.reverse ++ out by simp)
    (by intro k hk hk'; cases k <;> first | rfl | exact (hk rfl).elim | exact (hk' rfl).elim)
  have h := ((h₁.followedBy h₂).followedBy h₃).followedBy h₄
  have ht : lookupTicks pre.length cell.length = 3 * pre.length + 1 + (4 * cell.length + 1) +
      (2 * (b .saved).length + 1) + (2 * (c .revDigit).length + 1) := by
    simp only [lookupTicks, b, c, bank, List.length_append, List.length_reverse]; omega
  rw [ht]
  exact h

theorem lookupRoutine_runs_at (data out : List Bool) (offset width : ℕ)
    (fits : offset + width ≤ data.length) :
    lookupRoutine.Runs (lookupTicks offset width) (ready data offset width out)
      (ready data 0 0 ((data.drop offset).take width ++ out)) := by
  have ho : offset ≤ data.length := by omega
  simpa only [List.length_take, min_eq_left ho, List.length_drop,
    min_eq_left (show width ≤ data.length - offset by omega), List.append_assoc,
    List.take_append_drop] using
    lookupRoutine_runs (data.take offset) ((data.drop offset).take width)
      ((data.drop offset).drop width) out

/-- A linear peak storage bound for all six stacks at every intermediate point. -/
theorem lookupRoutine_space (data out : List Bool) (offset width : ℕ) (fits : offset + width ≤ data.length)
    {n : ℕ} {q : Option lookupRoutine.State} {u : Stacks Port}
    (run : StackRuns lookupRoutine.body.standalone n (some lookupRoutine.body.entry)
      (ready data offset width out) q u) :
    ∑ k, (u k).length ≤ 6 * (data.length + out.length + lookupTicks offset width) := by
  have hn := ticks_le_at_return (lookupRoutine_runs_at data out offset width fits) (by rfl) run
  have h (k : Port) : (u k).length ≤ data.length + out.length + lookupTicks offset width := by
    have h₁ := run_length run k
    have h₂ : (ready data offset width out k).length ≤ data.length + out.length := by
      cases k <;> simp [ready, bank] <;> omega
    omega
  calc
    ∑ k, (u k).length ≤ ∑ _ : Port, (data.length + out.length + lookupTicks offset width) :=
      Finset.sum_le_sum (fun k _ => h k)
    _ = _ := by simp [show Fintype.card Port = 6 by decide]

end EvaluatorDigitLookup

end VPVNP
end Computability
end OAI
