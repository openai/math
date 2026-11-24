import OAI.Computability.VPVNP.RAMTapeWord
import OAI.Computability.VPVNP.StructuredStacks
import Mathlib.Tactic.DeriveFintype

/-! # Repetition by a binary field digit

The evaluator multiplies by one label as many times as specified by its
current base-`Q` digit. Its finite control decrements a little-endian bit
stack, using a second stack to save the trailing zeros. A positive digit
decreases by one before calling the matrix-step routine. The two digit
stacks together occupy at most the width of the digit throughout the scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorDigitRepeat

open RAMTape

/-- Finite control for decrementing a binary digit, restoring the digit stack and invoking the
scheduled callback once per decrement. -/
inductive State (Q : Type*) where
  | scan | mark | clearHigh | restore | restoreBit | discard | call (q : Q)
  deriving DecidableEq, Fintype

variable {K Q : Type*} [DecidableEq K]

/-- The callback returns to the scan for the next unit of the digit. -/
def repeatRoutine (src tmp : K) (body : Routine K Q) : Routine K (State Q) where
  entry := .scan
  code
    | .scan => .pop src (fun b => match b with
      | none => some .discard | some false => some .mark | some true => some .clearHigh)
    | .mark => .push tmp true (some .scan)
    | .clearHigh => .push src false (some .restore)
    | .restore => .pop tmp (fun b => if b.isSome then some .restoreBit else some (.call body.entry))
    | .restoreBit => .push src true (some .restore)
    | .discard => .pop tmp (fun b => if b.isSome then some .discard else none)
    | .call q => body.install State.call (some .scan) q

/-- Assign both digit stacks while carrying all other registers through. -/
def frame (src tmp : K) (base : Stacks K) (xs ys : List Bool) : Stacks K :=
  Function.update (Function.update base src xs) tmp ys

variable (src tmp : K) (hne : src ≠ tmp) (body : Routine K Q)
variable (c : ℕ → Stacks K → ℕ) (base : Stacks K)

include hne in
private theorem source_frame (xs ys : List Bool) : frame src tmp base xs ys src = xs := by
  simp [frame, hne]

include hne in
private theorem update_source (xs ys zs : List Bool) :
    Function.update (frame src tmp base xs ys) src zs = frame src tmp base zs ys := by
  funext k
  by_cases hk : k = src <;> by_cases hj : k = tmp <;> simp_all [frame]

private theorem update_tmp (xs ys zs : List Bool) :
    Function.update (frame src tmp base xs ys) tmp zs = frame src tmp base xs zs := by
  simp [frame]

private theorem scratch_frame (xs ys : List Bool) : frame src tmp base xs ys tmp = ys := by
  simp [frame]

include hne in
private theorem scan_false (n : ℕ) (xs ys : List Bool) :
    (repeatRoutine src tmp body).countFrom c (n+2) (some .scan) (frame src tmp base (false::xs) ys) =
      (repeatRoutine src tmp body).countFrom c n (some .scan) (frame src tmp base xs (true::ys)) := by
  simp [Routine.countFrom, repeatRoutine, source_frame src tmp hne, scratch_frame,
    update_source src tmp hne, update_tmp]

include hne in
private theorem scan_true (n : ℕ) (xs ys : List Bool) :
    (repeatRoutine src tmp body).countFrom c (n+2) (some .scan) (frame src tmp base (true::xs) ys) =
      (repeatRoutine src tmp body).countFrom c n (some .restore) (frame src tmp base (false::xs) ys) := by
  simp [Routine.countFrom, repeatRoutine, source_frame src tmp hne, update_source src tmp hne]

include hne in
private theorem scan_nil (n : ℕ) (ys : List Bool) :
    (repeatRoutine src tmp body).countFrom c (n+1) (some .scan) (frame src tmp base [] ys) =
      (repeatRoutine src tmp body).countFrom c n (some .discard) (frame src tmp base [] ys) := by
  simp [Routine.countFrom, repeatRoutine, source_frame src tmp hne, update_source src tmp hne]

include hne in
private theorem restore_bit (n : ℕ) (xs ys : List Bool) :
    (repeatRoutine src tmp body).countFrom c (n+2) (some .restore) (frame src tmp base xs (true::ys)) =
      (repeatRoutine src tmp body).countFrom c n (some .restore) (frame src tmp base (true::xs) ys) := by
  simp [Routine.countFrom, repeatRoutine, scratch_frame, update_tmp, source_frame src tmp hne,
    update_source src tmp hne]

include hne in
private theorem scan_zeros (l n : ℕ) (xs ys : List Bool) :
    (repeatRoutine src tmp body).countFrom c (n + 2*l) (some .scan)
        (frame src tmp base (List.replicate l false ++ xs) ys) =
      (repeatRoutine src tmp body).countFrom c n (some .scan)
        (frame src tmp base xs (List.replicate l true ++ ys)) := by
  induction l generalizing ys with
  | zero => simp
  | succ l ih =>
    rw [show n + 2*(l+1) = n+2*l+2 by omega, List.replicate_succ, List.cons_append,
      scan_false src tmp hne body c, ih, List.replicate_succ', List.append_assoc]
    rfl

include hne in
private theorem restore_ones (l n : ℕ) (xs : List Bool) :
    (repeatRoutine src tmp body).countFrom c (n + 2*l + 1) (some .restore)
        (frame src tmp base xs (List.replicate l true)) =
      (repeatRoutine src tmp body).countFrom c n (some (.call body.entry))
        (frame src tmp base (List.replicate l true ++ xs) []) := by
  induction l generalizing xs with
  | zero => simp [Routine.countFrom, repeatRoutine, scratch_frame, update_tmp]
  | succ l ih =>
    rw [show n+2*(l+1)+1 = n+2*l+1+2 by omega]
    nth_rw 1 [List.replicate_succ]
    rw [restore_bit src tmp hne body c, ih, List.replicate_succ', List.append_assoc]
    rfl

private theorem discard_one (n : ℕ) (ys : List Bool) :
    (repeatRoutine src tmp body).countFrom c (n+1) (some .discard)
        (frame src tmp base [] (true::ys)) =
      (repeatRoutine src tmp body).countFrom c n (some .discard) (frame src tmp base [] ys) := by
  simp [Routine.countFrom, repeatRoutine, scratch_frame, update_tmp]

private theorem discard_ones (l n : ℕ) :
    (repeatRoutine src tmp body).countFrom c (n+l+1) (some .discard)
        (frame src tmp base [] (List.replicate l true)) = c n (frame src tmp base [] []) := by
  induction l with
  | zero => simp [Routine.countFrom, repeatRoutine, scratch_frame, update_tmp]
  | succ l ih => rw [show n+(l+1)+1 = n+l+1+1 by omega, List.replicate_succ, discard_one, ih]

include hne in
/-- On a zero digit the control returns directly to the continuation. -/
theorem count_zero (w fuel : ℕ) :
    (repeatRoutine src tmp body).count c (fuel + (3*w+2))
        (frame src tmp base (List.replicate w false) []) = c fuel (frame src tmp base [] []) := by
  change (repeatRoutine src tmp body).countFrom c _ (some .scan) _ = _
  rw [show fuel+(3*w+2) = (fuel+w+1+1)+2*w by omega]
  have h := scan_zeros src tmp hne body c base w (fuel+w+1+1) [] []
  simp only [List.append_nil] at h
  rw [h]
  rw [scan_nil src tmp hne body c]
  exact discard_ones src tmp body c base w fuel

include hne in
/-- A positive digit with `l` trailing zeros costs `4*l+3` control instructions
before entering the callback on the decremented digit. This equality retains
every nondeterministic branch of the callback. -/
theorem count_positive (l fuel : ℕ) (xs : List Bool) :
    (repeatRoutine src tmp body).count c (fuel + (4*l+3))
        (frame src tmp base (List.replicate l false ++ true :: xs) []) =
      body.count ((repeatRoutine src tmp body).count c) fuel
        (frame src tmp base (List.replicate l true ++ false :: xs) []) := by
  change (repeatRoutine src tmp body).countFrom c _ (some .scan) _ = _
  rw [show fuel+(4*l+3) = (fuel+2*l+1+1+1)+2*l by omega,
    scan_zeros src tmp hne body c base l (fuel+2*l+1+1+1), List.append_nil]
  rw [scan_true src tmp hne body c, restore_ones src tmp hne body c base l fuel]
  exact Routine.countFrom_install (repeatRoutine src tmp body) body State.call (some .scan)
    (fun _ => rfl) c fuel (some body.entry) _

/-- The positive branch implements subtraction of one, at the same bit width. -/
theorem value_decrement (l : ℕ) (xs : List Bool) :
    TapeWord.value (List.replicate l true ++ false :: xs) + 1 =
      TapeWord.value (List.replicate l false ++ true :: xs) := by
  induction l with
  | zero => simp [TapeWord.value, Nat.add_comm]
  | succ l ih =>
    simp only [List.replicate_succ, List.cons_append, TapeWord.value, Bool.toNat_true, Bool.toNat_false]
    omega

end EvaluatorDigitRepeat

end VPVNP
end Computability
end OAI
