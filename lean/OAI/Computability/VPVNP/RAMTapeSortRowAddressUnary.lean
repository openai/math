import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.RAMTapeWordSlice

/-! # Converting the sorter’s high-bit-first row offset to a unary count -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRowAddress.Unary

open TapeWord

/-- Stacks for high-bit-first binary input, the unary output and the scratch tally used while
doubling it. -/
inductive Port where | bits | out | tmp
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Control for reading the next bit, doubling the unary accumulator, restoring its marks and
adding the bit. -/
inductive State where
  | read | double (b : Bool) | put₁ (b : Bool) | put₂ (b : Bool)
  | restore (b : Bool) | putBack (b : Bool) | extra | done
  deriving DecidableEq, Fintype

/-- Consume high-order bits first and update the unary offset by doubling and adding the
incoming bit. -/
def code : StackCode Port State
  | .read => .pop .bits fun x => x.elim .done .double
  | .double b => .pop .out fun x => x.elim (.restore b) (fun _ => .put₁ b)
  | .put₁ b => .push .tmp true (.put₂ b)
  | .put₂ b => .push .tmp true (.double b)
  | .restore b => .pop .tmp fun x => x.elim (if b then .extra else .read) (fun _ => .putBack b)
  | .putBack b => .push .out true (.restore b)
  | .extra => .push .out true .read
  | .done => .halt true

/-- Install the remaining binary input and unary encodings of the output and scratch counts. -/
def bank (xs : List Bool) (n k : ℕ) : Stacks Port
  | .bits => xs
  | .out => List.replicate n true
  | .tmp => List.replicate k true

private def raw (xs out tmp : List Bool) : Stacks Port
  | .bits => xs
  | .out => out
  | .tmp => tmp

private theorem set_raw (xs out tmp v : List Bool) (p : Port) :
    Function.update (raw xs out tmp) p v = match p with
      | .bits => raw v out tmp
      | .out => raw xs v tmp
      | .tmp => raw xs out v := by
  cases p <;> funext k <;> cases k <;> rfl

local macro "unary_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [raw, List.replicate_succ, List.replicate_zero, List.head?_cons,
    List.head?_nil, List.tail_cons, List.tail_nil, Option.elim_none, Option.elim_some, set_raw])

private theorem double_runs (b : Bool) (xs : List Bool) (n k : ℕ) :
    StackRuns code (3*n+1) (.double b) (bank xs n k) (.restore b) (bank xs 0 (k+2*n)) := by
  change StackRuns code _ _ (raw xs _ _) _ (raw xs _ _)
  induction n generalizing k with
  | zero => simp only [Nat.mul_zero, Nat.add_zero]; unary_step; exact .nil ..
  | succ n ih =>
    simp only [Nat.mul_succ]
    unary_step
    unary_step
    unary_step
    simpa only [List.replicate_zero, List.replicate_succ, show k + (2*n+2) = (k+1+1)+2*n by omega]
      using ih (k+1+1)

private theorem restore_runs (b : Bool) (xs : List Bool) (n k : ℕ) :
    StackRuns code (2*k+1) (.restore b) (bank xs n k) (if b then .extra else .read)
      (bank xs (n+k) 0) := by
  change StackRuns code _ _ (raw xs _ _) _ (raw xs _ _)
  induction k generalizing n with
  | zero => simp only [Nat.mul_zero, Nat.add_zero]; unary_step; exact .nil ..
  | succ k ih =>
    simp only [Nat.mul_succ]
    unary_step
    unary_step
    simpa only [List.replicate_zero, List.replicate_succ, show n+(k+1) = (n+1)+k by omega] using ih (n+1)

private def eval (xs : List Bool) (n : ℕ) : ℕ := xs.foldl (fun a b => 2*a+b.toNat) n

private theorem scan (xs : List Bool) (n : ℕ) : ∃ t, t + 7*n ≤ 7*eval xs n + 4*xs.length+1 ∧
    StackRuns code t .read (bank xs n 0) .done (bank [] (eval xs n) 0) := by
  induction xs generalizing n with
  | nil =>
    refine ⟨1, by simp [eval]; omega, ?_⟩
    change StackRuns code 1 _ (raw [] _ _) _ (raw [] _ _)
    unary_step
    exact .nil ..
  | cons b xs ih =>
    obtain ⟨t, ht, tail⟩ := ih (2*n+b.toNat)
    have hd := double_runs b xs n 0
    have hr := restore_runs b xs 0 (2*n)
    simp only [Nat.zero_add] at hd hr
    have start : StackRuns code 1 .read (bank (b :: xs) n 0) (.double b) (bank xs n 0) := by
      change StackRuns code 1 _ (raw _ _ _) _ (raw _ _ _)
      unary_step
      exact .nil ..
    have endStep : StackRuns code b.toNat (if b then .extra else .read)
        (bank xs (2*n) 0) .read (bank xs (2*n+b.toNat) 0) := by
      cases b with
      | false => exact .nil ..
      | true =>
        change StackRuns code 1 _ (raw _ _ _) _ (raw _ _ _)
        unary_step
        exact .nil ..
    refine ⟨_, ?_, (((start.trans hd).trans hr).trans endStep).trans tail⟩
    simp only [eval, List.foldl_cons, List.length_cons] at ht ⊢
    cases b <;> simp_all only [Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem eval_value (xs : List Bool) (n : ℕ) :
    eval xs n = value xs.reverse + 2^xs.length*n := by
  induction xs generalizing n with
  | nil => simp [eval, value]
  | cons b xs ih =>
    change eval xs (2*n+b.toNat) = _
    rw [ih, List.reverse_cons, value_append, List.length_reverse, List.length_cons, pow_succ]
    simp only [value, Nat.mul_zero, Nat.add_zero]
    ring

/-- Convert the possibly toggled row address to the unary count used to fetch its partner
record. -/
def routine : FiniteRoutine Port := FiniteRoutine.ofStackCode code id .read (· == .done)

/-- The accumulator doubles once per bit. Charging each old unary mark to a newly
created mark bounds the total number of stack steps linearly in the final offset. -/
theorem runs (xs : List Bool) : ∃ t ≤ 7*value xs + 4*xs.length+1,
    routine.Runs t (bank xs.reverse 0 0) (bank [] (value xs) 0) := by
  obtain ⟨t, ht, run⟩ := scan xs.reverse 0
  simp only [eval_value, List.reverse_reverse, Nat.mul_zero, Nat.add_zero, List.length_reverse] at ht run
  refine ⟨t, ht, ?_⟩
  exact FiniteRoutine.runs_ofStackCode_framed Function.injective_id rfl rfl
    (fun q h => by simp only [beq_iff_eq] at h; subst q; rfl) run (fun _ => rfl) (fun _ => rfl)
    (fun k h => (h k rfl).elim)

end RAMTape.SortRowAddress.Unary

end VPVNP
end Computability
end OAI
