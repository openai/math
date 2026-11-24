import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.RAMTapeWordSlice
import OAI.Computability.VPVNP.RAMSortRouting

/-! # Indexed bit reads and stride-bit flips in the row address machine -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRowAddress.IndexScan

open TapeWord

/-- Read a little-endian bit with zero extension. -/
def read : ℕ → List Bool → Bool
  | _, [] => false
  | 0, b :: _ => b
  | j+1, _ :: bs => read j bs

/-- Toggle a bit within a fixed width. An out-of-range index preserves the word. -/
def flip : ℕ → List Bool → List Bool
  | _, [] => []
  | 0, b :: bs => (!b) :: bs
  | j+1, b :: bs => b :: flip j bs

@[simp] theorem length_flip (j : ℕ) (xs : List Bool) : (flip j xs).length = xs.length := by
  induction xs generalizing j with
  | nil => simp [flip]
  | cons b xs ih => cases j <;> simp [flip, ih]

theorem read_value (j : ℕ) (xs : List Bool) : read j xs = (value xs).testBit j := by
  induction xs generalizing j with
  | nil => simp [value, read]
  | cons b xs ih =>
    have h : b.toNat < 2^1 := by cases b <;> decide
    rw [value, Nat.add_comm, ← pow_one (2 : ℕ), Nat.testBit_two_pow_mul_add _ h]
    cases j with
    | zero => cases b <;> rfl
    | succ j => simpa [read] using ih j

private theorem read_flip (j k : ℕ) (xs : List Bool) :
    read k (flip j xs) = (read k xs ^^ decide (j = k ∧ j < xs.length)) := by
  induction xs generalizing j k with
  | nil => simp [read, flip]
  | cons b xs ih =>
    cases j <;> cases k <;> simp [read, flip, ih]

theorem flip_value (j : ℕ) (xs : List Bool) :
    value (flip j xs) = if j < xs.length then RAMSort.partner j (value xs) else value xs := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [← read_value, read_flip, read_value]
  by_cases h : j < xs.length <;> simp [h, RAMSort.partner, Nat.testBit_two_pow]

/-- The bit stream, unary position counter, reverse buffer and one-bit result of an indexed
address scan. -/
inductive Port where | bits | count | rev | flag
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Control for consuming the unary index, recording or flipping the addressed bit, draining
the remaining stream and reporting the result. -/
inductive State where
  | scan | count (b : Bool) | write (b : Bool) (found : Option Bool)
  | rest (b : Bool) | clear (b : Bool) | report (b : Bool) | done
  deriving DecidableEq, Fintype

/-- The same scan is used in two modes. A read returns the observed bit.
A partner scan emits the modified word in high-to-low order and returns
whether the stride bit belongs to the row. -/
def code (peer : Bool) : StackCode Port State
  | .scan => .pop .bits fun x => x.elim (.clear false) .count
  | .count b => .pop .count fun x => x.elim (.write (!b) (some b)) (fun _ => .write b none)
  | .write b found =>
    let next := found.elim .scan .rest
    if peer then .push .rev b next else .goto next
  | .rest b => .pop .bits fun x => x.elim (.clear (peer || b)) (fun z => .write z (some b))
  | .clear b => .pop .count fun x => x.elim (.report b) (fun _ => .clear b)
  | .report b => .push .flag b .done
  | .done => .halt true

/-- Install the source bits, remaining count, reversed bits and result flag on their
indexed-scan ports. -/
def bank (xs count rev flag : List Bool) : Stacks Port
  | .bits => xs
  | .count => count
  | .rev => rev
  | .flag => flag

private theorem set_bank (xs n rev flag v : List Bool) (p : Port) :
    Function.update (bank xs n rev flag) p v = match p with
      | .bits => bank v n rev flag
      | .count => bank xs v rev flag
      | .rev => bank xs n v flag
      | .flag => bank xs n rev v := by
  cases p <;> funext k <;> cases k <;> rfl

local macro "scan_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_
         | refine StackRuns.cons (.goto rfl) ?_)
  <;> simp only [bank, List.replicate_succ, List.replicate_zero, List.head?_cons, List.head?_nil,
    List.tail_cons, List.tail_nil, Option.elim_none, Option.elim_some, set_bank])

private theorem clear_run (peer b : Bool) (j : ℕ) (rev flag : List Bool) :
    StackRuns (code peer) (j+2) (.clear b) (bank [] (List.replicate j true) rev flag)
      .done (bank [] [] rev (b :: flag)) := by
  induction j with
  | zero => scan_step; scan_step; exact .nil ..
  | succ j ih => scan_step; exact ih

private theorem rest_run (peer b : Bool) (xs rev flag : List Bool) :
    StackRuns (code peer) (2*xs.length+3) (.rest b) (bank xs [] rev flag)
      .done (bank [] [] (if peer then xs.reverse ++ rev else rev) ((peer || b) :: flag)) := by
  induction xs generalizing rev with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.nil_append, ite_self]
    scan_step
    exact clear_run peer _ 0 _ _
  | cons c xs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    scan_step
    cases peer <;> simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢ <;> scan_step <;> exact ih _

theorem scan_run (peer : Bool) (j : ℕ) (xs rev flag : List Bool) :
    ∃ t ≤ 3*xs.length+j+3, StackRuns (code peer) t .scan (bank xs (List.replicate j true) rev flag)
      .done (bank [] [] (if peer then (flip j xs).reverse ++ rev else rev)
        ((if peer then decide (j < xs.length) else read j xs) :: flag)) := by
  induction xs generalizing j rev with
  | nil =>
    refine ⟨(j+2)+1, by simp, ?_⟩
    simp only [flip, read, List.length_nil, List.reverse_nil, List.nil_append, ite_self, Nat.not_lt_zero,
      decide_false]
    scan_step
    exact clear_run peer false j rev flag
  | cons c xs ih =>
    cases j with
    | zero =>
      refine ⟨2*xs.length+3+3, by simp; omega, ?_⟩
      simp only [read, flip, List.length_cons, Nat.zero_lt_succ, decide_true, List.reverse_cons,
        List.append_assoc, List.singleton_append]
      scan_step
      scan_step
      cases peer <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> scan_step
      · simpa using rest_run false c xs rev flag
      · simpa using rest_run true c xs ((!c)::rev) flag
    | succ j =>
      let out := if peer then c :: rev else rev
      obtain ⟨t, ht, h⟩ := ih j out
      refine ⟨t+3, by simp; omega, ?_⟩
      simp only [read, flip, List.length_cons, Nat.succ_lt_succ_iff, List.reverse_cons,
        List.append_assoc, List.singleton_append]
      scan_step
      scan_step
      cases peer <;> simp only [out, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> scan_step <;> exact h

/-- Read the requested bit with zero extension, or in peer mode toggle it when present and
produce the reversed partner bits and local-stride flag. -/
def routine (peer : Bool) : FiniteRoutine Port :=
  FiniteRoutine.ofStackCode (code peer) id .scan (· == .done)

theorem runs (peer : Bool) (j : ℕ) (xs : List Bool) :
    ∃ t ≤ 3*xs.length+j+3, (routine peer).Runs t (bank xs (List.replicate j true) [] [])
      (bank [] [] (if peer then (flip j xs).reverse else [])
        [if peer then decide (j < xs.length) else (value xs).testBit j]) := by
  obtain ⟨t, ht, run⟩ := scan_run peer j xs [] []
  simp only [List.append_nil, read_value] at run
  refine ⟨t, ht, ?_⟩
  exact FiniteRoutine.runs_ofStackCode_framed Function.injective_id rfl rfl
    (fun q h => by simp only [beq_iff_eq] at h; subst q; rfl) run (fun _ => rfl) (fun _ => rfl)
    (fun k h => (h k rfl).elim)

end RAMTape.SortRowAddress.IndexScan

end VPVNP
end Computability
end OAI
