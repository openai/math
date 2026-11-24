import OAI.Computability.VPVNP.UniversalCountStackBounds
import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.LiveHeaderBits

/-!
# Prepending the equation address to a packed scalar query

The index register and the row field of the scalar query can have different
widths. The length of an immutable unary template selects the low bits to
prepend. A missing high bit is copied as zero. The two scratch stacks allow
the source to be restored and the bits to be emitted in little-endian order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar.RowPrefix

open RAMTape UniversalCountStack BurstRAM

set_option backward.isDefEq.respectTransparency false in
/-- Stacks for the source equation address, unary output width, destination and two temporary
bit sequences. -/
inductive Port where | source | width | dst | saved | staged deriving DecidableEq, Fintype

/-- Control states for staging the low address bits, restoring the source and emitting the
resized row prefix. -/
inductive Phase where
  | scan | read | save (b : Bool) | stage (b : Bool) | restore | replace (b : Bool)
  | flush | emit (b : Bool) | mark
  deriving DecidableEq, Fintype

private def code (marker : Bool) : Routine Port Phase where
  entry := .scan
  code
    | .scan => .pop .width fun b => some (if b.isSome then .read else .restore)
    | .read => .pop .source fun b => some (b.elim (.stage false) .save)
    | .save b => .push .saved b (some (.stage b))
    | .stage b => .push .staged b (some .scan)
    | .restore => .pop .saved fun b => some (b.elim .flush .replace)
    | .replace b => .push .source b (some .restore)
    | .flush => .pop .staged (Option.map .emit)
    | .emit b => .push .dst b (some .mark)
    | .mark => .push .width marker (some .flush)

/-- Prepend the equation address at the width specified by the unary template, restoring the
source and template on return. -/
def body (marker : Bool) : FiniteRoutine Port := .ofRoutine (code marker)

/-- Assign the equation address, width template, destination and both temporary sequences to
their respective stacks. -/
def bank (row width dst saved staged : List Bool) : Stacks Port
  | .source => row | .width => width | .dst => dst | .saved => saved | .staged => staged

private theorem update_bank (x w y a b v : List Bool) (p : Port) :
    Function.update (bank x w y a b) p v = match p with
      | .source => bank v w y a b | .width => bank x v y a b | .dst => bank x w v a b
      | .saved => bank x w y v b | .staged => bank x w y a v := by
  funext j; cases p <;> cases j <;> rfl

local macro "row_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [bank, update_bank, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
    Option.isSome_none, Option.isSome_some, Option.elim_none, Option.elim_some, Option.map_none,
    Option.map_some, Bool.false_eq_true, ite_false, ite_true])

/-- Take the requested number of low bits from a little-endian word, filling any missing high
bits with zero. -/
def resize : ℕ → List Bool → List Bool
  | 0, _ => []
  | n+1, xs => xs.headD false :: resize n xs.tail

@[simp] theorem resize_length (n : ℕ) (xs : List Bool) : (resize n xs).length = n := by
  induction n generalizing xs <;> simp [resize, *]

private theorem resize_get (n : ℕ) (xs : List Bool) (i : ℕ) (hi : i < n) :
    (resize n xs)[i]'(by simpa using hi) = xs[i]?.getD false := by
  induction n generalizing xs i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => cases xs <;> rfl
    | succ i =>
      change (resize n xs.tail)[i]'(by rw [resize_length]; omega) = _
      rw [ih _ _ (by omega)]
      cases xs <;> rfl

/-- Canonical physical little-endian digits of an integer at any width. -/
theorem digits_ofFn (r i : ℕ) : digits r i = List.ofFn (fun j : Fin r => i.testBit j.val) := by
  apply congrArg List.ofFn
  funext j
  rw [← LiveHeader.testBit_wordBits]
  simp [j.isLt]

/-- Resize the low-bit array of a natural number. The source must represent
the number. The result is the canonical low target-width word even on truncation. -/
theorem resize_digits (target wr i : ℕ) (hi : i < 2^wr) : resize target (digits wr i) = digits target i := by
  rw [digits_ofFn, digits_ofFn]
  apply List.ext_getElem (by simp)
  intro j hj _
  rw [resize_get _ _ _ (by simpa using hj), List.getElem_ofFn]
  by_cases h : j < wr
  · rw [List.getElem?_eq_getElem (by simpa using h), List.getElem_ofFn]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega)]
    exact (Nat.testBit_lt_two_pow (hi.trans_le (Nat.pow_le_pow_right (by decide) (by omega : wr ≤ j)))).symm

private theorem scan (marker : Bool) (n : ℕ) (xs y a b : List Bool) :
    ∃ ticks ≤ 4*n, StackRuns (code marker).standalone ticks (some .scan)
      (bank xs (List.replicate n marker) y a b) (some .scan)
      (bank (xs.drop n) [] y ((xs.take n).reverse ++ a) ((resize n xs).reverse ++ b)) := by
  induction n generalizing xs a b with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simpa [resize] using StackRuns.nil (code := (code marker).standalone) (some Phase.scan) (bank xs [] y a b)
  | succ n ih =>
    cases xs with
    | nil =>
      obtain ⟨ticks, ht, run⟩ := ih [] a (false :: b)
      refine ⟨ticks+3, by omega, ?_⟩
      simp only [List.replicate_succ, resize, List.headD_nil, List.tail_nil, List.take_nil, List.drop_nil,
        List.reverse_nil, List.nil_append, List.reverse_cons, List.append_assoc, List.singleton_append]
      row_step
      row_step
      row_step
      simpa using run
    | cons x xs =>
      obtain ⟨ticks, ht, run⟩ := ih xs (x :: a) (x :: b)
      refine ⟨ticks+4, by omega, ?_⟩
      simp only [List.replicate_succ, resize, List.headD_cons, List.tail_cons, List.take_succ_cons,
        List.drop_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
      row_step
      row_step
      row_step
      row_step
      exact run

private theorem restore (marker : Bool) (xs y a b : List Bool) :
    StackRuns (code marker).standalone (2*a.length+1) (some .restore) (bank xs [] y a b)
      (some .flush) (bank (a.reverse ++ xs) [] y [] b) := by
  induction a generalizing xs with
  | nil => row_step; exact .nil ..
  | cons u a ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    row_step
    row_step
    exact ih (u::xs)

private theorem flush (marker : Bool) (xs y b : List Bool) (markers : ℕ) :
    StackRuns (code marker).standalone (3*b.length+1) (some .flush)
      (bank xs (List.replicate markers marker) y [] b) none
      (bank xs (List.replicate (markers+b.length) marker) (b.reverse ++ y) [] []) := by
  induction b generalizing y markers with
  | nil => row_step; exact .nil ..
  | cons u b ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    row_step
    row_step
    row_step
    simpa only [List.replicate_succ, Nat.succ_add, Nat.add_succ] using ih (u::y) (markers+1)

/-- All input stacks are restored. Only the destination gains bits. -/
theorem runs (marker : Bool) (target wr i : ℕ) (hi : i < 2^wr) (dst : List Bool) :
    ∃ ticks ≤ 9*target+3, (body marker).Runs ticks
      (bank (digits wr i) (List.replicate target marker) dst [] [])
      (bank (digits wr i) (List.replicate target marker) (digits target i ++ dst) [] []) := by
  let xs := digits wr i
  let a := (xs.take target).reverse
  let b := (resize target xs).reverse
  obtain ⟨n, hn, first⟩ := scan marker target xs dst [] []
  simp only [List.append_nil] at first
  have hrest : StackRuns (code marker).standalone (2*a.length+1+1) (some .scan)
      (bank (xs.drop target) [] dst a b) (some .flush) (bank xs [] dst [] b) := by
    row_step
    simpa [a] using restore marker (xs.drop target) dst a b
  have final := (first.trans hrest).trans (flush marker xs dst b 0)
  have ha : a.length ≤ target := by simp [a]
  have hb : b.length = target := by simp [b]
  refine ⟨n + (2*a.length+1+1) + (3*b.length+1), by omega, ?_⟩
  change StackRuns (code marker).standalone _ (some .scan) _ none _
  simpa only [b, List.replicate_zero, Nat.zero_add, List.reverse_reverse, List.length_reverse,
    resize_length, xs, resize_digits target wr i hi, length_digits] using final

end JointScalar.RowPrefix

end VPVNP
end Computability
end OAI
