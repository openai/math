import OAI.Computability.VPVNP.RAMTapeWordScan

/-!
# Loading register, public-word and fixed-literal operands

A finite-state scan copies one bit per source cell, restoring the original
word and overwriting the destination. Its finite output transition may copy
the input bits unchanged, or ignore them and emit the low bits of a fixed
literal. In the latter case the source supplies only the word width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.Operand

open RAMTape BurstRAM

/-- Control for clearing the destination, scanning a source word with a finite bit
transformation, and restoring the source. -/
inductive State (A : Type*)
  | clear (a : A) | read (a : A) | save (b out : Bool) (a : A) | emit (out : Bool) (a : A)
  | restore (a : A) | takeOut (b : Bool) (a : A) | putSrc (b out : Bool) (a : A)
  | putOut (out : Bool) (a : A) | done (a : A) | reject
  deriving DecidableEq, Fintype

variable {A : Type*}

/-- Load an operand word using the given bit transition, overwrite the destination and restore
the source in its original order. -/
def code (step : A → Bool → Bool × A) : StackCode ScanPort (State A)
  | .clear a => .pop .out fun b => b.elim (.read a) fun _ => .clear a
  | .read a => .pop .left fun b => b.elim (.restore a) fun x => .save x (step a x).1 (step a x).2
  | .save b out a => .push .right b (.emit out a)
  | .emit out a => .push .tmp out (.read a)
  | .restore a => .pop .right fun b => b.elim (.done a) fun x => .takeOut x a
  | .takeOut b a => .pop .tmp fun d => d.elim .reject fun x => .putSrc b x a
  | .putSrc b out a => .push .left b (.putOut out a)
  | .putOut out a => .push .out out (.restore a)
  | .done _ => .halt true
  | .reject => .halt false

/-- Output bit list and final finite state obtained by applying the operand transformation once
per input bit. -/
def emitted (step : A → Bool → Bool × A) : A → List Bool → List Bool × A
  | a, [] => ([], a)
  | a, b :: xs =>
    let (out, next) := step a b
    let (rest, final) := emitted step next xs
    (out :: rest, final)

private theorem emitted_length (step : A → Bool → Bool × A) (a : A) (xs : List Bool) :
    (emitted step a xs).1.length = xs.length := by
  induction xs generalizing a with
  | nil => rfl
  | cons _ _ ih => simp [emitted, ih]

private theorem update_stacks (x s t o word : List Bool) (k : ScanPort) :
    Function.update (scanStacks x s t o) k word = match k with
      | .left => scanStacks word s t o
      | .right => scanStacks x word t o
      | .tmp => scanStacks x s word o
      | .out => scanStacks x s t word := by
  funext j; cases k <;> cases j <;> simp [scanStacks]

local macro "operand_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [scanStacks, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, update_stacks])

private theorem clear_run (step : A → Bool → Bool × A) (a : A) (x s t o : List Bool) :
    StackRuns (code step) (o.length + 1) (.clear a) (scanStacks x s t o) (.read a) (scanStacks x s t []) := by
  induction o with
  | nil => operand_step; exact .nil ..
  | cons b o ih => operand_step; exact ih

private theorem read_run (step : A → Bool → Bool × A) (a : A) (x s t o : List Bool) :
    StackRuns (code step) (3 * x.length + 1) (.read a) (scanStacks x s t o)
      (.restore (emitted step a x).2) (scanStacks [] (x.reverse ++ s) ((emitted step a x).1.reverse ++ t) o) := by
  induction x generalizing a s t with
  | nil => operand_step; exact .nil ..
  | cons b x ih =>
    simp only [List.length_cons, Nat.mul_succ, emitted, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    operand_step
    operand_step
    operand_step
    exact ih _ _ _

private theorem restore_run (step : A → Bool → Bool × A) (a : A) (x s t o : List Bool)
    (hlen : s.length = t.length) :
    StackRuns (code step) (4 * s.length + 1) (.restore a) (scanStacks x s t o)
      (.done a) (scanStacks (s.reverse ++ x) [] [] (t.reverse ++ o)) := by
  induction s generalizing x t o with
  | nil =>
    have ht : t = [] := List.length_eq_zero_iff.mp hlen.symm
    subst t
    operand_step
    exact .nil ..
  | cons b s ih =>
    cases t with
    | nil => simp at hlen
    | cons d t =>
      simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      operand_step
      operand_step
      operand_step
      operand_step
      exact ih _ _ _ (Nat.succ.inj hlen)

/-- The source is preserved, the destination is overwritten, and both
scratch stacks are empty on return. -/
theorem run (step : A → Bool → Bool × A) (a : A) (x old : List Bool) :
    StackRuns (code step) (old.length + 7 * x.length + 3) (.clear a) (scanStacks x [] [] old)
      (.done (emitted step a x).2) (scanStacks x [] [] (emitted step a x).1) := by
  have hc := clear_run step a x [] [] old
  have hr := read_run step a x [] [] []
  simp only [List.append_nil] at hr
  have hs := restore_run step (emitted step a x).2 [] x.reverse (emitted step a x).1.reverse []
    (by simp [emitted_length])
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hs
  convert (hc.trans hr).trans hs using 1
  omega

/-- Load any saved word from a register, the persistent input, or public data. -/
def copyBit (_ : Unit) (b : Bool) : Bool × Unit := (b, ())

private theorem emitted_copy (x : List Bool) : emitted copyBit () x = (x, ()) := by
  induction x <;> simp [emitted, copyBit, *]

theorem copy_run (x old : List Bool) :
    StackRuns (code copyBit) (old.length + 7 * x.length + 3) (.clear ()) (scanStacks x [] [] old)
      (.done ()) (scanStacks x [] [] x) := by simpa [emitted_copy] using run copyBit () x old

/-- A fixed literal is compiled into a finite family of control states for
its successively halved values. Word width affects only the input stack. -/
def literalBit (k : ℕ) (a : Fin (k + 1)) (_ : Bool) : Bool × Fin (k + 1) :=
  (decide (a.val % 2 = 1), ⟨a.val / 2, (Nat.div_le_self _ _).trans_lt a.isLt⟩)

private theorem emitted_literal (k : ℕ) (a : Fin (k + 1)) (x : List Bool) :
    value (emitted (literalBit k) a x).1 + 2^x.length * (emitted (literalBit k) a x).2.val = a.val := by
  induction x generalizing a with
  | nil => simp [emitted, value]
  | cons b x ih =>
    have h := ih (literalBit k a b).2
    have hl : (literalBit k a b).1.toNat = a.val % 2 := by
      by_cases hz : a.val % 2 = 1 <;> simp [literalBit, hz]
      omega
    simp only [emitted, value, hl, List.length_cons, pow_succ, Nat.mul_right_comm _ 2 _]
    change _ + _ = a.val / 2 at h
    omega

/-- Load a width-dependent residue of a fixed constant. -/
theorem literal_run {w : ℕ} (k : ℕ) (widthTemplate : Word w) (old : List Bool) :
    ∃ final : Fin (k + 1), StackRuns (code (literalBit k)) (old.length + 7*w + 3)
      (.clear (Fin.last k)) (scanStacks (wordBits widthTemplate) [] [] old) (.done final)
      (scanStacks (wordBits widthTemplate) [] [] (wordBits (Fin.ofNat (2^w) k))) := by
  let x := wordBits widthTemplate
  let a := Fin.last k
  let z := emitted (literalBit k) a x
  have hx : x.length = w := length_wordBits _
  have hz : z.1.length = w := (emitted_length _ _ _).trans hx
  have hv := emitted_literal k a x
  change value z.1 + 2^x.length * z.2.val = k at hv
  have hlo := value_lt z.1
  rw [hz] at hlo
  have he : z.1 = wordBits (Fin.ofNat (2^w) k) := by
    apply eq_of_length_value (by simpa using hz)
    have hm := congrArg (fun n => n % 2^w) hv
    simpa only [value_wordBits, Fin.val_ofNat, hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo] using hm
  refine ⟨z.2, ?_⟩
  have hr := run (literalBit k) a x old
  change StackRuns _ _ (State.clear a) (scanStacks x [] [] old) (State.done z.2) (scanStacks x [] [] z.1) at hr
  simpa only [hx, he] using hr

end TapeWord.Operand

end VPVNP
end Computability
end OAI
