import OAI.Computability.VPVNP.RAMTapeWordSimple
import OAI.Computability.VPVNP.RAMTapeStackLift

/-!
# Conditional jumps on staged RAM words

The equality scan remembers whether all pairs of bits have agreed so far.
For an unsigned less-than test, the subtraction scan's final borrow gives
the answer. The machine clears the emitted word before returning, keeping
the branch bit in finite control. The two staged inputs may contain copies
of the same register.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.Comparison

open RAMTape BurstRAM

/-- Equality and unsigned less-than operations used by word-RAM conditional branches. -/
inductive Op where
  | eq | lt
  deriving DecidableEq

/-- Initialize the equality flag to true or the subtraction borrow to false. -/
def Op.initial : Op → Bool
  | .eq => true
  | .lt => false

/-- Update the equality flag and emit zero, or perform a subtraction bit step to update the
less-than borrow. -/
def Op.step : Op → Bool → Bool → Bool → Bool × Bool
  | .eq => fun c x y => (false, c && (x == y))
  | .lt => subBit

/-- Evaluate the selected equality or unsigned less-than test directly on two fixed-width
words. -/
def Op.eval {w : ℕ} : Op → Word w → Word w → Bool
  | .eq, a, b => decide (a = b)
  | .lt, a, b => decide (a < b)

/-- Control states for executing the comparison bit scan and returning its branch decision. -/
inductive State where
  | scan (q : ScanState) | done (branch : Bool)
  deriving DecidableEq, Fintype

/-- Install the word scan, using its terminal flag while draining the output. -/
def code (op : Op) : StackCode ScanPort State
  | .scan (.done f) => .pop .out fun b => b.elim (.done f) fun _ => .scan (.done f)
  | .scan q => (scanCode op.step q).rename id State.scan
  | .done _ => .halt true

private theorem eq_flag (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (TapeWord.scan Op.eq.step c xs ys).2 = (c && decide (xs = ys)) := by
  induction xs generalizing c ys with
  | nil =>
    have hnil : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    simp [TapeWord.scan]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [TapeWord.scan, ih _ ys (Nat.succ.inj hlen)]
      cases x <;> cases y <;> simp [Op.step]

private theorem flag {w : ℕ} (op : Op) (a b : Word w) :
    (TapeWord.scan op.step op.initial (wordBits a) (wordBits b)).2 = op.eval a b := by
  have hlen : (wordBits a).length = (wordBits b).length := by simp
  cases op with
  | eq =>
    have he : wordBits a = wordBits b ↔ a = b := by
      refine ⟨fun h => Fin.ext ?_, congrArg wordBits⟩
      simpa only [value_wordBits] using congrArg value h
    simp [eq_flag _ _ _ hlen, Op.initial, Op.eval, he]
  | lt =>
    apply Bool.eq_iff_iff.mpr
    change (subScan false (wordBits a) (wordBits b)).2 = true ↔ decide (a.val < b.val) = true
    simpa only [value_wordBits, Bool.toNat_false, Nat.add_zero, decide_eq_true_eq] using
      subScan_borrow (c := false) hlen

private theorem install_id (base small : Stacks ScanPort) : installStacks id base small = small := by
  funext i
  exact installStacks_at Function.injective_id base small i

private theorem drain (op : Op) (f : Bool) (out : List Bool) :
    StackRuns (code op) (out.length + 1) (.scan (.done f)) (scanStacks [] [] [] out)
      (.done f) (scanStacks [] [] [] []) := by
  have updateOut (x y : List Bool) : Function.update (scanStacks [] [] [] x) .out y =
      scanStacks [] [] [] y := by funext p; cases p <;> simp [scanStacks]
  induction out with
  | nil =>
    refine .cons (.pop rfl) ?_
    simp only [scanStacks, List.head?_nil, List.tail_nil, Option.elim_none, updateOut]
    exact .nil ..
  | cons b out ih =>
    refine .cons (.pop rfl) ?_
    simp only [scanStacks, List.head?_cons, List.tail_cons, Option.elim_some, updateOut]
    exact ih

/-- From two operand copies, return the exact conditional-jump decision and
empty all four ports in a width-independent control. -/
theorem word_run {w : ℕ} (op : Op) (a b : Word w) :
    StackRuns (code op) (6 * w + 3) (.scan (.left op.initial))
      (scanStacks (wordBits a) (wordBits b) [] [])
      (.done (op.eval a b)) (scanStacks [] [] [] []) := by
  have hlen : (wordBits a).length = (wordBits b).length := by simp
  let u := TapeWord.scan op.step op.initial (wordBits a) (wordBits b)
  have hs := scanRuns op.step op.initial (wordBits a) (wordBits b) [] hlen
  have rows (q : ScanState) (h : (scanCode op.step q).returns = false) :
      code op (.scan q) = (scanCode op.step q).rename id State.scan := by
    cases q <;> first | rfl | contradiction
  have run := hs.lift id Function.injective_id State.scan (fun _ => []) rows
  simp only [install_id, length_wordBits, List.append_nil, flag] at run
  have hw : u.1.length = w := (length_scan op.step op.initial _ _ hlen).trans (length_wordBits a)
  have clear := drain op (op.eval a b) u.1
  rw [hw] at clear
  convert run.trans clear using 1
  omega

end TapeWord.Comparison

end VPVNP
end Computability
end OAI
