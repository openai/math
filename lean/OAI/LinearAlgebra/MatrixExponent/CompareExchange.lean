import OAI.LinearAlgebra.MatrixExponent.FunctionNetwork
import Mathlib.Data.Prod.Lex

/-!
# A linear-size compare-and-exchange network on words

Comparison folds a single bit of state up the word. Selection copies that bit
to all positions, then multiplexes them in parallel. This avoids paying for
identity on a shrinking word at each step of a sequential selection.
-/

namespace OAI.LinearAlgebra.MatrixExponent

@[simp] theorem wd_word (n : ℕ) : wd (word n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wd, ih, Nat.add_comm]

/-- Lexicographic order with the first bit most significant. -/
instance wordOrder : (n : ℕ) → LinearOrder (Val (word n))
  | 0 => inferInstanceAs (LinearOrder Unit)
  | n + 1 => @Prod.Lex.instLinearOrder Bool (Val (word n)) _ (wordOrder n)

private theorem word_lt_succ (n : ℕ) (x y : Val (word (n + 1))) :
    @LT.lt _ (wordOrder (n + 1)).toLT x y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2 := by
  exact Prod.Lex.toLex_lt_toLex (x := x) (y := y)

variable (F : Type) [Field F]

private abbrev two := Wire.pair .bit .bit

private theorem selectBit :
    DNet F (.pair two .bit) .bit (fun x => if x.2 then x.1.1 else x.1.2) 6 := by
  have dup := ((DNet.id F two).par (DNet.dup F .bit)).post (.middle .bit .bit .bit .bit)
  have yes := DNet.table F two .bit (fun x => x.1 && x.2) (by decide)
  have no := DNet.table F two .bit (fun x => x.1 && !x.2) (by decide)
  have join := DNet.table F two .bit (fun x => x.1 || x.2) (by decide)
  convert (dup.comp (yes.par no)).comp join using 1 <;> try rfl
  funext ⟨⟨p, q⟩, b⟩
  cases b <;> simp

/-- Evaluate both two-input branches and select with the third bit. -/
private theorem ternary (f : Val (.pair two .bit) → Bool) :
    DNet F (.pair two .bit) .bit f 11 := by
  have branch (b : Bool) := DNet.table F two .bit (fun x => f (x, b)) (by decide)
  convert (((branch true).pair (branch false)).par (DNet.id F .bit)).comp (selectBit F) using 1 <;> try rfl
  funext ⟨x, b⟩
  cases b <;> rfl

/-- A strict comparator using a linear number of trivalent vertices. -/
theorem compare_lt (n : ℕ) :
    DNet F (.pair (word n) (word n)) .bit (fun x => decide (x.1 < x.2)) (100 * (n + 1)) := by
  induction n with
  | zero => exact (DNet.table F _ _ _ (by decide)).mono (by decide)
  | succ n ih =>
    have step := ternary F (fun x => decide (x.1.1 < x.1.2 ∨ x.1.1 = x.1.2 ∧ x.2 = true))
    have h := (((DNet.id F two).par ih).pre (.middle .bit (word n) .bit (word n))).comp step
    convert h.mono (n := 100 * (n + 1 + 1)) (by simp only [wd]; omega) using 1
    funext ⟨x, y⟩
    simp only [decide_eq_true_eq, decide_eq_decide]
    exact word_lt_succ n x y

private def repeatBit : (n : ℕ) → Bool → Val (word n)
  | 0, _ => ()
  | n + 1, b => (b, repeatBit n b)

private theorem broadcast (n : ℕ) : DNet F .bit (word n) (repeatBit n) (2 * n + 1) := by
  induction n with
  | zero => exact DNet.discard F .bit
  | succ n ih => exact ((DNet.id F .bit).pair ih).mono (by simp only [wd]; omega)

private def selectBits : (n : ℕ) → Val (word n) → Val (word n) → Val (word n) → Val (word n)
  | 0, _, _, _ => ()
  | n + 1, x, y, mask =>
    (if mask.1 then x.1 else y.1, selectBits n x.2 y.2 mask.2)

private theorem selectBits_repeat (n : ℕ) (x y : Val (word n)) (b : Bool) :
    selectBits n x y (repeatBit n b) = if b then x else y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [selectBits, repeatBit, ih]; cases b <;> rfl

private abbrev inputs (n : ℕ) := Wire.pair (word n) (word n)

private theorem selectParallel (n : ℕ) :
    DNet F (.pair (inputs n) (word n)) (word n)
      (fun x => selectBits n x.1.1 x.1.2 x.2) (6 * n + 1) := by
  induction n with
  | zero => exact DNet.table F _ _ _ (by decide)
  | succ n ih =>
    have r := ((Rewire.middle .bit (word n) .bit (word n)).par (Rewire.id (word (n + 1)))).comp
      (Rewire.middle two (inputs n) .bit (word n))
    exact (((selectBit F).par ih).pre r).mono (by omega)

theorem selectWord (n : ℕ) :
    DNet F (.pair (inputs n) .bit) (word n)
      (fun x => if x.2 then x.1.1 else x.1.2) (10 * n + 2) := by
  have h := ((DNet.id F (inputs n)).par (broadcast F n)).comp (selectParallel F n)
  simpa only [selectBits_repeat] using
    h.mono (n := 10 * n + 2) (by simp only [wd, wd_word]; omega)

/-- Order the two words while retaining both of them. -/
theorem compare_exchange (n : ℕ) :
    DNet F (.pair (word n) (word n)) (.pair (word n) (word n))
      (fun x => (min x.1 x.2, max x.1 x.2)) (200 * (n + 1)) := by
  have compare := (DNet.id F (inputs n)).pair (compare_lt F n)
  have lower := selectWord F n
  have upper := lower.pre ((Rewire.swap (word n) (word n)).par (.id .bit))
  have h := compare.comp (lower.pair upper)
  convert h.mono (n := 200 * (n + 1)) (by simp only [wd, wd_word]; omega) using 1
  funext ⟨x, y⟩
  by_cases hxy : x < y
  · simp [hxy, min_eq_left hxy.le, max_eq_right hxy.le]
  · simp [hxy, min_eq_right (le_of_not_gt hxy), max_eq_left (le_of_not_gt hxy)]

end OAI.LinearAlgebra.MatrixExponent
