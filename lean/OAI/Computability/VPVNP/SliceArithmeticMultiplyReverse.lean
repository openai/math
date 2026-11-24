import OAI.Computability.VPVNP.SliceArithmeticStreamWord
import OAI.Computability.VPVNP.SliceArithmeticLoop

/-!
# Preparing the digit and accumulator streams for Horner multiplication

A marker for each coefficient controls one load of the next input word,
followed by an order-preserving store onto the digit stack and a store of
one zero word onto the accumulator. Thus the highest-degree coefficient is
the first Horner digit, while each limb retains its little-endian encoding.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticMultiplyReverse

open BurstRAM RAMTape SliceArithmetic.StreamWord

set_option backward.isDefEq.respectTransparency false in
/-- Operand, digit, accumulator, marker, and word-copy ports for preparing the Horner input
order. -/
inductive Port where
  | query | digits | old | marker | staging | zero | scratch
  deriving DecidableEq, Fintype

private def copyOne : FiniteRoutine Port :=
  ((load .query .staging .scratch).followedBy (store .digits .staging .scratch)).followedBy
    (store .old .zero .scratch)

/-- The final store and load use the unconsumed query suffix to reset the
staging register. Both operations leave this suffix in its original place. -/
def prepare : FiniteRoutine Port :=
  ((FiniteRoutine.repeatMarked .marker copyOne).followedBy (store .query .zero .scratch)).followedBy
    (load .query .staging .scratch)

/-- Concatenate the little-endian bit encodings of a list of equal-width words in list order. -/
def pack {w : ℕ} (words : List (Word w)) : List Bool := words.flatMap wordBits

/-- State of the digit-order conversion with the remaining query, prepared digits, zero
accumulator, marker count, and staging word. -/
def frame {w : ℕ} (query digits old : List Bool) (markers : ℕ) (staging : Word w) : Stacks Port
  | .query => query
  | .digits => digits
  | .old => old
  | .marker => List.replicate markers true
  | .staging => wordBits staging
  | .zero => wordBits (0 : Word w)
  | .scratch => []

private theorem copyOne_runs {w : ℕ} (x staging : Word w) (tail digits old : List Bool) (markers : ℕ) :
    copyOne.Runs (15*w + 6) (frame (wordBits x ++ tail) digits old markers staging)
      (frame tail (wordBits x ++ digits) (wordBits (0 : Word w) ++ old) markers x) := by
  let s := frame (wordBits x ++ tail) digits old markers staging
  let s₁ := frame tail digits old markers x
  let s₂ := frame tail (wordBits x ++ digits) old markers x
  let s₃ := frame tail (wordBits x ++ digits) (wordBits (0 : Word w) ++ old) markers x
  have h₁ := load_runs (stream := Port.query) (reg := .staging) (scratch := .scratch)
    (by decide) (by decide) (by decide) s x tail (length_wordBits staging) rfl rfl
  have h₂ := store_runs (stream := Port.digits) (reg := .staging) (scratch := .scratch)
    (by decide) (by decide) (by decide) s₁ x rfl rfl
  have h₃ := store_runs (stream := Port.old) (reg := .zero) (scratch := .scratch)
    (by decide) (by decide) (by decide) s₂ (0 : Word w) rfl rfl
  rw [show Function.update (Function.update s .query tail) .staging (wordBits x) = s₁ by
    funext i; cases i <;> simp [s, s₁, frame]] at h₁
  rw [show Function.update s₁ .digits (wordBits x ++ s₁ .digits) = s₂ by
    funext i; cases i <;> simp [s₁, s₂, frame]] at h₂
  rw [show Function.update s₂ .old (wordBits (0 : Word w) ++ s₂ .old) = s₃ by
    funext i; cases i <;> simp [s₂, s₃, frame]] at h₃
  rw [show 15*w + 6 = (5*w + 2 + (5*w + 2)) + (5*w + 2) by omega]
  exact (h₁.followedBy h₂).followedBy h₃

private theorem copyLoop_runs {w : ℕ} (words : List (Word w)) (tail digits old : List Bool) (staging : Word w) :
    (FiniteRoutine.repeatMarked .marker copyOne).Runs (words.length * (15*w + 7) + 1)
      (frame (pack words ++ tail) digits old words.length staging)
      (frame tail (pack words.reverse ++ digits) (pack (List.replicate words.length (0 : Word w)) ++ old)
        0 (words.getLastD staging)) := by
  induction words generalizing digits old staging with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, List.reverse_nil, List.getLastD_nil,
      pack, List.flatMap_nil, List.nil_append, List.replicate_zero]
    exact Routine.Runs.popLoop_empty .marker (fun _ => true) (Routine.halt false) copyOne.body
      (s := frame tail digits old 0 staging) rfl
  | cons x words ih =>
    let query := pack words ++ tail
    let s := frame (wordBits x ++ query) digits old (words.length + 1) staging
    have hs : Function.update s .marker (List.replicate words.length true) =
        frame (wordBits x ++ query) digits old words.length staging := by
      funext i; cases i <;> simp [s, frame]
    have step := copyOne_runs x staging query digits old words.length
    rw [← hs] at step
    have tailRun := ih (wordBits x ++ digits) (wordBits (0 : Word w) ++ old) x
    change (Routine.popLoop Port.marker (fun _ => true) (Routine.halt false) copyOne.body).Runs _ _ _ at tailRun
    have run := Routine.Runs.popLoop_true_continue Port.marker (fun _ => true) (Routine.halt false) copyOne.body
      (s := s) (by simp [s, frame, List.replicate_succ]) rfl step tailRun
    rw [List.length_cons, Nat.succ_mul words.length]
    change (FiniteRoutine.repeatMarked .marker copyOne).Runs _ _ _ at run
    rw [show words.length * (15*w+7) + (15*w+7) + 1 = 1 + (15*w+6) + (words.length*(15*w+7)+1) by omega]
    rw [List.getLastD_cons]
    simpa [s, query, pack, List.replicate_succ', List.flatMap_append] using run

/-- Exact bit-stack execution for the query preparation. The three streams can
have arbitrary suffixes, and the staging register returns to the zero word. -/
theorem prepare_runs {w : ℕ} (words : List (Word w)) (tail digits old : List Bool) (staging : Word w) :
    prepare.Runs (words.length * (15*w + 7) + 1 + (10*w + 4))
      (frame (pack words ++ tail) digits old words.length staging)
      (frame tail (pack words.reverse ++ digits) (pack (List.replicate words.length (0 : Word w)) ++ old) 0 (0 : Word w)) := by
  let ds := pack words.reverse ++ digits
  let zs := pack (List.replicate words.length (0 : Word w)) ++ old
  let s := frame tail ds zs 0 (words.getLastD staging)
  let middle := frame (wordBits (0 : Word w) ++ tail) ds zs 0 (words.getLastD staging)
  have scan := copyLoop_runs words tail digits old staging
  have save := store_runs (stream := Port.query) (reg := .zero) (scratch := .scratch)
    (by decide) (by decide) (by decide) s (0 : Word w) rfl rfl
  have reset := load_runs (stream := Port.query) (reg := .staging) (scratch := .scratch)
    (by decide) (by decide) (by decide) middle (0 : Word w) tail (length_wordBits _) rfl rfl
  rw [show Function.update s .query (wordBits (0 : Word w) ++ s .query) = middle by
    funext i; cases i <;> simp [s, middle, frame]] at save
  rw [show Function.update (Function.update middle .query tail) .staging (wordBits (0 : Word w)) =
      frame tail ds zs 0 (0 : Word w) by funext i; cases i <;> simp [middle, frame]] at reset
  rw [show words.length * (15*w + 7) + 1 + (10*w + 4) =
    (words.length * (15*w + 7) + 1 + (5*w + 2)) + (5*w + 2) by omega]
  exact (scan.followedBy save).followedBy reset

end SliceArithmeticMultiplyReverse

end VPVNP
end Computability
end OAI
