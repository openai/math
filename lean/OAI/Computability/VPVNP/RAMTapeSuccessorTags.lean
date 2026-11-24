import OAI.Computability.VPVNP.RAMTapeStacks
import OAI.Computability.VPVNP.RAMTapeWord
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# Scanning the small integer tags of a successor message

Status and record-kind words use the values zero through three. Scanning a
little-endian word, the control remembers its low two bits and tests whether
any higher bit is set. The same scan tests whether a padding or clamp word
is zero. It works on arbitrary lists, including empty and malformed words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorTags

open TapeWord

/-- Successor word classes for unsigned values zero through three and values at least four. -/
inductive Tag where
  | zero | one | two | three | large
  deriving DecidableEq

instance : Fintype Tag := derive_fintype% _

/-- The enumeration maps all values of at least four to its final constructor. -/

theorem Tag.ofNat_large {n : ℕ} (h : 4 ≤ n) : Tag.ofNat n = .large := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]
  rfl

/-- States for remembering the low two bits and detecting set higher bits during a
little-endian tag scan. -/
inductive State where
  | first
  | second (low : Bool)
  | high (tag : Tag)
  | done (tag : Tag)
  deriving DecidableEq, Fintype

/-- The transition on one actual bit. -/
def advance : State → Bool → State
  | .first, b => .second b
  | .second low, b => .high (Tag.ofNat (low.toNat + 2 * b.toNat))
  | .high t, b => .high (if b then .large else t)
  | .done t, _ => .done t

/-- The tag when the source word has been exhausted. -/
def finish : State → Tag
  | .first => .zero
  | .second b => Tag.ofNat b.toNat
  | .high t | .done t => t

private theorem high_fold (xs : List Bool) (t : Tag) :
    finish (xs.foldl advance (.high t)) = if value xs = 0 then t else .large := by
  induction xs generalizing t with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [advance, ih, value]

/-- The width-independent scan classifies the full unsigned word. -/
theorem finish_fold (word : List Bool) :
    finish (word.foldl advance .first) = Tag.ofNat (value word) := by
  cases word with
  | nil => rfl
  | cons low rest =>
    cases rest with
    | nil => simp [advance, finish, value]
    | cons b xs =>
      simp only [List.foldl_cons, advance, high_fold, value]
      by_cases h : value xs = 0
      · simp [h]
      · rw [ite_eq_right h]
        exact (Tag.ofNat_large (by omega)).symm

/-- On the empty pop, return the classification in finite control. -/
def code {K : Type*} (src : K) : StackCode K State
  | .done _ => .halt true
  | q => .pop src fun bit => bit.elim (.done (finish q)) (advance q)

private def scanning : State → Prop
  | .done _ => False
  | _ => True

private theorem pop_eq {K : Type*} (src : K) (q : State) (hq : scanning q) :
    code src q = .pop src (fun bit => bit.elim (.done (finish q)) (advance q)) := by
  cases q <;> first | rfl | exact hq.elim

private theorem scan_runs {K : Type*} [DecidableEq K] (src : K) (base : Stacks K)
    (xs : List Bool) (q : State) (hq : scanning q) :
    StackRuns (code src) (xs.length + 1) q (Function.update base src xs)
      (.done (finish (xs.foldl advance q))) (Function.update base src []) := by
  induction xs generalizing q with
  | nil =>
    refine .cons (.pop (pop_eq src q hq)) ?_
    simp only [Function.update_self, List.head?_nil, List.tail_nil, Option.elim_none,
      Function.update_idem]
    exact .nil ..
  | cons b xs ih =>
    refine .cons (.pop (pop_eq src q hq)) ?_
    simp only [Function.update_self, List.head?_cons, List.tail_cons, Option.elim_some,
      Function.update_idem, List.foldl_cons]
    exact ih (advance q b) (by cases q <;> trivial)

/-- The designated stack is emptied in one pop per bit plus one empty pop. -/
theorem run {K : Type*} [DecidableEq K] (src : K) (s : Stacks K) :
    StackRuns (code src) ((s src).length + 1) .first s
      (.done (Tag.ofNat (value (s src)))) (Function.update s src []) := by
  simpa only [Function.update_eq_self, finish_fold] using
    scan_runs src s (s src) .first trivial

theorem word_run {K : Type*} [DecidableEq K] {w : ℕ} (src : K) (s : Stacks K)
    (a : BurstRAM.Word w) (h : s src = BurstRAM.wordBits a) :
    StackRuns (code src) (w + 1) .first s (.done (Tag.ofNat a.val)) (Function.update s src []) := by
  simpa only [h, BurstRAM.length_wordBits, value_wordBits] using run src s

end RAMTape.SuccessorTags

end VPVNP
end Computability
end OAI
