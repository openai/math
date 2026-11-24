import OAI.Computability.VPVNP.RAMRecordOrder
import OAI.Computability.VPVNP.RAMSerialization
import Mathlib.Tactic.FinCases

/-!
# Word program for one sorting comparison

The fixed five-word format is ordered first by address, then by the
initialization flag, start cost and probe ordinal. Ties are broken by kind
and value. Empty records follow every occupied record. The comparator below
uses only fixed-offset reads, word constants, comparisons and conditional
selection. Each expression node costs one elementary operation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

open BurstRAM RAMMemory RAMSerialization

namespace WordCompare

/-- Word expressions. A conditional selection is evaluated after its three
operands, so the operation count is independent of the input. -/
inductive Expr where
  | field (right : Bool) (index : Fin 5)
  | const (n : Fin 4)
  | eq (a b : Expr)
  | lt (a b : Expr)
  | le (a b : Expr)
  | select (test yes no : Expr)

/-- Two five-word comparison operands indexed by side and by field within each record. -/
abbrev Input := Bool → Fin 5 → ℕ

/-- Evaluate a comparison expression on the two input records, encoding truth by one and
selecting the false arm on a zero test. -/
def Expr.eval (x : Input) : Expr → ℕ
  | .field right index => x right index
  | .const n => n.val
  | .eq a b => if a.eval x = b.eval x then 1 else 0
  | .lt a b => if a.eval x < b.eval x then 1 else 0
  | .le a b => if a.eval x ≤ b.eval x then 1 else 0
  | .select test yes no => if test.eval x = 0 then no.eval x else yes.eval x

/-- Word-operation count for a comparison expression, charging field accesses, constants,
comparisons, and both arms of a select. -/
def Expr.steps : Expr → ℕ
  | .field .. | .const _ => 1
  | .eq a b | .lt a b | .le a b => a.steps + b.steps + 1
  | .select test yes no => test.steps + yes.steps + no.steps + 1

/-- Each intermediate result fits one word when both operands fit.
The immediate constants use at most two bits. -/
theorem Expr.eval_lt {w : ℕ} (hw : 2 ≤ w) {x : Input} (hx : ∀ b i, x b i < 2 ^ w) (e : Expr) :
    e.eval x < 2 ^ w := by
  have hsize : 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  induction e with
  | field b i => exact hx b i
  | const n => exact n.isLt.trans_le hsize
  | eq | lt | le => simp only [Expr.eval]; split <;> omega
  | select => simp only [Expr.eval]; split <;> assumption

private def occupied (right : Bool) : Expr :=
  .select (.lt (.const 3) (.field right 0)) (.const 0) (.lt (.const 0) (.field right 0))

private def lexStep (a b tail : Expr) : Expr := .select (.eq a b) tail (.lt a b)

private def compareField (i : Fin 5) (tail : Expr) : Expr :=
  lexStep (.field false i) (.field true i) tail

private def probeFlag (right : Bool) : Expr := .lt (.const 1) (.field right 0)

/-- The straight-line word comparison for two encoded slots. Tags outside
the occupied range 1--3 compare as empty, as in the parser. -/
def program : Expr :=
  .select (occupied true)
    (.select (occupied false)
      (compareField 1 (lexStep (probeFlag false) (probeFlag true)
        (compareField 3 (compareField 4 (compareField 0 (.le (.field false 2) (.field true 2)))))))
      (.const 0))
    (.const 1)

private def tag : Kind → ℕ
  | .init => 1
  | .read => 2
  | .write => 3

/-- Word values of the paper's physical record, viewed as naturals. -/
def slotWords {w : ℕ} (s : OrderedSlot (Word w)) : Fin 5 → ℕ :=
  match s.record with
  | none => fun _ ↦ 0
  | some r => ![tag r.kind, r.address, r.value.val, r.startCost, r.ordinal]

/-- Assemble the comparator input from two five-word arrays, choosing the right array on true
and the left array on false. -/
def inputs (l r : Fin 5 → ℕ) : Input := fun side ↦ if side then r else l

private def kindIndex : Kind → ℕ
  | .init => 0
  | .read => 1
  | .write => 2

private abbrev Code (V : Type*) :=
  WithTop (Lex (Lex (ℕ × Lex (ℕ × Lex (ℕ × ℕ))) × Lex (ℕ × V)))

private def key {V : Type*} (s : OrderedSlot V) : Code V :=
  match s.record with
  | none => ⊤
  | some r => ↑(toLex (toLex (r.address, r.timestamp), toLex (kindIndex r.kind, r.value)))

private theorem le_iff_key {V : Type*} [LinearOrder V] (s t : OrderedSlot V) :
    s ≤ t ↔ key s ≤ key t := Iff.rfl

private theorem program_slots {w : ℕ} (s t : OrderedSlot (Word w)) :
    program.eval (inputs (slotWords s) (slotWords t)) ≠ 0 ↔ s ≤ t := by
  rcases s with ⟨_ | ⟨k, a, v, c, j⟩⟩ <;> rcases t with ⟨_ | ⟨k', a', v', c', j'⟩⟩
  all_goals rw [le_iff_key]
  all_goals first | cases k | skip
  all_goals first | cases k' | skip
  all_goals simp [program, occupied, compareField, lexStep, probeFlag, Expr.eval, inputs,
    slotWords, tag, key, kindIndex, Record.timestamp, Prod.Lex.toLex_le_toLex,
    Prod.Lex.toLex_lt_toLex]
  all_goals try split_ifs
  all_goals (try simp_all) <;> omega

end WordCompare

/-- Result and elementary word count of the fixed comparator. Natural field
values represent one word for every slot supplied by the word-format parser. -/
def compareSlots {w : ℕ} (s t : OrderedSlot (Word w)) : Bool × ℕ :=
  (decide (WordCompare.program.eval (WordCompare.inputs (WordCompare.slotWords s)
    (WordCompare.slotWords t)) ≠ 0), WordCompare.program.steps)

theorem compareSlots_result {w : ℕ} (s t : OrderedSlot (Word w)) :
    (compareSlots s t).1 = decide (s ≤ t) :=
  decide_eq_decide.mpr (WordCompare.program_slots s t)

@[simp] theorem compareSlots_steps {w : ℕ} (s t : OrderedSlot (Word w)) :
    (compareSlots s t).2 = 66 := rfl

/-- The word-level representation supplied by the five-word parser, including
its convention for unknown tags and noncanonical padding. Canonicality is
checked separately by `Format.decode`. -/
def parsedSlot {w : ℕ} (hw : 2 ≤ w) (x : Fin 5 → Word w) : OrderedSlot (Word w) :=
  ⟨((recordFormat hw).parse x).map WordRecord.record⟩

namespace WordCompare

private def Occupied (x : Fin 5 → ℕ) : Prop := 0 < x 0 ∧ x 0 ≤ 3

private instance (x : Fin 5 → ℕ) : Decidable (Occupied x) :=
  inferInstanceAs (Decidable (0 < x 0 ∧ x 0 ≤ 3))

private def normalize (x : Fin 5 → ℕ) : Fin 5 → ℕ := if Occupied x then x else fun _ ↦ 0

private theorem occupied_eval (x : Input) (side : Bool) :
    (occupied side).eval x = if Occupied (x side) then 1 else 0 := by
  by_cases hi : 3 < x side 0
  · simp [occupied, Expr.eval, Occupied, hi, Nat.not_le_of_lt hi]
  · have hle := Nat.le_of_not_gt hi
    by_cases hpos : 0 < x side 0 <;> simp [occupied, Expr.eval, Occupied, hi, hle, hpos]

private theorem program_normalize (x y : Fin 5 → ℕ) :
    program.eval (inputs x y) = program.eval (inputs (normalize x) (normalize y)) := by
  by_cases hy : Occupied y
  · by_cases hx : Occupied x
    · simp [normalize, hx, hy]
    · have hz : ¬Occupied (fun _ ↦ 0) := by simp [Occupied]
      simp [program, Expr.eval, occupied_eval, inputs, normalize, hx, hy, hz]
  · have hz : ¬Occupied (fun _ ↦ 0) := by simp [Occupied]
    simp [program, Expr.eval, occupied_eval, inputs, normalize, hy, hz]

private theorem slotWords_parse {w : ℕ} (hw : 2 ≤ w) (a : Fin 5 → Word w) :
    slotWords (parsedSlot hw a) = normalize (fun i ↦ (a i).val) := by
  by_cases hv : Occupied (fun i ↦ (a i).val)
  · rw [normalize, ite_eq_left hv]
    change 0 < (a 0).val ∧ (a 0).val ≤ 3 at hv
    have ht : (a 0).val = 1 ∨ (a 0).val = 2 ∨ (a 0).val = 3 := by omega
    rcases ht with h | h | h <;> funext i <;> fin_cases i <;>
      simp [slotWords, parsedSlot, recordFormat, WordRecord.record, tag, h]
  · rw [normalize, ite_eq_right hv]
    change ¬(0 < (a 0).val ∧ (a 0).val ≤ 3) at hv
    have h₁ : (a 0).val ≠ 1 := by omega
    have h₂ : (a 0).val ≠ 2 := by omega
    have h₃ : (a 0).val ≠ 3 := by omega
    simp [slotWords, parsedSlot, recordFormat]

end WordCompare

namespace WordCompare

private def flag {w : ℕ} (hw : 2 ≤ w) (p : Prop) [Decidable p] : Word w :=
  if p then ⟨1, by have := Nat.pow_le_pow_right (by decide : 0 < 2) hw; omega⟩ else 0

private theorem flag_val {w : ℕ} (hw : 2 ≤ w) (p : Prop) [Decidable p] :
    (flag hw p).val = if p then 1 else 0 := by
  by_cases h : p <;> simp [flag, h]

/-- Execute the syntax using genuine `w`-bit words. Each operand is evaluated
before its instruction, including all three inputs of conditional selection. -/
def Expr.runWord {w : ℕ} (hw : 2 ≤ w) (x : Bool → Fin 5 → Word w) : Expr → Word w × ℕ
  | .field b i => (x b i, 1)
  | .const n => (⟨n.val, n.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hw)⟩, 1)
  | .eq a b =>
    let l := a.runWord hw x
    let r := b.runWord hw x
    (flag hw (l.1 = r.1), l.2 + r.2 + 1)
  | .lt a b =>
    let l := a.runWord hw x
    let r := b.runWord hw x
    (flag hw (l.1 < r.1), l.2 + r.2 + 1)
  | .le a b =>
    let l := a.runWord hw x
    let r := b.runWord hw x
    (flag hw (l.1 ≤ r.1), l.2 + r.2 + 1)
  | .select t a b =>
    let test := t.runWord hw x
    let l := a.runWord hw x
    let r := b.runWord hw x
    (if test.1.val = 0 then r.1 else l.1, test.2 + l.2 + r.2 + 1)

theorem Expr.runWord_spec {w : ℕ} (hw : 2 ≤ w) (x : Bool → Fin 5 → Word w) (e : Expr) :
    (e.runWord hw x).1.val = e.eval (fun b i ↦ (x b i).val) ∧ (e.runWord hw x).2 = e.steps := by
  induction e with
  | field | const => exact ⟨rfl, rfl⟩
  | eq a b ha hb =>
    simp only [runWord, eval, steps, flag_val, Fin.ext_iff, ha.1, hb.1, ha.2, hb.2, and_self]
  | lt a b ha hb =>
    simp only [runWord, eval, steps, flag_val, Fin.lt_def, ha.1, hb.1, ha.2, hb.2, and_self]
  | le a b ha hb =>
    simp only [runWord, eval, steps, flag_val, Fin.le_def, ha.1, hb.1, ha.2, hb.2, and_self]
  | select t a b ht ha hb =>
    simp only [runWord, eval, steps, ht.1, ht.2, ha.2, hb.2, and_true]
    split
    · exact hb.1
    · exact ha.1

end WordCompare

/-- Evaluation directly on the two received five-word tuples. -/
def compareWords {w : ℕ} (hw : 2 ≤ w) (l r : Fin 5 → Word w) : Bool × ℕ :=
  let output := WordCompare.program.runWord hw (fun side ↦ if side then r else l)
  (decide (output.1.val ≠ 0), output.2)

/-- The direct word computation gives exactly the abstract slot order and
cost, even on arbitrary tag values that the raw parser interprets as empty. -/
theorem compareWords_eq {w : ℕ} (hw : 2 ≤ w) (l r : Fin 5 → Word w) :
    compareWords hw l r = compareSlots (parsedSlot hw l) (parsedSlot hw r) := by
  have spec := WordCompare.program.runWord_spec hw (fun side ↦ if side then r else l)
  simp only [compareWords, spec.1, spec.2, compareSlots, WordCompare.slotWords_parse]
  change (decide (WordCompare.program.eval (WordCompare.inputs (fun i ↦ (l i).val)
    (fun i ↦ (r i).val)) ≠ 0), _) = _
  rw [WordCompare.program_normalize]

/-- Every valid record, including an initialization or empty record, can be
compared in the physical representation with the same result and step count. -/
theorem compareWords_encoded {w : ℕ} (hw : 2 ≤ w) (l r : Option (WordRecord w)) :
    compareWords hw ((recordFormat hw).words l) ((recordFormat hw).words r) =
      compareSlots ⟨l.map WordRecord.record⟩ ⟨r.map WordRecord.record⟩ := by
  simp [compareWords_eq, parsedSlot, Format.parse_words]

namespace WordCompare

/-- Lexicographic step on ordinary unsigned word values. -/
def lexBit (a b : ℕ) (tail : Bool) : Bool := if a = b then tail else decide (a < b)

private theorem lex_eval (x : Input) (a b tail : Expr) :
    decide ((lexStep a b tail).eval x ≠ 0) =
      lexBit (a.eval x) (b.eval x) (decide (tail.eval x ≠ 0)) := by
  by_cases he : a.eval x = b.eval x <;> by_cases hl : a.eval x < b.eval x <;>
    simp [lexStep, lexBit, Expr.eval, he, hl]

/-- The bit-level sorting comparator can compute each lexicographic step
as soon as it has classified the two unsigned word values. -/
theorem compareWords_lex {w : ℕ} (hw : 2 ≤ w) (a b : Fin 5 → Word w) :
    (compareWords hw a b).1 =
      if 0 < (b 0).val ∧ (b 0).val ≤ 3 then
        if 0 < (a 0).val ∧ (a 0).val ≤ 3 then
          lexBit (a 1).val (b 1).val (lexBit (if 1 < (a 0).val then 1 else 0)
            (if 1 < (b 0).val then 1 else 0) (lexBit (a 3).val (b 3).val
            (lexBit (a 4).val (b 4).val (lexBit (a 0).val (b 0).val (decide (a 2 ≤ b 2)))))) else false
      else true := by
  have spec := program.runWord_spec hw (fun side ↦ if side then b else a)
  simp only [compareWords, spec.1]
  let x : Input := inputs (fun i ↦ (a i).val) (fun i ↦ (b i).val)
  change decide (program.eval x ≠ 0) = _
  have ha : (occupied false).eval x = if 0 < (a 0).val ∧ (a 0).val ≤ 3 then 1 else 0 :=
    occupied_eval x false
  have hb : (occupied true).eval x = if 0 < (b 0).val ∧ (b 0).val ≤ 3 then 1 else 0 :=
    occupied_eval x true
  let body := compareField 1 (lexStep (probeFlag false) (probeFlag true)
    (compareField 3 (compareField 4 (compareField 0 (.le (.field false 2) (.field true 2))))))
  change decide ((if (occupied true).eval x = 0 then 1 else if (occupied false).eval x = 0 then 0
    else body.eval x) ≠ 0) = _
  rw [ha,hb]
  by_cases vb : 0 < (b 0).val ∧ (b 0).val ≤ 3
  · rw [ite_eq_left vb, ite_eq_right (by decide : (1:ℕ) ≠ 0), ite_eq_left vb]
    by_cases va : 0 < (a 0).val ∧ (a 0).val ≤ 3
    · rw [ite_eq_left va, ite_eq_right (by decide : (1:ℕ) ≠ 0), ite_eq_left va]
      dsimp only [body, compareField]
      erw [lex_eval, lex_eval, lex_eval, lex_eval, lex_eval]
      apply congrArg (fun bit ↦ lexBit (a 1).val (b 1).val (lexBit (if 1 < (a 0).val then 1 else 0)
        (if 1 < (b 0).val then 1 else 0) (lexBit (a 3).val (b 3).val (lexBit (a 4).val (b 4).val
        (lexBit (a 0).val (b 0).val bit)))))
      apply decide_eq_decide.mpr
      change (if (a 2).val ≤ (b 2).val then 1 else 0) ≠ 0 ↔ _
      by_cases hv : (a 2).val ≤ (b 2).val <;> simp [hv, show (a 2 ≤ b 2) ↔ _ from Fin.le_def]
    · rw [ite_eq_right va, ite_eq_left rfl, ite_eq_right va]
      rfl
  · rw [ite_eq_right vb, ite_eq_left rfl, ite_eq_right vb]
    rfl

end WordCompare
end RAMSort

end VPVNP
end Computability
end OAI
