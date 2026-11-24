import OAI.Computability.VPVNP.RAMSortCompareCost

/-!
# Word tests for the boundary records of a RAM transcript

A read uses the preceding slot's value exactly when that slot is occupied and has
its address. At a successor edge the sender also compares the entire transmitted
slot with its final slot. Both word programs respect the parser on all input tuples.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMBoundary

open BurstRAM RAMMemory RAMSort RAMSort.WordCompare RAMSerialization

/-- A transcript slot after decoding, either empty or holding a word-valued RAM record. -/
abbrev Slot (w : ℕ) := Option (Record (Word w))
/-- Five machine words making up a physical slot before occupancy and record fields are
decoded. -/
abbrev RawSlot (w : ℕ) := Fin 5 → Word w

private abbrev Fields := Fin 5 → ℕ

private def occupied (side : Bool) : Expr :=
  .select (.eq (.field side 0) (.const 0)) (.const 0) (.le (.field side 0) (.const 3))

private def sameField (i : Fin 5) : Expr := .eq (.field false i) (.field true i)

private def readProgram : Expr :=
  .select (.eq (.field true 0) (.const 2))
    (.eq (.field true 2) (.select (occupied false)
      (.select (sameField 1) (.field false 2) (.const 0)) (.const 0)))
    (.const 1)

private def requireSame (i : Fin 5) (rest : Expr) : Expr :=
  .select (sameField i) rest (.const 0)

private def equalProgram : Expr :=
  .select (occupied false)
    (requireSame 0 (requireSame 1 (requireSame 2 (requireSame 3 (sameField 4)))))
    (.select (occupied true) (.const 0) (.const 1))

variable {w : ℕ}

private def typedRun (e : Expr) (a b : Slot w) : Bool × ℕ :=
  (decide (e.eval (inputs (slotWords ⟨a⟩) (slotWords ⟨b⟩)) ≠ 0), e.steps)

/-- Check the value of an occupied read against the preceding physical slot. -/
def readOK (prev curr : Slot w) : Bool × ℕ := typedRun readProgram prev curr

/-- Compare two physical slots, including the timestamp and ordinal of a probe. -/
def equalSlot (a b : Slot w) : Bool × ℕ := typedRun equalProgram a b

theorem readOK_cost (prev curr : Slot w) : (readOK prev curr).2 ≤ 35 := by
  change readProgram.steps ≤ 35
  decide

theorem equalSlot_cost (a b : Slot w) : (equalSlot a b).2 ≤ 55 := by
  change equalProgram.steps ≤ 55
  decide

private def Used (x : Fields) := 0 < x 0 ∧ x 0 ≤ 3

private instance (x : Fields) : Decidable (Used x) :=
  inferInstanceAs (Decidable (0 < x 0 ∧ x 0 ≤ 3))

private theorem occupied_eval (x : Input) (side : Bool) :
    (occupied side).eval x = if Used (x side) then 1 else 0 := by
  by_cases hz : x side 0 = 0
  · simp [occupied, Expr.eval, Used, hz]
  · simp [occupied, Expr.eval, Used, hz, Nat.pos_of_ne_zero hz]

private theorem read_eval (a b : Fields) :
    readProgram.eval (inputs a b) ≠ 0 ↔
      (b 0 = 2 → b 2 = if Used a ∧ a 1 = b 1 then a 2 else 0) := by
  by_cases hr : b 0 = 2 <;> by_cases ha : Used a <;> by_cases he : a 1 = b 1 <;>
    simp [readProgram, sameField, Expr.eval, occupied_eval, inputs, hr, ha, he]

private theorem requireSame_eval (i : Fin 5) (tail : Expr) (a b : Fields) :
    (requireSame i tail).eval (inputs a b) ≠ 0 ↔ a i = b i ∧ tail.eval (inputs a b) ≠ 0 := by
  by_cases h : a i = b i <;> simp [requireSame, sameField, Expr.eval, inputs, h]

private theorem equal_eval (a b : Fields) :
    equalProgram.eval (inputs a b) ≠ 0 ↔
      if Used a then a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ a 3 = b 3 ∧ a 4 = b 4 else ¬Used b := by
  have hleft : (occupied false).eval (inputs a b) = if Used a then 1 else 0 :=
    occupied_eval ..
  have hright : (occupied true).eval (inputs a b) = if Used b then 1 else 0 :=
    occupied_eval ..
  by_cases ha : Used a
  · simp only [equalProgram, Expr.eval, hleft, ite_eq_left ha, one_ne_zero, ite_false,
      requireSame_eval]
    by_cases h : a 4 = b 4 <;> simp [sameField, Expr.eval, inputs, h]
  · by_cases hb : Used b <;> simp [equalProgram, Expr.eval, hleft, hright, ha, hb]

private theorem words_none : slotWords (⟨none⟩ : OrderedSlot (Word w)) = fun _ ↦ 0 := rfl

private theorem words_some (r : Record (Word w)) :
    slotWords ⟨some r⟩ = ![r.kind.code + 1, r.address, r.value.val, r.startCost, r.ordinal] := by
  rcases r with ⟨k, _, _, _, _⟩
  cases k <;> rfl

theorem readOK_spec (prev curr : Slot w) : (readOK prev curr).1 = true ↔
    ∀ r ∈ curr, r.kind = .read → r.value = previousValue prev r.address := by
  simp only [readOK, typedRun, decide_eq_true_eq, read_eval]
  rcases curr with _ | ⟨k, a, v, c, j⟩
  · simp [words_none]
  · cases k <;> rcases prev with _ | ⟨k', a', v', c', j'⟩
    all_goals first | cases k' | skip
    all_goals simp [words_none, words_some, Used, Kind.code, previousValue]
    all_goals split_ifs <;> first | exact Fin.ext_iff.symm | simp

theorem equalSlot_spec (a b : Slot w) : (equalSlot a b).1 = true ↔ a = b := by
  simp only [equalSlot, typedRun, decide_eq_true_eq, equal_eval]
  rcases a with _ | ⟨k, _, _, _, _⟩ <;> rcases b with _ | ⟨k', _, _, _, _⟩
  all_goals first | cases k | skip
  all_goals first | cases k' | skip
  all_goals simp [words_none, words_some, Used, Kind.code]
  all_goals intros; exact Fin.ext_iff.symm

private def rawRun (hw : 2 ≤ w) (e : Expr) (a b : RawSlot w) : Bool × ℕ :=
  let output := e.runWord hw (fun side ↦ if side then b else a)
  (decide (output.1.val ≠ 0), output.2)

/-- Execute the predecessor test on two arbitrary five-word tuples. -/
def readRaw (hw : 2 ≤ w) (prev curr : RawSlot w) : Bool × ℕ := rawRun hw readProgram prev curr

/-- Execute whole-slot equality on two arbitrary five-word tuples. -/
def equalRaw (hw : 2 ≤ w) (a b : RawSlot w) : Bool × ℕ := rawRun hw equalProgram a b

private def values (a : RawSlot w) : Fields := fun i ↦ (a i).val

private theorem rawRun_eq (hw : 2 ≤ w) (e : Expr) (a b : RawSlot w) :
    rawRun hw e a b = (decide (e.eval (inputs (values a) (values b)) ≠ 0), e.steps) := by
  have spec := e.runWord_spec hw (fun side ↦ if side then b else a)
  have h : (fun side i ↦ ((if side then b else a) i).val) = inputs (values a) (values b) := by
    funext side i
    cases side <;> rfl
  simp only [rawRun, spec.1, spec.2, h]

private def normalize (x : Fields) : Fields := if Used x then x else fun _ ↦ 0

private theorem words_parsed (hw : 2 ≤ w) (a : RawSlot w) :
    slotWords ⟨(parsedSlot hw a).record⟩ = normalize (values a) := by
  by_cases h : Used (values a)
  · rw [normalize, ite_eq_left h]
    change 0 < (a 0).val ∧ (a 0).val ≤ 3 at h
    have ht : (a 0).val = 1 ∨ (a 0).val = 2 ∨ (a 0).val = 3 := by omega
    rcases ht with ht | ht | ht <;> funext i <;> fin_cases i <;>
      simp [parsedSlot, recordFormat, WordRecord.record, words_some, Kind.code, ht, values]
  · rw [normalize, ite_eq_right h]
    change ¬(0 < (a 0).val ∧ (a 0).val ≤ 3) at h
    have h₁ : (a 0).val ≠ 1 := by omega
    have h₂ : (a 0).val ≠ 2 := by omega
    have h₃ : (a 0).val ≠ 3 := by omega
    simp [parsedSlot, recordFormat, words_none]

private theorem zero_unused : ¬Used (fun _ ↦ 0) := by simp [Used]

private theorem read_normalize (a b : Fields) :
    readProgram.eval (inputs a b) ≠ 0 ↔ readProgram.eval (inputs (normalize a) (normalize b)) ≠ 0 := by
  rw [read_eval, read_eval]
  by_cases hb : Used b
  · by_cases ha : Used a <;> simp [normalize, ha, hb, zero_unused]
  · have hread : b 0 ≠ 2 := fun ht ↦ hb (by simp [Used, ht])
    simp [normalize, hb, hread]

private theorem equal_normalize (a b : Fields) :
    equalProgram.eval (inputs a b) ≠ 0 ↔ equalProgram.eval (inputs (normalize a) (normalize b)) ≠ 0 := by
  rw [equal_eval, equal_eval]
  by_cases ha : Used a <;> by_cases hb : Used b
  · simp [normalize, ha, hb]
  · have hne : a 0 ≠ b 0 := fun h ↦ hb (by simpa [Used, ← h] using ha)
    have hnz : a 0 ≠ 0 := Nat.ne_of_gt ha.1
    simp [normalize, ha, hb, hnz, hne]
  · simp [normalize, ha, hb, zero_unused]
  · simp [normalize, ha, hb, zero_unused]

theorem readRaw_eq (hw : 2 ≤ w) (prev curr : RawSlot w) :
    readRaw hw prev curr = readOK (parsedSlot hw prev).record (parsedSlot hw curr).record := by
  simp only [readRaw, rawRun_eq, readOK, typedRun, words_parsed]
  exact Prod.ext (decide_eq_decide.mpr (read_normalize _ _)) rfl

theorem equalRaw_eq (hw : 2 ≤ w) (a b : RawSlot w) :
    equalRaw hw a b = equalSlot (parsedSlot hw a).record (parsedSlot hw b).record := by
  simp only [equalRaw, rawRun_eq, equalSlot, typedRun, words_parsed]
  exact Prod.ext (decide_eq_decide.mpr (equal_normalize _ _)) rfl

end RAMBoundary

end VPVNP
end Computability
end OAI
