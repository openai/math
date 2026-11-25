import OAI.Computability.BorderVNP.CellSparseChecks

/-! # Boolean tests for one-copy private truth tables and gadget positions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro

/-- Test a little-endian bit word against a fixed nonnegative integer. The
empty suffix also checks that no high bit of the integer remains. -/
def wordIs : List NatExpr → ℕ → Term
  | [], j => .lit (decide (j = 0))
  | a :: as, j => .and ((Term.wire a).equal (.lit (decide (j % 2 = 1)))) (wordIs as (j / 2))

/-- This test includes the full range check, so out-of-width rows cannot alias
in-range rows. -/
theorem wordIs_correct (as : List NatExpr) (j : ℕ) (e : List ℕ) (bank : ℕ → Bool) :
    (wordIs as j).eval e bank = true ↔ word bank (as.map (NatExpr.eval e)) = j := by
  induction as generalizing j with
  | nil => simp [wordIs, Term.eval, word, eq_comm]
  | cons a as ih =>
    simp only [wordIs, Term.eval, Bool.and_eq_true, Term.eval_equal,
      List.map_cons, word]
    rw [ih]
    by_cases hb : bank (a.eval e) = true
    · simp [hb]; omega
    · have hz := Bool.eq_false_iff.mpr hb
      simp [hz]; omega

/-- Select the truth-table rows satisfying the requested test. Each row is emitted
once, with its actual integer row number. -/
def rowTest {α : Type} (as : List NatExpr) (test : α → Bool) (rows : List α) : Term :=
  Term.any (rows.zipIdx.filterMap fun r => if test r.1 then some (wordIs as r.2) else none)

/-- Table selection reads precisely the row addressed by the local bits. -/
theorem rowTest_correct {α : Type} (as : List NatExpr) (test : α → Bool) (rows : List α)
    (e : List ℕ) (bank : ℕ → Bool) :
    (rowTest as test rows).eval e bank = true ↔
      ∃ v, rows[word bank (as.map (NatExpr.eval e))]? = some v ∧ test v = true := by
  simp only [rowTest, Term.eval_any, List.any_eq_true, List.mem_filterMap]
  constructor
  · rintro ⟨_, ⟨⟨v, i⟩, hm, hv⟩, ht⟩
    cases h : test v <;> simp [h] at hv
    subst_vars
    rw [wordIs_correct] at ht
    refine ⟨v, ?_, h⟩
    simpa [ht] using (List.mem_zipIdx_iff_getElem?.mp hm)
  · rintro ⟨v, hv, h⟩
    let i := word bank (as.map (NatExpr.eval e))
    exact ⟨wordIs as i, ⟨(v, i), List.mem_zipIdx_iff_getElem?.mpr hv, by simp [h]⟩,
      (wordIs_correct ..).mpr rfl⟩

/-- Shift each local wire offset into its physical copy in the assignment bank. -/
def tableWires (offset : NatExpr) (wires : List ℕ) : List NatExpr :=
  wires.map fun i => .add offset (.lit i)

/-- The selected row address uses the same actual wire numbers as the one-copy
table's denotation. -/
theorem tableWires_eval (offset : NatExpr) (wires : List ℕ) (e : List ℕ) :
    (tableWires offset wires).map (NatExpr.eval e) = wires.map (offset.eval e + ·) := by
  simp [tableWires, List.map_map, Function.comp_def, NatExpr.eval]

/-- First conjunct for a one-copy table: its Boolean read passes, or its signed
or gadget row exists. A unary weight checks exactly its announced use bit. -/
def factorPass (offset copy : NatExpr) : Factor → Term
  | .truth wires rows => rowTest (tableWires offset wires) id rows
  | .sign wires rows => rowTest (tableWires offset wires) (fun _ => true) rows
  | .gadget wires rows => rowTest (tableWires offset wires) (fun _ => true) rows
  | .unary i p => (Term.wire (.add offset (.lit i))).equal (.wire (p.expr copy (.lit 0)))

/-- Local negative weight for a passing entry. -/
def factorSign (offset : NatExpr) : Factor → Term
  | .sign wires rows => rowTest (tableWires offset wires) id rows
  | _ => .lit false

/-- Whether the observed table position names this gadget. The test reads the
ID, and never consults the corresponding field scalar. -/
def factorSelect (offset : NatExpr) (id : ℕ) : Factor → Term
  | .gadget wires rows => rowTest (tableWires offset wires) (fun r => decide (r = id)) rows
  | _ => .lit false

/-- The compiled validity check accepts just the successful one-copy reads. -/
theorem factorPass_correct (f : Factor) (off copy : NatExpr) (e : List ℕ) (bank : ℕ → Bool) :
    (factorPass off copy f).eval e bank = true ↔
      (f.observe bank (off.eval e) (copy.eval e)).isSome := by
  cases f with
  | truth wires rows => simp [factorPass, Factor.observe, rowTest_correct, tableWires_eval]
  | sign wires rows =>
    rw [factorPass, rowTest_correct, tableWires_eval]
    simp only [Factor.observe, Option.isSome_map, Option.isSome_iff_exists, and_true]
  | gadget wires rows =>
    rw [factorPass, rowTest_correct, tableWires_eval]
    simp only [Factor.observe, Option.isSome_map, Option.isSome_iff_exists, and_true]
  | unary i p => simp [factorPass, Factor.observe, Term.eval, NatExpr.eval]; exact decide_eq_true_iff

/-- The bit emitted into the sign accumulator is the sign of the selected row. -/
theorem factorSign_correct (f : Factor) (off copy : NatExpr) (e : List ℕ) (bank : ℕ → Bool)
    (b : Bool) (g : Option ℕ) (h : f.observe bank (off.eval e) (copy.eval e) = some (b, g)) :
    (factorSign off f).eval e bank = b := by
  apply Bool.eq_iff_iff.mpr
  cases f with
  | truth wires rows => simp only [Factor.observe] at h; split at h <;> simp_all [factorSign, Term.eval]
  | sign wires rows =>
    simp only [Factor.observe, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [factorSign, rowTest_correct, tableWires_eval, hv]
  | gadget wires rows =>
    simp only [Factor.observe, Option.map_eq_some_iff] at h
    obtain ⟨v, _, h⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl
  | unary i p => simp only [Factor.observe] at h; split at h <;> simp_all [factorSign, Term.eval]

/-- The selected gadget flag counts each genuine row, including any zero-valued row. -/
theorem factorSelect_correct (f : Factor) (off copy : NatExpr) (e : List ℕ) (bank : ℕ → Bool)
    (id : ℕ) (b : Bool) (g : Option ℕ)
    (h : f.observe bank (off.eval e) (copy.eval e) = some (b, g)) :
    (factorSelect off id f).eval e bank = true ↔ g = some id := by
  cases f with
  | truth wires rows => simp only [Factor.observe] at h; split at h <;> simp_all [factorSelect, Term.eval] ; simp [← h.2]
  | sign wires rows =>
    simp only [Factor.observe, Option.map_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [factorSelect, Term.eval]
  | gadget wires rows =>
    simp only [Factor.observe, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [factorSelect, rowTest_correct, tableWires_eval, hv]
  | unary i p => simp only [Factor.observe] at h; split at h <;> simp_all [factorSelect, Term.eval] ; simp [← h.2]

end CellSparse

end BorderVNP
end Computability
end OAI
