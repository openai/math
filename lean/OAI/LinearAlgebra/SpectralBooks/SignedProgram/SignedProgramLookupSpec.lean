import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramTable
import Mathlib.Data.List.OfFn

/-! # Priority semantics of a bounded transition table -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram
open SignedMachine

private instance : LawfulBEq Symbol where
  rfl := by intro a; cases a <;> rfl
  eq_of_beq := by intro a b; cases a <;> cases b <;> decide

def keyMatch {n : ℕ} (t : Table n) (q : Fin (n+1)) (a : Symbol) (w : Fin n → Symbol)
    (i : Fin n) : Bool :=
  decide (i.val < t.rows.val ∧ (t.row i).state = q ∧ (t.row i).input = a ∧
    ∀ j : Fin n, j.val < t.tapes.val → (t.row i).reads j = w j)

/-- First active row agreeing with every active head read. -/
def firstRow {n : ℕ} (t : Table n) (q : Fin (n+1)) (a : Symbol) (w : Fin n → Symbol) :
    Option (Fin n) := (List.ofFn (id : Fin n → Fin n)).find? (keyMatch t q a w)

private theorem find_masked {k n : ℕ} (h : k ≤ n) (f : Fin n → Bool) :
    (List.ofFn (id : Fin n → Fin n)).find? (fun i => decide (i.val < k) && f i) =
      (List.ofFn (fun i : Fin k => i.castLE h)).find? f := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.ofFn_add, List.find?_append]
  have hnone : (List.ofFn fun i : Fin s => i.natAdd k).find?
      (fun i => decide (i.val < k) && f i) = none := by
    rw [List.find?_eq_none]
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    simp
  simp only [id_eq, hnone, Option.or_none]
  apply List.find?_congr
  intro i hi
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  simp

private theorem activeList_eq_iff {n : ℕ} {α : Type*} (k : Fin (n+1)) (f g : Fin n → α) :
    activeList k f = activeList k g ↔ ∀ j, j.val < k.val → f j = g j := by
  rw [activeList, activeList, List.ofFn_inj, funext_iff]
  constructor
  · intro h j hj
    exact h ⟨j.val, hj⟩
  · intro h j
    exact h (j.castLE (Nat.le_of_lt_succ k.isLt)) j.isLt

/-- The index search reproduces the machine interpreter's first matching action.
No distinct-key assumption is needed. -/
theorem firstRow_action {n : ℕ} (t : Table n) (q : Fin (n+1)) (a : Symbol) (w : Fin n → Symbol) :
    (t.program.table.find? (fun r => r.state == q.val && r.inputSymbol == a &&
      r.workSymbols == activeList t.tapes w)).map Rule.action =
    (firstRow t q a w).map (fun i => (t.row i).action t.tapes) := by
  let f (i : Fin n) := (t.row i).state == q && (t.row i).input == a &&
    activeList t.tapes (t.row i).reads == activeList t.tapes w
  have hm (i : Fin n) : keyMatch t q a w i = (decide (i.val < t.rows.val) && f i) := by
    apply Bool.eq_iff_iff.mpr
    simp [keyMatch, f, activeList_eq_iff, and_assoc]
  let ids := activeList t.rows (id : Fin n → Fin n)
  have hrows : t.program.table = ids.map (fun i => (t.row i).rule t.tapes) := by
    simp [ids, Table.program, activeList, List.map_ofFn, Function.comp_def]
  have hid : firstRow t q a w = ids.find? f := by
    unfold firstRow
    simp_rw [hm]
    exact find_masked (Nat.le_of_lt_succ t.rows.isLt) f
  rw [hrows, List.find?_map, Option.map_map, hid]
  have hkey (i : Fin n) : (((t.row i).rule t.tapes).state == q.val &&
      ((t.row i).rule t.tapes).inputSymbol == a &&
      ((t.row i).rule t.tapes).workSymbols == activeList t.tapes w) = f i := by
    apply Bool.eq_iff_iff.mpr
    simp [Row.rule, f, Fin.ext_iff]
  simp only [Function.comp_def, hkey]
  rfl

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
