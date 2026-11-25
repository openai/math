import OAI.Computability.NearSquareRoot.CommonAlphabetNumbering
import OAI.Computability.NearSquareRoot.ScheduleGeneratorTable

/-! # Effective ROM serialization with numbered states, letters, and tracks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator

open IntegerMultiplication CommonAlphabet Universal

/-- The ROM starts at row zero, so the entry and zero exchange addresses. -/
private def swapEntry (e n : ℕ) := if n = e then 0 else if n = 0 then e else n

private theorem primrec_swapEntry : Primrec₂ swapEntry :=
  Primrec.ite (Primrec.eq.comp Primrec.snd Primrec.fst) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) Primrec.fst Primrec.snd)

private theorem swapEntry_twice (e n : ℕ) : swapEntry e (swapEntry e n) = n := by
  by_cases h : n = e <;> by_cases z : n = 0 <;> simp [swapEntry, h, z]

private theorem numbering_val {Q : Type} (q : Numbering Q) (entry s : Q) :
    (Reindex.numbering q.equiv entry s).val = swapEntry (q.equiv entry).val (q.equiv s).val := by
  simp only [Reindex.numbering, Equiv.trans_apply, Equiv.swap_apply_def, swapEntry, Fin.ext_iff]
  split
  · rfl
  · split <;> rfl

/-- A fixed read tuple has a finite table sending ranked actions to ROM branch digits. -/
private def branchTable {A I : Type} {M : ℕ} (ops : Numbering (I → A × TM.Move))
    (enum : Tag A I ≃ Fin (M + 1)) (r : I → A) : List ℕ :=
  List.ofFn fun k => (enum (.branch r (some (ops.equiv.symm k)))).val

private theorem branchTable_get {A I : Type} {M : ℕ} (ops : Numbering (I → A × TM.Move))
    (enum : Tag A I ≃ Fin (M + 1)) (r : I → A) (op : I → A × TM.Move) :
    (branchTable ops enum r).getD (ops.equiv op).val 0 = (enum (.branch r (some op))).val := by
  simp [branchTable, List.getD_eq_getElem?_getD]

/-- Computable ranked transitions and a computable entry address suffice to serialize
a family of pointed machines, including the permutation putting its entry in row zero. -/
theorem computable_numbered_program {A I : Type} {Q : ℕ → Type} {M : ℕ}
    (a : Numbering A) (i : Numbering I) (q : ∀ j, Numbering (Q j)) (entry : ∀ j, Q j)
    (m : ∀ j, TM.Rule A (Q j) I) (reads : List (I → A)) (enum : Tag A I ≃ Fin (M + 1))
    (rows : ℕ → ℕ × ℕ → Option (ℕ × ℕ))
    (hsize : Computable fun j => (q j).size)
    (hentry : Computable fun j => ((q j).equiv (entry j)).val)
    (hrows : Computable₂ rows)
    (correct : ∀ j state read,
      rows j (((q j).equiv state).val, ((i.arrow a).equiv read).val) =
        (m j state read).map fun p =>
          (((q j).equiv p.1).val, ((i.arrow (a.prod Numbering.move)).equiv p.2).val)) :
    Computable fun j => (Reindex.encode (q j).equiv (entry j) (m j) reads).map
      (fun t => (enum t).val) := by
  let start j := ((q j).equiv (entry j)).val
  let e j := Reindex.numbering (q j).equiv (entry j)
  let ops := i.arrow (a.prod Numbering.move)
  let row (r : I → A) (j k : ℕ) := rows j (swapEntry (start j) k, ((i.arrow a).equiv r).val)
  have hr r : Computable₂ (row r) := hrows.comp Computable.fst
    ((primrec_swapEntry.to_comp.comp (hentry.comp Computable.fst) Computable.snd).pair
      (Computable.const _))
  let next (r : I → A) (j k : ℕ) :=
    ((row r j k).map fun p => swapEntry (start j) p.1).getD 0
  let branch (r : I → A) (j k : ℕ) :=
    ((row r j k).map fun p => (branchTable ops enum r).getD p.2 0).getD
      (enum (.branch r none)).val
  have hn r : Computable₂ (next r) := Computable.option_getD
    (Computable.option_map (hr r) (primrec_swapEntry.to_comp.comp
      (hentry.comp (Computable.fst.comp Computable.fst)) (Computable.fst.comp Computable.snd)))
    (Computable.const _)
  have hb r : Computable₂ (branch r) := Computable.option_getD
    (Computable.option_map (hr r) ((Primrec.list_getD 0).to_comp.comp (Computable.const _)
      (Computable.snd.comp Computable.snd))) (Computable.const _)
  have row_eq (r) (j) (s : Q j) : row r j (e j s).val =
      (m j s r).map (fun p => (((q j).equiv p.1).val, (ops.equiv p.2).val)) := by
    simpa only [row, e, start, numbering_val, swapEntry_twice, ops] using correct j s r
  apply computable_program reads (fun j => (q j).size) (fun j => Reindex.rule (e j) (m j))
    enum next branch hsize (fun r _ => hn r) (fun r _ => hb r)
  · intro r _ j k
    obtain ⟨s, rfl⟩ := (e j).surjective k
    simp only [next, row_eq, Reindex.rule, Equiv.symm_apply_apply, target]
    cases m j s r <;> simp [e, start, numbering_val]
  · intro r _ j k
    obtain ⟨s, rfl⟩ := (e j).surjective k
    simp only [branch, row_eq, Reindex.rule, Equiv.symm_apply_apply, commands]
    cases m j s r with
    | none => rfl
    | some p => exact branchTable_get ops enum r p.2

end Generator

end NearSquareRoot
end Computability
end OAI
