import OAI.Optimization.LinearProgramming.Geometry.PivotRAM

/-! Exact correspondence between the RAM winner index and the adaptive pivot query. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotRAM

open RAM

private theorem argmax_map_val {α β K : Type*} [LinearOrder K] (g : α → β) (score : β → K) (l : List α) :
    (l.map g).argmax score = (l.argmax (score ∘ g)).map g := by
  have fold (l : List α) (a : Option α) :
      (l.map g).foldl (List.argAux fun b c => score c < score b) (a.map g) =
        (l.foldl (List.argAux fun b c => score (g c) < score (g b)) a).map g := by
    induction l generalizing a with
    | nil => rfl
    | cons x tl ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [← ih]
      congr 1
      cases a with
      | none => rfl
      | some y => by_cases h : score (g y) < score (g x) <;> simp [List.argAux,h]
  exact fold l none

private theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

theorem incumbent_finRange {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : Memory K) (n : ℕ) :
    incumbent m n = (((List.finRange n).filter fun j => inputMinor m j.val ≠ 0).argmax
      (fun j => inputScore m j.val)).map Fin.val := by
  unfold incumbent
  rw [← finRange_values n, List.filter_map, argmax_map_val]
  rfl

/-- Agreement of selected pivot and RAM scan index, separated from the halted trace so
it also applies to a scan embedded in a larger machine program. -/
theorem incumbent_eq_pivotStep {n k : ℕ} (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n)
    (price : Fin n → ℚ) (f : PivotKey n → ℚ) (row : PivotRow n)
    (hr : MinorQuery.eval f (pivotStep D J price) = some row) (m : Memory ℚ)
    (hminor : ∀ j : Fin n, inputMinor m j.val = row.raw j)
    (hscore : ∀ j : Fin n, inputScore m j.val = row.logs j - price j) :
    incumbent m n = some row.pivot.val := by
  have hraw : ((List.finRange n).filter (fun j => decide (row.raw j ≠ 0))).argmax
      (fun j => row.logs j - price j) = some row.pivot := by
    let d := (Vector.ofFn (borderedMinor D J)).get
    let cells := (List.finRange n).filter fun j => d j ≠ 0
    let logs := MinorQuery.eval f (MinorQuery.readColumns (pivotKey J) cells 0)
    unfold pivotStep at hr
    rw [MinorQuery.eval_bind] at hr
    change Option.map (fun p => ⟨p,d,logs⟩) (cells.argmax (fun j => logs j - price j)) = some row at hr
    cases h : cells.argmax (fun j => logs j - price j) with
    | none => rw [h] at hr; contradiction
    | some p => rw [h] at hr; cases hr; exact h
  rw [incumbent_finRange]
  simp only [hminor, hscore, hraw, Option.map_some]

/-- The index returned by the compiled scan is the very same index used by `pivotStep`,
including equal-score ties. The initial triples here are the materialized entries of the
completed query, and the bound covers every scalar register at every instruction. -/
theorem scan_matches_pivotStep {n k : ℕ} (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n)
    (price : Fin n → ℚ) (f : PivotKey n → ℚ) (row : PivotRow n)
    (hr : MinorQuery.eval f (pivotStep D J price) = some row) (m : Memory ℚ) (B : ℕ)
    (hs : ∀ j, ratBits (m.data j) ≤ B) (hbase : 6 ≤ m.index 4) (hdim : m.index 0 = n)
    (hminor : ∀ j : Fin n, inputMinor m j.val = row.raw j)
    (hscore : ∀ j : Fin n, inputScore m j.val = row.logs j - price j) :
    ∃ count ≤ 19*n + 6, ∃ t : Fin (count+1) → State ℚ,
      Trace (scanBlock.compile 0 ++ [.halt 0]) (m.atPC 0) count t ∧
      (t (Fin.last count)).output = some 0 ∧ (t (Fin.last count)).index 3 = row.pivot.val ∧
      ∀ j, scalarBound (3+4*B) (t j) := by
  have hw := incumbent_eq_pivotStep D J price f row hr m hminor hscore
  obtain ⟨count,hcount,t,ht,ho,hi,hb⟩ := scan_trace m B hs hbase
  rw [hdim,hw] at hi
  exact ⟨count,hdim ▸ hcount,t,ht,ho,hi,hb⟩

end PivotRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
