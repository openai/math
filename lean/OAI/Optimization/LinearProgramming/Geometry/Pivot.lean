import OAI.Optimization.LinearProgramming.Geometry.PivotQueries
import OAI.Optimization.LinearProgramming.Geometry.PivotRounding
import OAI.Optimization.LinearProgramming.Geometry.Circuits
import OAI.Optimization.LinearProgramming.Elimination.Basic
import Mathlib.Data.List.MinMax
import Init.Data.Vector.OfFn

/-! Successive maximizing pivots for the geometric price oracle (Section 2). -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Finset SignType
open scoped Matrix

variable {n k m : ℕ}

/-- Row indices are always a prefix. Column order affects the signed determinant but does
not affect this key, since the compression procedure describes the absolute determinant. -/
abbrev PivotKey (n : ℕ) := ℕ × Finset (Fin n)

def pivotKey (J : Fin k → Fin n) (j : Fin n) : PivotKey n :=
  (k+1, insert j (Finset.univ.image J))

/-- A signed minor uses the package's determinant with a materialized table at every Bird stage. -/
def borderedMinor (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n) (j : Fin n) : ℚ :=
  Elimination.determinant (D.submatrix id (Fin.lastCases j J))

@[simp] theorem borderedMinor_eq (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n) (j : Fin n) :
    borderedMinor D J j = circuitMinor D J j := by
  exact Elimination.determinant_eq _

/-- The sign and the priced logarithm of each entry are retained for the resulting row. -/
structure PivotRow (n : ℕ) where
  pivot : Fin n
  raw : Fin n → ℚ
  logs : Fin n → ℚ

def PivotRow.rounded (r : PivotRow n) (price : Fin n → ℚ) (B : ℕ) : Fin n → ℚ :=
  pivotRound r.raw r.logs price r.pivot B

private def candidateList (raw : Fin n → ℚ) : List (Fin n) :=
  (List.finRange n).filter fun j => raw j ≠ 0

@[simp] private theorem mem_candidateList (raw : Fin n → ℚ) (j : Fin n) :
    j ∈ candidateList raw ↔ raw j ≠ 0 := by simp [candidateList]

/-- Compute all candidate minor signs, query the nonzero candidates in increasing index order,
and resolve tied maximal prices by the first column in that order. -/
def pivotStep (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n) (price : Fin n → ℚ) :
    MinorQuery (PivotKey n) (Option (PivotRow n)) :=
  let table := Vector.ofFn (borderedMinor D J)
  let raw := table.get
  let candidates := candidateList raw
  (MinorQuery.readColumns (pivotKey J) candidates 0).bind fun f =>
    .done ((candidates.argmax (fun j => f j - price j)).map (fun j => ⟨j, raw, f⟩))

/-- Characterization at every assignment extending the recorded minor replies. -/
structure PivotStepSpec (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n)
    (price : Fin n → ℚ) (f : PivotKey n → ℚ) (r : PivotRow n) : Prop where
  minors (j) : r.raw j = circuitMinor D J j
  replies (j) : r.raw j ≠ 0 → r.logs j = f (pivotKey J j)
  nonzero : r.raw r.pivot ≠ 0
  maximizing (j) : r.raw j ≠ 0 → r.logs j - price j ≤ r.logs r.pivot - price r.pivot

theorem pivotStep_bounded (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n) (price : Fin n → ℚ) :
    (pivotStep D J price).Bounded n := by
  unfold pivotStep
  let raw := (Vector.ofFn (borderedMinor D J)).get
  apply MinorQuery.bounded_mono (n := (candidateList raw).length + 0)
  · apply MinorQuery.bounded_bind
    · exact MinorQuery.readColumns_bounded ..
    · intro f; exact True.intro
  · simpa [candidateList] using List.length_filter_le (fun j : Fin n => decide (raw j ≠ 0)) (List.finRange n)

theorem pivotStep_eval (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n)
    (price : Fin n → ℚ) (f : PivotKey n → ℚ) (hD : LinearIndependent ℚ D.row)
    (hJ : (D.submatrix Fin.castSucc J).det ≠ 0) :
    ∃ r, MinorQuery.eval f (pivotStep D J price) = some r ∧ PivotStepSpec D J price f r := by
  let raw := (Vector.ofFn (borderedMinor D J)).get
  have hraw (j : Fin n) : raw j = circuitMinor D J j :=
    (Vector.getElem_ofFn (f := borderedMinor D J) j.isLt).trans (borderedMinor_eq D J j)
  let cols := candidateList raw
  let l := MinorQuery.eval f (MinorQuery.readColumns (pivotKey J) cols 0)
  obtain ⟨j, _, hj⟩ := exists_nonsingular_column_extension D J hD hJ
  have hin : j ∈ cols := (mem_candidateList raw _).mpr (by rwa [hraw])
  obtain ⟨p, hp⟩ : ∃ p, cols.argmax (fun i => l i - price i) = some p := by
    cases h : cols.argmax (fun i => l i - price i) with
    | some p => exact ⟨p,rfl⟩
    | none => exact False.elim (List.ne_nil_of_mem hin (List.argmax_eq_none.mp h))
  have hm := List.argmax_eq_some_iff.mp hp
  refine ⟨⟨p,raw,l⟩, ?_, ⟨hraw, ?_, (mem_candidateList _ _).mp hm.1, ?_⟩⟩
  · unfold pivotStep
    rw [MinorQuery.eval_bind]
    change Option.map _ (cols.argmax (fun i => l i - price i)) = _
    rw [hp]; rfl
  · intro u hu
    exact (MinorQuery.readColumns_eval (pivotKey J) cols 0 f u).trans (ite_eq_left ((mem_candidateList _ _).mpr hu))
  · intro u hu
    exact hm.2.1 u ((mem_candidateList _ _).mpr hu)

/-- For `a ≤ m`, perform the first `a` pivot stages. Failure means an empty candidate
list, which the full-row-rank proof below rules out. An oracle restart is a separate exit
in `MinorQuery.Run` and aborts the entire computation immediately. -/
def pivotPrefix (D : Matrix (Fin m) (Fin n) ℚ) (price : Fin n → ℚ) :
    (a : ℕ) → a ≤ m → MinorQuery (PivotKey n) (Option (Fin a → PivotRow n))
  | 0, _ => .done (some Fin.elim0)
  | a+1, ha => (pivotPrefix D price a (by omega)).bind fun
    | none => .done none
    | some rows => (pivotStep (D.submatrix (Fin.castLE ha) id) (fun j => (rows j).pivot) price).bind
        fun r => .done (r.map (fun row => Fin.lastCases row rows))

theorem pivotPrefix_bounded (D : Matrix (Fin m) (Fin n) ℚ) (price : Fin n → ℚ) (a) (ha : a ≤ m) :
    (pivotPrefix D price a ha).Bounded (a*n) := by
  induction a with
  | zero => exact True.intro
  | succ a ih =>
    rw [pivotPrefix, Nat.succ_mul]
    apply MinorQuery.bounded_bind _ _ (ih (by omega))
    rintro (_ | rows)
    · exact True.intro
    · exact MinorQuery.bounded_mono (MinorQuery.bounded_bind _ _ (pivotStep_bounded ..)
        (m := 0) (fun _ => True.intro)) (by omega)

/-- Every minor-query run, including an interrupted run, uses at most one request per
original column and prefix row. -/
theorem pivotPrefix_run_bound (D : Matrix (Fin m) (Fin n) ℚ) (price : Fin n → ℚ) (a) (ha : a ≤ m)
    {log out} (run : MinorQuery.Run (pivotPrefix D price a ha) log out) :
    log.length + MinorQuery.restartCost out ≤ a*n := run.call_bound (pivotPrefix_bounded ..)

/-- Pivots already found before row `s`. -/
def earlierPivots {a : ℕ} (rows : Fin a → PivotRow n) (s : Fin a) (j : Fin s.val) : Fin n :=
  (rows ⟨j.val, j.isLt.trans s.isLt⟩).pivot

private theorem earlierPivots_last {a : ℕ} (rows : Fin a → PivotRow n) (r : PivotRow n) :
    earlierPivots (Fin.lastCases r rows) (Fin.last a) = fun j => (rows j).pivot := by
  funext j
  change (Fin.lastCases (motive := fun _ => PivotRow n) r rows j.castSucc).pivot = _
  simp

private theorem earlierPivots_castSucc {a : ℕ} (rows : Fin a → PivotRow n) (r : PivotRow n)
    (s : Fin a) : earlierPivots (Fin.lastCases r rows) s.castSucc = earlierPivots rows s := by
  funext j
  change (Fin.lastCases (motive := fun _ => PivotRow n) r rows (Fin.castSucc ⟨j.val, j.isLt.trans s.isLt⟩)).pivot = _
  rw [Fin.lastCases_castSucc]
  rfl

/-- Exact invariant of the entire adaptive construction. Each `s` comes from the actual
first `s+1` rows and the actual previous pivots at this assignment, with the full signed
minor vector, all relevant replies, and a maximizing pivot. -/
structure PivotSystemSpec (D : Matrix (Fin m) (Fin n) ℚ) (price : Fin n → ℚ)
    (f : PivotKey n → ℚ) {a : ℕ} (ha : a ≤ m) (rows : Fin a → PivotRow n) : Prop where
  nonsingular : (D.submatrix (Fin.castLE ha) (fun j => (rows j).pivot)).det ≠ 0
  stage (s : Fin a) : PivotStepSpec (D.submatrix (Fin.castLE (Nat.le_trans s.isLt ha)) id)
    (earlierPivots rows s) price f (rows s)

theorem pivotPrefix_eval (D : Matrix (Fin m) (Fin n) ℚ) (price : Fin n → ℚ) (f : PivotKey n → ℚ)
    (a) (ha : a ≤ m) (hD : LinearIndependent ℚ D.row) :
    ∃ rows, MinorQuery.eval f (pivotPrefix D price a ha) = some rows ∧ PivotSystemSpec D price f ha rows := by
  induction a with
  | zero =>
    refine ⟨Fin.elim0, rfl, ⟨?_, fun s => Fin.elim0 s⟩⟩
    simp
  | succ a ih =>
    have ha' : a ≤ m := by omega
    obtain ⟨rows, hrows, hOld⟩ := ih ha'
    let A := D.submatrix (Fin.castLE ha) id
    let J := fun j => (rows j).pivot
    have hA : LinearIndependent ℚ A.row := hD.comp (Fin.castLE ha) (Fin.castLE_injective ha)
    have hJ : (A.submatrix Fin.castSucc J).det ≠ 0 := hOld.nonsingular
    obtain ⟨r, hr, h⟩ := pivotStep_eval A J price f hA hJ
    refine ⟨Fin.lastCases r rows, ?_, ?_⟩
    · simp only [pivotPrefix, MinorQuery.eval_bind, hrows]
      change Option.map _ (MinorQuery.eval f (pivotStep A J price)) = _
      rw [hr]; rfl
    · constructor
      · have hcols : (fun j => (Fin.lastCases (motive := fun _ => PivotRow n) r rows j).pivot) = Fin.lastCases r.pivot J := by
          funext j; refine Fin.lastCases ?_ (fun q => ?_) j <;> simp [J]
        rw [hcols]
        have hn := h.nonzero
        rw [h.minors] at hn
        exact hn
      · intro s
        refine Fin.lastCases ?_ (fun j => ?_) s
        · rw [earlierPivots_last, Fin.lastCases_last]
          exact h
        · rw [earlierPivots_castSucc, Fin.lastCases_castSucc]
          exact hOld.stage j

/-- The same rational output is valid for *every* assignment extending its answer prefix. -/
theorem pivotPrefix_run_correct (D : Matrix (Fin m) (Fin n) ℚ) (price : Fin n → ℚ)
    (a) (ha : a ≤ m) (hD : LinearIndependent ℚ D.row) {log out}
    (run : MinorQuery.Run (pivotPrefix D price a ha) log (.inr out))
    (f : PivotKey n → ℚ) (hext : ∀ e ∈ log, f e.1 = e.2) :
    ∃ rows, out = some rows ∧ PivotSystemSpec D price f ha rows := by
  obtain ⟨rows, hr, hrows⟩ := pivotPrefix_eval D price f a ha hD
  exact ⟨rows, (run.eval_of_extends f hext).symm.trans hr, hrows⟩

namespace PivotSystemSpec

variable {D : Matrix (Fin m) (Fin n) ℚ} {price : Fin n → ℚ} {f : PivotKey n → ℚ}
    {a : ℕ} {ha : a ≤ m} {rows : Fin a → PivotRow n}

theorem earlier_zero (cert : PivotSystemSpec D price f ha rows) (r s : Fin a) (hrs : r < s) :
    (rows s).raw (rows r).pivot = 0 := by
  rw [(cert.stage s).minors]
  let j : Fin s.val := ⟨r.val, hrs⟩
  exact circuitMinor_of_mem_columns _ (earlierPivots rows s) j

theorem rounded_triangular (cert : PivotSystemSpec D price f ha rows) (B : ℕ) :
    (∀ s, (rows s).rounded price B (rows s).pivot = 1) ∧
    (∀ r s, r < s → (rows s).rounded price B (rows r).pivot = 0) ∧
    (∀ s j, |(rows s).rounded price B j| ≤ 1) :=
  ⟨fun s => pivotRound_pivot _ _ _ _ _ (cert.stage s).nonzero,
   fun r s h => pivotRound_zero _ _ _ _ _ _ (cert.earlier_zero r s h),
   fun s j => abs_pivotRound_le_one (rows s).raw _ _ _ _ j⟩

theorem rounded_approximates (cert : PivotSystemSpec D price f ha rows) (B : ℕ) (s : Fin a) (j : Fin n) :
    |((rows s).rounded price B j : ℝ) - (sign (((rows s).raw (rows s).pivot : ℚ) : ℝ) : ℝ) *
      normalizedMinorRow (fun u => ((rows s).raw u : ℝ)) (fun u => ((rows s).logs u : ℝ))
        (fun u => (price u : ℝ)) j| ≤ (1 / 2 : ℝ) ^ B :=
  pivotRound_error _ _ _ _ _ (cert.stage s).nonzero (cert.stage s).maximizing j

end PivotSystemSpec
end Geometry
end LinearProgramming
end Optimization
end OAI
