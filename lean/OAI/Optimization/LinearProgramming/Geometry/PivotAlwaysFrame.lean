import OAI.Optimization.LinearProgramming.Geometry.PivotBasis
import Init.Data.Vector.OfFn

/-! The rounded pivot frame remains triangular for every possible sequence of rational
replies, including histories with repeated or mutually inconsistent answers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Finset

namespace MinorQuery

/-- A postcondition holds at every completed leaf of a query tree. -/
def AllReturns {κ α : Type*} (q : MinorQuery κ α) (P : α → Prop) : Prop :=
  match q with
  | .done x => P x
  | .query _ k => ∀ v, AllReturns (k v) P

theorem AllReturns.trivial {κ α : Type*} (q : MinorQuery κ α) : q.AllReturns (fun _ => True) := by
  induction q with
  | done => trivial
  | query _ _ ih => exact ih

theorem AllReturns.bind {κ α β : Type*} (q : MinorQuery κ α) (k : α → MinorQuery κ β) {P : α → Prop} {Q : β → Prop}
    (h : q.AllReturns P) (next : ∀ a, P a → (k a).AllReturns Q) : (q.bind k).AllReturns Q := by
  induction q with
  | done a => exact next a h
  | query key cont ih => exact fun v => ih v (h v)

def ReturnPost {κ α : Type*} (P : α → Prop) : Sum κ α → Prop
  | .inr v => P v
  | .inl _ => True

theorem AllReturns.run {κ α : Type*} {q : MinorQuery κ α} {xs res} (hr : Run q xs res) {P : α → Prop}
    (h : q.AllReturns P) : ReturnPost P res := by
  induction hr with
  | done _ => exact h
  | restart => trivial
  | answer _ _ v _ ih => exact ih (h v)

end MinorQuery

/-- The three rational conditions that imply both rational independence and the
real conditioning bound for the rounded geometric oracle. -/
structure RoundedTriangular {n a : ℕ} (rows : Fin a → PivotRow n) (t : Fin n → ℚ) (B : ℕ) : Prop where
  diag (s) : (rows s).rounded t B (rows s).pivot = 1
  zeros (i j : Fin a) : i < j → (rows j).rounded t B (rows i).pivot = 0
  bounded (i j) : |(rows i).rounded t B j| ≤ 1

private theorem RoundedTriangular.snoc {n a B : ℕ} {rows : Fin a → PivotRow n} {row : PivotRow n} {t : Fin n → ℚ}
    (old : RoundedTriangular rows t B) (hd : row.rounded t B row.pivot = 1)
    (hz : ∀ q, row.rounded t B (rows q).pivot = 0) : RoundedTriangular (Fin.lastCases row rows) t B := by
  constructor
  · intro s
    refine Fin.lastCases ?_ (fun q => ?_) s
    · simpa only [Fin.lastCases_last] using hd
    · simpa only [Fin.lastCases_castSucc] using old.diag q
  · intro i j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · refine Fin.lastCases ?_ (fun p => ?_) i
      · intro less; exact (lt_irrefl _ less).elim
      · intro _; simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using hz p
    · refine Fin.lastCases ?_ (fun p => ?_) i
      · intro less; change a < q.val at less; have := q.isLt; omega
      · intro less; simpa only [Fin.lastCases_castSucc] using old.zeros p q less
  · intro s j; exact abs_pivotRound_le_one _ _ _ _ _ _

/-- The part of one pivot stage that uses only signs and rational answers. -/
def selectingRow {κ : Type*} {n : ℕ} (raw : Fin n → ℚ) (key : Fin n → κ) (t : Fin n → ℚ) :
    MinorQuery κ (Option (PivotRow n)) :=
  let cols := (List.finRange n).filter fun j => raw j ≠ 0
  (MinorQuery.readColumns key cols 0).bind fun f =>
    .done ((cols.argmax (fun j => f j-t j)).map fun j => ⟨j,raw,f⟩)

/-- Any selected row has a unit pivot and vanishes on the previous pivot columns,
including for mutually inconsistent answers to other stages. -/
theorem selectingRow_all {κ : Type*} {a n : ℕ} (raw : Fin n → ℚ) (key : Fin n → κ) (J : Fin a → Fin n)
    (t : Fin n → ℚ) (B : ℕ) (zeros : ∀ q, raw (J q)=0) :
    MinorQuery.AllReturns (selectingRow raw key t) (fun opt => ∀ row, opt = some row →
      row.rounded t B row.pivot = 1 ∧ ∀ q, row.rounded t B (J q) = 0) := by
  unfold selectingRow
  let cols := (List.finRange n).filter fun j => raw j ≠ 0
  apply MinorQuery.AllReturns.bind _ _ (MinorQuery.AllReturns.trivial _)
  intro f _
  change ∀ row, (cols.argmax (fun j => f j-t j)).map (fun j => PivotRow.mk j raw f) = some row → _
  cases hp : cols.argmax (fun j => f j-t j) with
  | none => simp
  | some p =>
    intro row he
    simp only [Option.map_some,Option.some.injEq] at he
    subst row
    have member := (List.argmax_eq_some_iff.mp hp).1
    have pnz : raw p ≠ 0 := by simpa [cols] using member
    exact ⟨pivotRound_pivot _ _ _ _ _ pnz, fun q => pivotRound_zero _ _ _ _ _ _ (zeros q)⟩

/-- Appending a row actually returned by a pivot query preserves triangularity on every leaf. -/
theorem roundedStage_extend {κ : Type*} {a n B : ℕ} {t : Fin n → ℚ}
    (rows : Fin a → PivotRow n) (stage : MinorQuery κ (Option (PivotRow n)))
    (old : RoundedTriangular rows t B)
    (next : stage.AllReturns fun opt => ∀ row, opt=some row →
      row.rounded t B row.pivot=1 ∧ ∀ q, row.rounded t B (rows q).pivot=0) :
    (stage.bind fun r => .done (r.map (fun row => Fin.lastCases row rows))).AllReturns
      (fun opt => ∀ rs, opt=some rs → RoundedTriangular rs t B) := by
  apply MinorQuery.AllReturns.bind _ _ next
  rintro (_ | row) h
  · intro _ eq; cases eq
  · intro rs he
    change some (Fin.lastCases row rows) = some rs at he
    cases Option.some.inj he
    obtain ⟨hd,hz⟩ := h row rfl
    exact old.snoc hd hz

/-- Extend a pivot prefix after the literal query selecting its next row. -/
theorem roundedPrefix_extend {κ : Type*} {a n B : ℕ} {t : Fin n → ℚ}
    (old : MinorQuery κ (Option (Fin a → PivotRow n)))
    (stage : (Fin a → PivotRow n) → MinorQuery κ (Option (PivotRow n)))
    (hOld : MinorQuery.AllReturns old fun opt => ∀ rows, opt=some rows → RoundedTriangular rows t B)
    (hStage : ∀ rows, MinorQuery.AllReturns (stage rows) fun opt => ∀ row, opt=some row →
      row.rounded t B row.pivot=1 ∧ ∀ q, row.rounded t B (rows q).pivot=0) :
    MinorQuery.AllReturns (old.bind fun
      | none => .done none
      | some rows => (stage rows).bind fun r => .done (r.map (fun row => Fin.lastCases row rows)))
      (fun opt => ∀ rows, opt=some rows → RoundedTriangular rows t B) := by
  apply MinorQuery.AllReturns.bind _ _ hOld
  rintro (_ | rows) hist
  · intro _ eq; cases eq
  · exact roundedStage_extend rows (stage rows) (hist rows rfl) (hStage rows)

private theorem step_all {a n : ℕ} (D : Matrix (Fin (a+1)) (Fin n) ℚ) (J : Fin a → Fin n) (t : Fin n → ℚ) (B : ℕ) :
    MinorQuery.AllReturns (pivotStep D J t) (fun opt => ∀ row, opt = some row →
      row.rounded t B row.pivot = 1 ∧ ∀ q, row.rounded t B (J q) = 0) := by
  apply selectingRow_all (Vector.ofFn (borderedMinor D J)).get (pivotKey J) J t B
  intro q
  exact (Vector.getElem_ofFn (f := borderedMinor D J) (J q).isLt).trans
    ((borderedMinor_eq D J (J q)).trans (circuitMinor_of_mem_columns D J q))

private theorem prefix_all {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (t : Fin n → ℚ) (B a : ℕ) (ha : a ≤ m) :
    MinorQuery.AllReturns (pivotPrefix D t a ha) (fun opt => ∀ rows, opt=some rows → RoundedTriangular rows t B) := by
  induction a with
  | zero =>
    intro rows he
    cases Option.some.inj he
    exact ⟨fun j => j.elim0,fun j => j.elim0,fun j => j.elim0⟩
  | succ a ih =>
    rw [pivotPrefix]
    apply MinorQuery.AllReturns.bind _ _ (ih (by omega))
    rintro (_ | rows) old
    · intro _ eq; cases eq
    · exact roundedStage_extend rows _ (old rows rfl)
        (step_all (D.submatrix (Fin.castLE ha) id) (fun j => (rows j).pivot) t B)

/-- Every successful adaptive transcript, with no assignment-extension hypothesis,
produces a unit upper-triangular minor of the actual rational rounded matrix. -/
theorem prefix_run_rounded_triangular {m n a : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (t : Fin n → ℚ) (ha : a ≤ m)
    {rows : Fin a → PivotRow n} {xs} (hr : MinorQuery.Run (pivotPrefix D t a ha) xs (.inr (some rows))) (B : ℕ) :
    RoundedTriangular rows t B :=
  MinorQuery.AllReturns.run hr (prefix_all D t B a ha) rows rfl

theorem RoundedTriangular.independent {a n B : ℕ} {rows : Fin a → PivotRow n} {t : Fin n → ℚ}
    (shape : RoundedTriangular rows t B) : LinearIndependent ℚ (roundedPivotMatrix rows t B).row := by
  let p i := (rows i).pivot
  let R := (roundedPivotMatrix rows t B).submatrix id p
  have upper : R.IsUpperTriangular := fun i j lt => shape.zeros j i lt
  have determinant : R.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular upper]
    simp [R,p,roundedPivotMatrix,shape.diag]
  let sub : (Fin n → ℚ) →ₗ[ℚ] (Fin a → ℚ) := LinearMap.pi fun j => LinearMap.proj (p j)
  apply LinearIndependent.of_comp sub
  exact Matrix.linearIndependent_rows_of_det_ne_zero (determinant ▸ one_ne_zero)

theorem RoundedTriangular.isPivotFrame {a n B : ℕ} {rows : Fin a → PivotRow n} {t : Fin n → ℚ}
    (shape : RoundedTriangular rows t B) : IsPivotFrame ((roundedPivotMatrix rows t B).map (Rat.castHom ℝ)) (fun s => (rows s).pivot) := by
  constructor
  · intro i; change ((rows i).rounded t B (rows i).pivot : ℝ) = 1; exact_mod_cast shape.diag i
  · intro i j h; change ((rows j).rounded t B (rows i).pivot : ℝ) = 0; exact_mod_cast shape.zeros i j h
  · intro i j; change |((rows i).rounded t B j : ℝ)| ≤ 1; exact_mod_cast shape.bounded i j

theorem prefix_run_rounded_independent {m n a : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (t : Fin n → ℚ) (ha : a ≤ m)
    {rows : Fin a → PivotRow n} {xs} (hr : MinorQuery.Run (pivotPrefix D t a ha) xs (.inr (some rows))) (B : ℕ) :
    LinearIndependent ℚ (roundedPivotMatrix rows t B).row := (prefix_run_rounded_triangular D t ha hr B).independent

end Geometry
end LinearProgramming
end Optimization
end OAI
