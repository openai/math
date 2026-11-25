import OAI.Optimization.LinearProgramming.Geometry.Pivot
import OAI.Optimization.LinearProgramming.Geometry.FrameControl
import OAI.Optimization.LinearProgramming.Geometry.MinorKeys

/-! The rational triangular output and the full compressed assignments used in its proof. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Finset Submodule SignType
open scoped Matrix

variable {a m n : ℕ}

/-- Rows passed to the rational Gram projector by the geometric test. -/
def roundedPivotMatrix (rows : Fin a → PivotRow n) (price : Fin n → ℚ) (B : ℕ) :
    Matrix (Fin a) (Fin n) ℚ := fun s => (rows s).rounded price B

/-- The actual row family with signs determined at the selected pivots. -/
noncomputable def exactPivotFrameRow (rows : Fin a → PivotRow n) (price : Fin n → ℚ)
    (f : PivotKey n → ℚ) (s : Fin a) (j : Fin n) : ℝ :=
  (sign (((rows s).raw (rows s).pivot : ℚ) : ℝ) : ℝ) *
    normalizedMinorRow (fun u => ((rows s).raw u : ℝ))
      (fun u => (f (prefixMinorKey (earlierPivots rows s) u) : ℝ))
      (fun u => (price u : ℝ)) j

/-- At zero minor entries no request is necessary, even when the full assignment there
is subsequently supplied by a different extension. -/
theorem normalizedMinorRow_congr_logs {ι : Type*} [Fintype ι] (raw t l g : ι → ℝ)
    (h : ∀ i, raw i ≠ 0 → l i = g i) : normalizedMinorRow raw l t = normalizedMinorRow raw g t := by
  have he : pricedMinorRow raw l t = pricedMinorRow raw g t := by
    funext j
    by_cases hj : raw j = 0
    · simp [pricedMinorRow, hj]
    · simp [pricedMinorRow, h j hj]
  funext j
  simp only [normalizedMinorRow, he]

namespace PivotSystemSpec

variable {D : Matrix (Fin m) (Fin n) ℚ} {price : Fin n → ℚ} {f : PivotKey n → ℚ}
    {ha : a ≤ m} {rows : Fin a → PivotRow n}

theorem isPivotFrame (cert : PivotSystemSpec D price f ha rows) (B : ℕ) :
    IsPivotFrame ((roundedPivotMatrix rows price B).map (Rat.castHom ℝ)) (fun s => (rows s).pivot) := by
  obtain ⟨hd, hz, hb⟩ := cert.rounded_triangular B
  constructor
  · intro s
    change ((rows s).rounded price B (rows s).pivot : ℝ) = 1
    exact_mod_cast hd s
  · intro r s hrs
    change ((rows s).rounded price B (rows r).pivot : ℝ) = 0
    exact_mod_cast hz r s hrs
  · intro s j
    change |((rows s).rounded price B j : ℝ)| ≤ 1
    exact_mod_cast hb s j

theorem rounded_approximates_extension (cert : PivotSystemSpec D price f ha rows)
    (B : ℕ) (s : Fin a) (j : Fin n) :
    |(roundedPivotMatrix rows price B s j : ℝ) - exactPivotFrameRow rows price f s j| ≤
      (1 / 2 : ℝ) ^ B := by
  have hg := normalizedMinorRow_congr_logs (fun u => ((rows s).raw u : ℝ))
    (fun u => (price u : ℝ)) (fun u => ((rows s).logs u : ℝ))
    (fun u => (f (prefixMinorKey (earlierPivots rows s) u) : ℝ)) (by
      intro u hu
      exact_mod_cast (cert.stage s).replies u (by exact_mod_cast hu))
  simpa only [roundedPivotMatrix, exactPivotFrameRow, hg] using cert.rounded_approximates B s j

/-- The uncompressed signed input to every rounded frame row belongs to the real row
space of the original rational matrix, including proper prefixes. -/
theorem raw_mem_realRowSpan (cert : PivotSystemSpec D price f ha rows) (s : Fin a) :
    (fun j => ((rows s).raw j : ℝ)) ∈ span ℝ (Set.range (D.map (Rat.castHom ℝ)).row) := by
  let idx := Fin.castLE (Nat.le_trans s.isLt ha)
  let J := earlierPivots rows s
  have he : (fun j => ((rows s).raw j : ℝ)) =
      circuitMinor ((D.map (Rat.castHom ℝ)).submatrix idx id) J := by
    funext j
    rw [(cert.stage s).minors]
    change (Rat.castHom ℝ) (((D.submatrix idx id).submatrix id (Fin.lastCases j J)).det) = _
    rw [RingHom.map_det]
    rfl
  rw [he]
  exact circuitMinor_rowPrefix_mem_rowSpan _ _ _

/-- Actual requesting indices are sorted square-minor indices of the original matrix.
The unordered column set erases only the determinant sign. -/
theorem requested_key_spec (cert : PivotSystemSpec D price f ha rows) (s : Fin a) (j : Fin n)
    (hj : (rows s).raw j ≠ 0) :
    ∃ u : Compression.SquareMinorIndex m n,
      canonicalPrefixIndex m (pivotKey (earlierPivots rows s) j) = some u ∧
        |(D.submatrix u.2.1 u.2.2).det| = |(rows s).raw j| := by
  rw [(cert.stage s).minors] at hj ⊢
  exact canonicalPrefixIndex_spec D (Nat.le_trans s.isLt ha) (earlierPivots rows s) j hj

end PivotSystemSpec
end Geometry
end LinearProgramming
end Optimization
end OAI
