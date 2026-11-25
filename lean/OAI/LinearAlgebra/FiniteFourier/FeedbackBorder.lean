import OAI.LinearAlgebra.FiniteFourier.Feedback

/-! # Geometric border of binary feedback systems

We take the affine Zariski closure of all regular binary feedback systems of bounded
size over the algebraic closure. Equivalently, every polynomial that vanishes on
the locus of their transfer matrices must also vanish on the candidate matrix.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

variable {K L I O : Type*} [Field K] [Field L] {s : ℕ}

private def mapReadout {W : Type*} (f : K →+* L) : Readout K W → Readout L W
  | .zero => .zero
  | .scaled c w => .scaled (f c) w

namespace Feedback

/-- Keep all wires and extend their weights along a field embedding. -/
def mapCoeffs (F : Feedback K I O s) (f : K →+* L) : Feedback L I O s where
  equation i :=
    let g := F.equation i
    ⟨g.left, g.right, f g.leftCoeff, f g.rightCoeff⟩
  output o := mapReadout f (F.output o)

private theorem gateRow_map {W : Type*} (g : BinaryGate K W) (f : K →+* L) (w : W) :
    gateRow (⟨g.left, g.right, f g.leftCoeff, f g.rightCoeff⟩ : BinaryGate L W) w =
      f (gateRow g w) := by
  classical
  simp only [gateRow, Pi.add_apply, Pi.single_apply, map_add]
  split_ifs <;> simp

private theorem readRow_map {W : Type*} (g : Readout K W) (f : K →+* L) (w : W) :
    readRow (mapReadout f g) w =
      f (readRow g w) := by
  classical
  cases g with
  | zero => simp [mapReadout, readRow]
  | scaled c z => by_cases h : w = z <;> simp [mapReadout, readRow, h]

private theorem stateDifference_map (F : Feedback K I O s) (f : K →+* L) :
    1 - (F.mapCoeffs f).stateMatrix = (1 - F.stateMatrix).map f := by
  ext i j
  simp [stateMatrix, mapCoeffs, Matrix.one_apply, apply_ite, gateRow_map]

theorem regular_mapCoeffs {F : Feedback K I O s} (h : F.Regular) (f : K →+* L) :
    (F.mapCoeffs f).Regular := by
  unfold Regular at *
  rw [stateDifference_map]
  intro hz
  apply h
  apply f.injective
  exact (f.map_det _).trans (hz.trans (map_zero f).symm)

theorem matrix_mapCoeffs {F : Feedback K I O s} (h : F.Regular) (f : K →+* L) :
    (F.mapCoeffs f).matrix = F.matrix.map f := by
  have hInv : ((1 - F.stateMatrix).map f)⁻¹ = (1 - F.stateMatrix)⁻¹.map f := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  have hInput : (F.mapCoeffs f).inputMatrix = F.inputMatrix.map f := by
    ext i j
    exact gateRow_map _ _ _
  have hRead : (F.mapCoeffs f).readState = F.readState.map f := by
    ext o j
    exact readRow_map (F.output o) f (.inr j)
  have hDirect : (F.mapCoeffs f).readInput = F.readInput.map f := by
    ext o j
    exact readRow_map (F.output o) f (.inl j)
  simp [Matrix.map_add f (map_add f), matrix, stateDifference_map, hInv, hInput, hRead, hDirect]

end Feedback

/-- Matrices of regular feedback systems with at most the prescribed number of states. -/
def FeedbackAtMost (M : Matrix O I K) (S : ℕ) : Prop :=
  ∃ s ≤ S, ∃ F : Feedback K I O s, F.Realizes M

theorem FeedbackAtMost.map {M : Matrix O I K} {S : ℕ} (h : FeedbackAtMost M S)
    (f : K →+* L) : FeedbackAtMost (M.map f) S := by
  obtain ⟨s, hs, F, hF, rfl⟩ := h
  exact ⟨s, hs, F.mapCoeffs f, F.regular_mapCoeffs hF f, F.matrix_mapCoeffs hF f⟩

/-- Membership of the scalar-extended matrix in the Zariski closure of regular
binary feedback systems with at most `S` states. -/
def GeometricBorderAtMost (M : Matrix O I K) (S : ℕ) : Prop :=
  ∀ p : MvPolynomial (O × I) (AlgebraicClosure K),
    (∀ A : Matrix O I (AlgebraicClosure K), FeedbackAtMost A S →
      MvPolynomial.eval (fun ij => A ij.1 ij.2) p = 0) →
    MvPolynomial.eval (fun ij => algebraMap K (AlgebraicClosure K) (M ij.1 ij.2)) p = 0

theorem FeedbackAtMost.geometricBorder {M : Matrix O I K} {S : ℕ} (h : FeedbackAtMost M S) :
    GeometricBorderAtMost M S := by
  intro p hp
  exact hp (M.map (algebraMap K (AlgebraicClosure K))) (h.map _)

theorem GeometricBorderAtMost.mono {M : Matrix O I K} {s t : ℕ}
    (h : GeometricBorderAtMost M s) (hst : s ≤ t) : GeometricBorderAtMost M t := by
  intro p hp
  apply h p
  rintro A ⟨r, hr, F, hF⟩
  exact hp A ⟨r, hr.trans hst, F, hF⟩

end

end FiniteFourier
end LinearAlgebra
end OAI
