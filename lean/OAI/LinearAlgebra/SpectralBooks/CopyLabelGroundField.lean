import OAI.LinearAlgebra.SpectralBooks.CopyLabelLimit
import OAI.LinearAlgebra.SpectralBooks.SpectrumExtension
import OAI.LinearAlgebra.SpectralBooks.CopyLabelOutput
import OAI.LinearAlgebra.SpectralBooks.FinitePlacementDiameter
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The copying inequality over arbitrary ground fields

Extend a ground spectral point to the algebraic closure with the same values on
all extended tensors. The old coefficients, appended label, and placed diagonals
commute with extension, so the inequality over the infinite closure descends.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor

noncomputable section
open scoped Classical

variable {I : Type} {K : Type*} [Field K]

private theorem mapScalars_appendLabel {L : Type*} [Field L] (f : K →+* L)
    (T : Raw.{0} I K) (s : I) (D : Type) [Fintype D] (label : (∀ i, T.Leg i) → D) :
    (T.appendLabel s D label).mapScalars f = (T.mapScalars f).appendLabel s D label := by
  unfold Raw.appendLabel Raw.mapScalars
  congr 1
  funext x
  dsimp only
  rw [apply_ite f, map_zero]

/-- Grouped diagonal tensors commute with scalar extension, including placements
with repeated sites. -/
theorem Raw.mapScalars_group_diagonal {L : Type*} [Field L] (f : K →+* L)
    {H : Type} [Fintype H] (σ : H → I) (D : Type) [Fintype D] :
    ((Raw.diagonal H K D).group σ).mapScalars f = (Raw.diagonal H L D).group σ := by
  unfold Raw.group Raw.diagonal Raw.mapScalars
  congr 1
  funext x
  dsimp only
  simp only [map_sum, apply_ite f, map_one, map_zero]
  apply Finset.sum_congr rfl
  intro d _
  split <;> rfl

variable [Fintype I] [Nonempty I]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))

/-- For every field, a label shared by the first two marked slots can be copied
to the third slot at the difference of the corresponding diagonal and wire
prices per label bit. -/
theorem rawLogPrice_copy (c : ℝ) (hc : 0 ≤ c) (T : Raw.{0} I K) (σ : Fin 3 → I)
    {q : ℕ} (hq : 0 < q) (hA : T.Leg (σ 0) → Fin q) (hB : T.Leg (σ 1) → Fin q)
    (hmatch : ∀ x, T.coeff x ≠ 0 → hA (x (σ 0)) = hB (x (σ 1))) :
    rawLogPrice φ c (T.appendLabel (σ 2) (Fin q) (fun x => hA (x (σ 0)))) ≤
      rawLogPrice φ c T + (rawLogPrice φ c ((Raw.diagonal (Fin 3) K (Fin 2)).group σ) -
        rawWireDistance φ c (σ 0) (σ 1)) * Real.logb 2 q := by
  by_cases hT : T.coeff = 0
  · have hz := not_congr (Raw.appendLabel_nonzero_iff T (σ 2) (Fin q) (fun x => hA (x (σ 0))))
    rw [rawLogPrice_zero φ c _ (not_ne_iff.mp (hz.mpr (not_ne_iff.mpr hT))),
      rawLogPrice_zero φ c _ hT, zero_add]
    exact mul_nonneg (sub_nonneg.mpr (rawWireDistance_le_group_diagonal φ hc σ 0 1))
      (Real.logb_nonneg (by norm_num) (by exact_mod_cast hq))
  let L := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  obtain ⟨ψ, hψ⟩ := exists_spectrum_mapScalars (K := L) φ
  have price (X : Raw.{0} I K) : rawLogPrice ψ c (X.mapScalars f) = rawLogPrice φ c X :=
    congrArg (fun z : NNReal => c * Real.logb 2 (z : ℝ)) (hψ (ofRaw X))
  have hnonzero : (T.mapScalars f).coeff ≠ 0 := by
    intro hz
    apply hT
    funext x
    exact f.injective ((congrFun hz x).trans f.map_zero.symm)
  have hm (x : ∀ i, T.Leg i) (hx : (T.mapScalars f).coeff x ≠ 0) :
      hA (x (σ 0)) = hB (x (σ 1)) :=
    hmatch x (fun h => hx ((congrArg f h).trans f.map_zero))
  have h := rawLogPrice_copy_infinite ψ c hc (T.mapScalars f) σ hq hA hB hm hnonzero
  unfold rawWireDistance at h ⊢
  rw [← price (T.appendLabel _ _ _), ← price T,
    ← price ((Raw.diagonal (Fin 3) K (Fin 2)).group σ),
    ← price ((Raw.diagonal (Fin 2) K (Fin 2)).group ![σ 0, σ 1]),
    Raw.mapScalars_group_diagonal, Raw.mapScalars_group_diagonal, mapScalars_appendLabel]
  exact h

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
