import OAI.LinearAlgebra.FiniteFourier.GeometricNewton
import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization

/-! # The factors of a geometric grid

The geometric-grid theorem allows evaluation at distinct geometric nodes, its inverse,
and either orientation of a triangular Toeplitz matrix with nonzero main diagonal.
These conditions persist when the entries are embedded in a working field.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix ExactFourier.CoefficientTime
open scoped Matrix

variable {K E : Type*} [Field K] [Field E] {a : ℕ}

/-- An allowed axis matrix of the geometric-grid theorem. The axis length
condition `2 ≤ a` is imposed on the family of axes. -/
inductive GridFactor : Matrix (Fin a) (Fin a) K → Prop
  | geometric (q : K) (hq : q ≠ 0) (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val)) :
      GridFactor (geometricMatrix a q)
  | inverseGeometric (q : K) (hq : q ≠ 0) (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val)) :
      GridFactor (geometricMatrix a q)⁻¹
  | lower (f : PowerSeries K) (hf : f.constantCoeff ≠ 0) : GridFactor (truncMatrix a f)
  | upper (f : PowerSeries K) (hf : f.constantCoeff ≠ 0) : GridFactor (truncMatrix a f)ᵀ

theorem map_geometricMatrix (φ : K →+* E) (q : K) :
    (geometricMatrix a q).map φ = geometricMatrix a (φ q) := by
  ext i j
  simp

theorem map_geometricMatrix_inv (φ : K →+* E) (q : K)
    (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val)) :
    ((geometricMatrix a q)⁻¹).map φ = (geometricMatrix a (φ q))⁻¹ := by
  rw [← map_geometricMatrix φ q]
  refine (Matrix.inv_eq_right_inv ?_).symm
  change φ.mapMatrix (geometricMatrix a q) * φ.mapMatrix (geometricMatrix a q)⁻¹ = 1
  rw [← map_mul, Matrix.mul_nonsing_inv (geometricMatrix a q) (Matrix.det_vandermonde_ne_zero_iff.mpr hd).isUnit,
    map_one]

theorem map_truncMatrix (φ : K →+* E) (f : PowerSeries K) :
    (truncMatrix a f).map φ = truncMatrix a (f.map φ) := by
  ext i j
  simp [truncMatrix, apply_ite φ]

theorem GridFactor.map {A : Matrix (Fin a) (Fin a) K} (hA : GridFactor A) (φ : K →+* E) :
    GridFactor (A.map φ) := by
  have nodes (q : K) (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val)) :
      Function.Injective (fun i : Fin a ↦ (φ q) ^ i.val) := by
    simpa [Function.comp_def] using φ.injective.comp hd
  have coeff (f : PowerSeries K) (hf : f.constantCoeff ≠ 0) :
      (f.map φ).constantCoeff ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
      using ((map_ne_zero φ).mpr hf)
  cases hA with
  | geometric q hq hd =>
    rw [map_geometricMatrix]
    exact .geometric _ ((map_ne_zero φ).mpr hq) (nodes q hd)
  | inverseGeometric q hq hd =>
    rw [map_geometricMatrix_inv φ q hd]
    exact .inverseGeometric _ ((map_ne_zero φ).mpr hq) (nodes q hd)
  | lower f hf =>
    rw [map_truncMatrix]
    exact .lower _ (coeff f hf)
  | upper f hf =>
    change GridFactor ((truncMatrix a f).map φ)ᵀ
    rw [map_truncMatrix]
    exact .upper _ (coeff f hf)

/-- The same seven-factor bound covers every allowed axis matrix. -/
theorem GridFactor.factor_list {A : Matrix (Fin a) (Fin a) K} (hA : GridFactor A) :
    ∃ factors : List (Matrix (Fin a) (Fin a) K), factors.length ≤ 7 ∧
      (∀ B ∈ factors, IsGridDiagonalOrToeplitz B) ∧ factors.prod = A := by
  cases hA with
  | geometric q hq hd => exact geometricMatrix_and_inverse_factors q hq hd _ (Or.inl rfl)
  | inverseGeometric q hq hd => exact geometricMatrix_and_inverse_factors q hq hd _ (Or.inr rfl)
  | lower f hf =>
    exact ⟨[truncMatrix a f], by simp, by simpa using IsGridDiagonalOrToeplitz.lower (a := a) f hf, by simp⟩
  | upper f hf =>
    exact ⟨[(truncMatrix a f)ᵀ], by simp, by simpa using IsGridDiagonalOrToeplitz.upper (a := a) f hf, by simp⟩

/-- Embedding all coefficients of the tensor product gives the tensor product
of the embedded factors. -/
theorem map_gridTensor {ι : Type*} [Fintype ι] {I : ι → Type*}
    (φ : K →+* E) (A : ∀ i, Matrix (I i) (I i) K) :
    (gridTensor A).map φ = gridTensor (fun i ↦ (A i).map φ) := by
  ext i j
  simp [gridTensor]

end FiniteFourier
end LinearAlgebra
end OAI
