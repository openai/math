import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # A transvection on two selected registers

A unit transvection is a single shear layer, with every unused register in an identity
block. Diagonal conjugation gives an arbitrary scalar transvection.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix

variable {K : Type*} {I : Type} [Fintype I] [DecidableEq I]

section Ring

variable [CommRing K]

private theorem shear_eq_transvection :
    unitShear K = transvection (0 : Fin 2) 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unitShear, transvection, Matrix.one_apply, Matrix.single_apply]

theorem LayerMatrix.unitTransvection {i j : I} (hij : i ≠ j) :
    LayerMatrix .shear (transvection i j (1 : K)) := by
  classical
  let f : Fin 2 → I := ![i, j]
  have hf : Function.Injective f := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp [f, hij, hij.symm]
  let R := (Set.range f)ᶜ
  let e : Fin 2 ⊕ (R : Set I) ≃ I :=
    ((Equiv.ofInjective f hf).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range f))
  have h₀ : e (.inl 0) = i := rfl
  have h₁ : e (.inl 1) = j := rfl
  have hblock : LayerMatrix .shear
      (transvection (Sum.inl (0 : Fin 2) : Fin 2 ⊕ (R : Set I)) (.inl 1) (1 : K)) := by
    have hb := (LayerMatrix.unitShear (K := K)).parallel
      (LayerMatrix.id .shear (I := (R : Set I)) (K := K))
    rw [shear_eq_transvection] at hb
    convert hb using 2
    ext (a | a) (b | b) <;>
      simp [transvection, Matrix.single_apply, Matrix.one_apply, Matrix.fromBlocks]
  have he := hblock.relabel e
  simpa [transvection, Matrix.submatrix_add, Matrix.submatrix_one_equiv, h₀, h₁] using he

/-- Conjugate the unit shear using a unit diagonal on the target register. -/
theorem layerWord_transvection_unit {i j : I} (hij : i ≠ j) (c : Kˣ) :
    LayerWord 3 (transvection i j (c : K)) := by
  let d (a : I) : Kˣ := if a = i then c else 1
  have hd (u : I → Kˣ) : LayerWord 1 (diagonal fun a => (u a : K)) :=
    layerWord_of_layer (LayerMatrix.monomial (Equiv.refl I) u)
  have h := layerWord_mul (layerWord_mul (hd d)
    (layerWord_of_layer (LayerMatrix.unitTransvection (K := K) hij))) (hd fun a => (d a)⁻¹)
  convert h using 1
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, transvection, Matrix.add_apply,
    Matrix.single_apply, Matrix.one_apply]
  by_cases he : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := he
    simp [hij, hij.symm, d]
  · by_cases hab : a = b
    · subst b
      simp [he]
    · simp [he, hab]

/-- A uniform word for each scalar shear in a coefficient ring with the two-unit property. -/
theorem layerWord_transvection_of_unit_split
    (hs : ∀ s : K, ∃ t : K, IsUnit t ∧ IsUnit (s-t)) {i j : I} (hij : i ≠ j) (s : K) :
    LayerWord 6 (transvection i j s) := by
  obtain ⟨t, ht, hr⟩ := hs s
  have h := layerWord_mul (layerWord_transvection_unit hij ht.unit)
    (layerWord_transvection_unit hij hr.unit)
  rwa [ht.unit_spec, hr.unit_spec, transvection_mul_transvection_same i j hij,
    show t + (s - t) = s by abel] at h

end Ring

/-- An arbitrary scalar transvection costs at most three monomial/shear pairs. -/
theorem layerWord_transvection [Field K] {i j : I} (hij : i ≠ j) (c : K) :
    LayerWord 3 (transvection i j c) := by
  by_cases hc : c = 0
  · simpa [hc] using (layerWord_one (K := K) (I := I) 3)
  let d (a : I) := if a = i then c else 1
  have hd (a : I) : d a ≠ 0 := by dsimp [d]; split <;> simp_all
  have hD := layerWord_of_layer (layerMatrix_diagonal hd)
  have hD' := layerWord_of_layer (layerMatrix_diagonal (fun a => inv_ne_zero (hd a)))
  have hu := layerWord_of_layer (LayerMatrix.unitTransvection (K := K) hij)
  convert layerWord_mul (layerWord_mul hD hu) hD' using 1
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [transvection, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases he : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := he
    simp [hij, hij.symm, d]
  · by_cases hab : a = b
    · subst b
      simp [he, hd]
    · simp [he, hab]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
