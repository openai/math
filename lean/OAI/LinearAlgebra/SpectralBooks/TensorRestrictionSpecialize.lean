import OAI.LinearAlgebra.SpectralBooks.AbsoluteTensorRank
import OAI.LinearAlgebra.SpectralBooks.ScalarExtensionSpectrum

/-! # Finite fields of definition of tensor restrictions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped BigOperators

namespace SiteTensor.Raw

universe v
variable {I F L : Type*} [Fintype I] [Field F] [Field L] [Algebra F L]

/-- The matrices witnessing a tensor restriction over a field extension can be
chosen over a finite extension inside the algebraic closure of the ground field. -/
theorem exists_finite_restriction_of_mapScalars {X Y : Raw.{v} I F}
    (h : (X.mapScalars (algebraMap F L)).Restricts (Y.mapScalars (algebraMap F L))) :
    ∃ S : IntermediateField F (AlgebraicClosure F), FiniteDimensional F S ∧
      (X.mapScalars (algebraMap F S)).Restricts (Y.mapScalars (algebraMap F S)) := by
  classical
  obtain ⟨M, hM⟩ := h
  let V := Σ i, X.Leg i × Y.Leg i
  let a : V → L := fun ⟨i, x, y⟩ => M i x y
  obtain ⟨b, hb⟩ := exists_specialization (F := F) (AlgebraicClosure F) a
  let S := IntermediateField.adjoin F (Set.range b)
  refine ⟨S, IntermediateField.finiteDimensional_adjoin
    (fun z _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) z).isIntegral), ?_⟩
  let B (v : V) : S := ⟨b v, IntermediateField.subset_adjoin F _ ⟨v, rfl⟩⟩
  refine ⟨fun i x y => B ⟨i, x, y⟩, fun x => ?_⟩
  let p : MvPolynomial V F := MvPolynomial.C (X.coeff x) -
    ∑ y, MvPolynomial.C (Y.coeff y) * ∏ i, MvPolynomial.X ⟨i, x i, y i⟩
  have hp : MvPolynomial.aeval a p = 0 := by
    simp [p, a, sub_eq_zero]
    exact hM x
  apply Subtype.ext
  have hx := hb p hp
  simp [p, sub_eq_zero] at hx
  simp [B, Raw.mapScalars]
  exact hx

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
