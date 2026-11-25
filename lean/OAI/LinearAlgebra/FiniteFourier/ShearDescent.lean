import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization
import OAI.LinearAlgebra.FiniteFourier.ScalarDescent
import OAI.LinearAlgebra.FiniteFourier.CircuitParallel

/-! # Base change for the shear layers of a grid word -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped Kronecker

variable {K E : Type*} [CommRing K] [CommRing E]

private lemma shearLayer_baseChange_aux (f : K →+* E)
    {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I E} {k : LayerKind}
    (h : LayerMatrix k A) (hk : k = .shear) :
    ∃ B : Matrix I I K, LayerMatrix .shear B ∧ B.map f = A := by
  classical
  induction h with
  | id =>
    refine ⟨1, .id _, ?_⟩
    ext i j
    simp [one_apply]
  | monomial => contradiction
  | unitShear =>
    refine ⟨unitShear K, .unitShear, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unitShear]
  | relabel e _ ih =>
    obtain ⟨B, hB, rfl⟩ := ih hk
    exact ⟨_, .relabel e hB, rfl⟩
  | tensor _ _ ih₁ ih₂ =>
    obtain ⟨B₁, h₁, rfl⟩ := ih₁ hk
    obtain ⟨B₂, h₂, rfl⟩ := ih₂ hk
    refine ⟨B₁ ⊗ₖ B₂, .tensor h₁ h₂, ?_⟩
    ext x y
    exact map_mul f _ _
  | parallel _ _ ih₁ ih₂ =>
    obtain ⟨B₁, h₁, rfl⟩ := ih₁ hk
    obtain ⟨B₂, h₂, rfl⟩ := ih₂ hk
    refine ⟨_, .parallel h₁ h₂, ?_⟩
    simp [Matrix.fromBlocks_map]
  | grid _ ih =>
    choose B hB hM using fun i => ih i hk
    refine ⟨_, .grid hB, ?_⟩
    ext x y
    simp [gridTensor, ← hM]
  | blocks _ ih =>
    choose B hB hM using fun i => ih i hk
    refine ⟨_, .blocks hB, ?_⟩
    rw [Matrix.blockDiagonal'_map B f (map_zero f)]
    exact congrArg Matrix.blockDiagonal' (funext hM)

/-- The same shear layer acts on every base coordinate. This applies to all
tensor products and disjoint blocks represented by a shear layer. -/
theorem shearLayer_baseChange (f : K →+* E)
    {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I E}
    (hA : LayerMatrix .shear A) :
    ∃ B : Matrix I I K, LayerMatrix .shear B ∧ B.map f = A :=
  shearLayer_baseChange_aux f hA rfl

/-- Restriction of scalars charges at most one base-layer circuit per basis
coordinate in each shear slot. -/
theorem realizable_restrict_shear [Algebra K E] {D : Type*} [Fintype D] [DecidableEq D]
    {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I E} (b : Module.Basis D K E)
    (hA : LayerMatrix .shear A) {s : ℕ}
    (hcost : ∀ B : Matrix I I K, LayerMatrix .shear B → RealizableAtMost B s) :
    RealizableAtMost (restrictMatrix b A) (Fintype.card D * s) := by
  obtain ⟨B, hB, rfl⟩ := shearLayer_baseChange (algebraMap K E) hA
  rw [restrictMatrix_algebraMap]
  exact (hcost B hB).blockDiagonal D

end FiniteFourier
end LinearAlgebra
end OAI
