import OAI.LinearAlgebra.FiniteFourier.OccupiedWord

/-! # Base change for synchronized transform words

A unital coefficient map sends permutations with unit scalings to permutations
with unit scalings. Tensor products, block sums, and the elementary shear are
preserved, including the identity on all occupied workspace registers.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped Kronecker

variable {R S : Type*} [CommSemiring R] [CommSemiring S]
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- Every synchronized layer remains a layer of the same kind after base change. -/
theorem LayerMatrix.mapCoefficients {kind : LayerKind} {A : Matrix I I R}
    (h : LayerMatrix kind A) (φ : R →+* S) : LayerMatrix kind (A.map φ) := by
  induction h with
  | id k => simpa using LayerMatrix.id (K := S) k
  | monomial e d =>
    have he : Matrix.map (fun i j => if e i = j then (d i : R) else 0) φ =
        (fun i j => if e i = j then (Units.map φ.toMonoidHom (d i) : S) else 0) := by
      ext i j
      change φ (if e i = j then (d i : R) else 0) = if e i = j then φ (d i : R) else 0
      split <;> simp_all
    rw [he]
    exact LayerMatrix.monomial e (fun i => Units.map φ.toMonoidHom (d i))
  | unitShear =>
    convert LayerMatrix.unitShear (K := S) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [FiniteFourier.unitShear]
  | relabel e _ ih => exact ih.relabel e
  | tensor _ _ ihA ihB =>
    convert LayerMatrix.tensor ihA ihB using 1
    ext i j
    simp
  | parallel _ _ ihA ihB =>
    simpa [fromBlocks_map] using LayerMatrix.parallel ihA ihB
  | grid _ ih =>
    convert LayerMatrix.grid ih using 1
    ext i j
    simp [gridTensor]
  | blocks _ ih =>
    rw [blockDiagonal'_map _ _ (map_zero φ)]
    exact LayerMatrix.blocks ih

/-- A word specializes entrywise with exactly its original number of layer pairs. -/
theorem LayerWord.mapCoefficients {d : ℕ} {A : Matrix I I R} (h : LayerWord d A)
    (φ : R →+* S) : LayerWord d (A.map φ) := by
  induction d generalizing A with
  | zero =>
    obtain rfl : A = 1 := h
    exact φ.mapMatrix.map_one
  | succ d ih =>
    obtain ⟨M, T, P, hM, hT, hP, rfl⟩ := h
    exact ⟨M.map φ, T.map φ, P.map φ, hM.mapCoefficients φ, hT.mapCoefficients φ, ih hP,
      by simp only [Matrix.map_mul]⟩

/-- Specializing a workspace word preserves its action on the data and restores
the original contents of every workspace register. -/
theorem OccupiedWord.mapCoefficients {d : ℕ} {A : Matrix I I R} (h : OccupiedWord W d A)
    (φ : R →+* S) : OccupiedWord W d (A.map φ) := by
  simpa [OccupiedWord, fromBlocks_map] using LayerWord.mapCoefficients h φ

end FiniteFourier
end LinearAlgebra
end OAI
