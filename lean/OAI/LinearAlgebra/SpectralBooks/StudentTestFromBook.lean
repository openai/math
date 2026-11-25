import OAI.LinearAlgebra.SpectralBooks.BinaryJointConvexity
import OAI.LinearAlgebra.SpectralBooks.CharacteristicAlternative
import OAI.LinearAlgebra.SpectralBooks.GridCubeExtension
import OAI.LinearAlgebra.SpectralBooks.PlacedSpectralWires
import OAI.LinearAlgebra.SpectralBooks.SpectralFlatLaw

/-! # The finite Student test from a spectral book -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open HyperbolicObstruction
open scoped Classical NNReal

/-- The three-page book over `ℝ^q` gives the Student test in dimension
`q + 1`. Pulling prices back to each isometric Euclidean chart allows the
flat diagonal law to be applied inside that chart. -/
theorem studentMatrixTest_of_spectral_book (K : Type) [Field K] {q : ℕ} (hq : 0 < q)
    (P : SpectralPlacementPrices K (Book (EuclideanSpace ℝ (Fin q)))) : StudentMatrixTest K (q+1) := by
  let E := EuclideanSpace ℝ (Fin q)
  have hflat (e : Book.Lift E → Book E) (he : Isometry e) (S : Finset (Book.Lift E))
      (hS : S.Nonempty) : P.diagonal (S.image e) = meanWidth S hS := by
    let Q := P.pullback e he
    let hY := innerProductSpace_catZero (Book.Lift E)
    rw [← P.diagonal_pullback e he]
    have hjoint : Q.JointlyConvexDiagonal hY := Q.jointlyConvexDiagonal_of_raw hY (SiteTensor.rawDiagonalJointConvexity K)
    simpa using Q.flatDiagonalLaw_isometry hY hjoint isometry_id S hS
  have hwires (a : Fin 3 → ℝ≥0) (ha : ∀ i, 0 < a i) :
      let p := fun i => bookPoint i (a i) (0 : E)
      PlacedWires K p (P.diagonal (Finset.univ.image p)) := by
    let e : Fin 3 ↪ Book E := ⟨fun i => bookPoint i (a i) 0, by
      intro i j h
      by_contra hij
      have hd := book_dist_distinct_tips hij (a i) (a j) (0 : E)
      change bookPoint i (a i) (0 : E) = bookPoint j (a j) 0 at h
      rw [h, dist_self] at hd
      have hi : 0 < (a i : ℝ) := ha i
      have hj : 0 < (a j : ℝ) := ha j
      linarith⟩
    exact P.placedWires e
  intro x y z hx hy hz
  refine (matrix_student_bound_of_book K (E := E) (by simp [E]) hq P.diagonal P.diagonal_mono
    ?_ ?_ ?_ hx hy hz).2
  · convert P.intersectingSubmodular using 1
  · intro e he S hS
    convert hflat e he S hS using 2
    congr!
  · intro a ha
    convert hwires a ha using 1
    dsimp only
    congr!

end

end

end SpectralBooks
end LinearAlgebra
end OAI
