import OAI.LinearAlgebra.SpectralBooks.EveryField
import OAI.LinearAlgebra.SpectralBooks.BinaryJointConvexity
import OAI.LinearAlgebra.SpectralBooks.GridCubeExtension

/-! # A single complex spectral point for a finite planar placement -/

namespace OAI
namespace Combinatorics
namespace Sunflower

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

/-- All nonempty partial diagonals on the sites of a planar placement have their
normalized Euclidean mean widths as binary log-prices, in one spectral point. -/
theorem exists_planar_point {I : Type} [Fintype I] [Nontrivial I]
    (x : I ↪ EuclideanSpace ℝ (Fin 2)) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop),
      0 < meanWidth (Finset.univ.map x) Finset.univ_nonempty.map ∧
      ∀ (S : Finset I) (hS : S.Nonempty),
        Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal ℂ S (Fin 2))) : ℝ) =
          meanWidth (S.map x) hS.map /
            meanWidth (Finset.univ.map x) Finset.univ_nonempty.map := by
  classical
  let : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  obtain ⟨P, _⟩ := matrix_spectral_plane ℂ
  obtain ⟨φ, c, _, h⟩ := P.exists_point_diagonal_map x
  have geometry (S : Finset I) (hS : S.Nonempty) :
      P.diagonal (S.map x) = meanWidth (S.map x) hS.map := by
    let hE := innerProductSpace_catZero (EuclideanSpace ℝ (Fin 2))
    have hjoint : P.JointlyConvexDiagonal hE :=
      P.jointlyConvexDiagonal_of_raw hE (rawDiagonalJointConvexity ℂ)
    simpa using P.flatDiagonalLaw_isometry hE hjoint isometry_id (S.map x) hS.map
  have full := h Finset.univ Finset.univ_nonempty
  rw [ofRaw_maskDiagonal_univ, ofRaw_diagonal_fin_eq_natCast] at full
  have two := map_natCast (normalizedSpectrum.toRingHom φ) 2
  change φ.val (2 : TensorClass.{0} I ℂ) = 2 at two
  have hfull : P.diagonal (Finset.univ.map x) = c := by
    simpa [two, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using full
  have cpos : 0 < c := by
    rw [← hfull, Finset.map_eq_image]
    exact (P.diagonal_pos x).trans_le (P.price_binaryDiagonal_eq (x : I → _)).le
  have scale := (geometry Finset.univ Finset.univ_nonempty).symm.trans hfull
  refine ⟨φ, scale.symm ▸ cpos, fun S hS ↦ ?_⟩
  rw [scale, eq_div_iff cpos.ne', mul_comm, ← h S hS, geometry S hS]

end Sunflower
end Combinatorics
end OAI
