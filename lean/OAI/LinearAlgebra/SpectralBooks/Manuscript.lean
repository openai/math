import OAI.LinearAlgebra.SpectralBooks.RankFromBook
import OAI.LinearAlgebra.SpectralBooks.FinitePlaneCriterion
import OAI.LinearAlgebra.SpectralBooks.Theorem
import OAI.LinearAlgebra.SpectralBooks.SpectralBookTheorem
import OAI.LinearAlgebra.SpectralBooks.StudentTestFromFlat
import OAI.LinearAlgebra.SpectralBooks.VNPCharacteristicAlternative

/-! # The rectangular theorem from the spectral geometry input

A spectral plane over a field implies the finite rank theorem in every positive format.
The inequalities subsequently hold over any field of the same characteristic.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open HyperbolicObstruction

/-- A spectral plane over the field gives the manuscript’s full
finite rectangular rank inequality, including border and ordinary rank. -/
theorem rectangularRankBound_of_spectral_plane {K : Type} [Field K]
    (plane : SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 2))) :
    RectangularRankBound K := by
  let e : Option Unit ≃ Fin 2 := Fintype.equivOfCardEq (by simp)
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  obtain ⟨book⟩ := exists_planarBook_prices_of_plane (plane.pullback E E.isometry)
    (fun _ _ _ Q hg => Q.catZero hg)
  exact book.toPlanarBookPrices.rectangularRankBound

/-- A four-point defect in any spectral space over the field suffices. The
complete CAT(0) extension preserves the four distances. -/
theorem rectangularRankBound_of_four_point {K : Type} [Field K]
    {X : Type} [MetricSpace X] (P : SpectralPlacementPrices K X) (a b z w : X)
    (hbad : max (dist a z + dist b w) (dist a w + dist b z) < dist a b + dist z w) :
    RectangularRankBound K := by
  obtain ⟨Y, _, Q, ⟨e⟩, _, hY⟩ := P.exists_complete_catZero_extension
  have he := e.isometry
  obtain ⟨plane⟩ := spectralPlane_of_fourPointDefect Q hY (e.map a) (e.map b)
    (e.map z) (e.map w) (by simpa only [he.dist_eq] using hbad)
  exact rectangularRankBound_of_spectral_plane plane

/-- The rectangular rank theorem and the square exponent bound, for every
field of the characteristic, with formal arithmetic over finite fields. -/
theorem rank_and_exponent_of_spectral_plane {K : Type} [Field K]
    (plane : SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 2)))
    (F : Type*) [Field F] (hchar : ringChar K = ringChar F) :
    RectangularRankBound F ∧ 3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 ∧
      3 / Real.sqrt 2 ≤ divisionOmega F 1 1 1 := by
  have hr := (rectangularRankBound_of_spectral_plane plane).of_ringChar_eq hchar
  exact ⟨hr, hr.square_exponents⟩

/-- Sharp's non-tree alternative in one field of the characteristic gives
the rectangular inequalities and both square arithmetic exponent bounds. -/
theorem rank_and_exponent_of_nonTreeWireMetric {K : Type} [Field K]
    (hw : HasNonTreeWireMetric K) (F : Type*) [Field F] (hchar : ringChar K = ringChar F) :
    RectangularRankBound F ∧ 3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 ∧
      3 / Real.sqrt 2 ≤ divisionOmega F 1 1 1 := by
  obtain ⟨P, _⟩ := exists_jointly_convex_spectral_plane hw
  exact rank_and_exponent_of_spectral_plane P F hchar

end SpectralBooks
end LinearAlgebra
end OAI
