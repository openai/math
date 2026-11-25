import OAI.LinearAlgebra.SpectralBooks.PlacedSpectralWires
import OAI.LinearAlgebra.SpectralBooks.TriangleSemiperimeter
import OAI.LinearAlgebra.SpectralBooks.IntersectingSubmodularity
import OAI.LinearAlgebra.SpectralBooks.DiagonalMonotonicity
import OAI.LinearAlgebra.SpectralBooks.DivisionExponent
import OAI.LinearAlgebra.SpectralBooks.AbsoluteTensorRank

/-! # From a spectral book to the rank and arithmetic inequalities -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
section

open scoped Classical NNReal

/-- The rank test requires only the distances of the three pages. The universal
triangle upper bound controls each tip together with the endpoints of the spine. -/
def SpectralPlacementPrices.toPlanarBookPrices {F : Type} [Field F]
    (P : SpectralPlacementPrices F (Book ℝ)) :
    PlanarBookPrices F where
  diagonal := P.diagonal
  monotone := P.diagonal_mono
  submodular := P.intersectingSubmodular
  base := by
    have h := (P.diagonal_pair (bookSpine (-1)) (bookSpine 1)).trans bookSpine_dist
    convert h using 1
    apply congrArg P.diagonal
    ext x
    simp [bookBase]
  triangle r i := by
    have h := P.diagonal_triangle_le_half_perimeter (bookSpine (-1)) (bookSpine 1) (bookTip r i)
    convert h using 1
    apply congrArg P.diagonal
    ext x
    simp [bookBase, or_comm, or_left_comm]
  wires r hr := by
    let e : Fin 3 ↪ Book ℝ := ⟨bookTip r, by
      intro i j h
      by_contra hij
      have hd := bookTip_dist r hij
      rw [h, dist_self] at hd
      have hi : 0 < (r i : ℝ) := hr i
      have hj : 0 < (r j : ℝ) := hr j
      linarith⟩
    convert P.placedWires e using 1
    congr 2
    exact Subsingleton.elim _ _

/-- A proof of the asymptotic inequality in one field gives all three rank
bounds in *every* field of its characteristic. Only the asymptotic rank needs
to be transported between the fields. -/
theorem rectangularRankBound_of_same_characteristic {E F : Type*} [Field E] [Field F]
    (hchar : ringChar E = ringChar F)
    (h : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z →
      RadicalTest (loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z))
        (Real.logb 2 (asymptoticRank (matrixTensor E x y z)))) :
    RectangularRankBound F := by
  intro x y z hx hy hz
  dsimp only
  have ha := h x y z hx hy hz
  rw [asymptoticRank_matrixTensor_eq_of_ringChar_eq E F hchar] at ha
  have hn : 0 < max (z * x) (max (x * y) (y * z)) :=
    lt_of_lt_of_le (Nat.mul_pos hz hx) (le_max_left _ _)
  have hp := (Nat.cast_pos.mpr hn).trans_le (matrix_flattening_le_asymptoticRank F hx hy hz)
  have hlog (q : ℕ) (hq : 0 < q) := Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    (Nat.one_le_cast.mpr hq)
  have hm := loads_nonneg (hlog x hx) (hlog y hy) (hlog z hz)
  have hcomp := asymptoticRank_le_geometricBorderRank (matrixTensor F x y z)
  have hb := (ha.heightTest hm).mono (Real.logb_le_logb_of_le (by norm_num) hp hcomp)
  exact ⟨ha, hb.radicalTest hm, (hb.mono (Real.logb_le_logb_of_le (by norm_num)
    (hp.trans_le hcomp) (Nat.cast_le.mpr (geometricBorderRank_le_tensorRank _)))).radicalTest hm⟩

theorem RectangularRankBound.of_ringChar_eq {E F : Type*} [Field E] [Field F]
    (h : RectangularRankBound E) (hchar : ringChar E = ringChar F) : RectangularRankBound F :=
  rectangularRankBound_of_same_characteristic hchar (fun x y z hx hy hz => (h x y z hx hy hz).1)

/-- Both arithmetic models satisfy the same square lower bound once the finite
rectangular theorem is known over the field. -/
theorem RectangularRankBound.square_exponents {F : Type*} [Field F] (h : RectangularRankBound F) :
    3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 ∧ 3 / Real.sqrt 2 ≤ divisionOmega F 1 1 1 := by
  have hω := formalOmega_square_lower_bound_of_rank_bound
    (fun x y z hx hy hz => (h x y z hx hy hz).2.2)
  exact ⟨hω, (divisionOmega_square_eq_formalOmega F).symm ▸ hω⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
