import OAI.LinearAlgebra.SpectralBooks.TriangleAPComparison
import OAI.LinearAlgebra.SpectralBooks.TriangleWirePrice

/-! # The triangle diagonal is bounded above by its semiperimeter

A common-label diagonal of dimension `r²` is geometrically extractable
from the three wires of dimension `2r`. Evaluating at the point of a
placement and letting the label dimension grow gives the inequality for
every field and all three points, including repeated points.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped Classical NNReal

section

open SiteTensor

/-- The three wire prices in a normalized point sum to at least two. -/
theorem two_le_sum_wire_logs (K : Type*) [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop)) :
    let D (i j : Fin 3) := Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K {i,j} (Fin 2))) : ℝ)
    2 ≤ D 0 1 + D 1 2 + D 2 0 := by
  apply two_le_sum_binary_wire_logs φ
  intro r
  have h := triangleDiagonal_value_le K r φ
  change φ.val (ofRaw (Raw.diagonal (Fin 3) K (Fin r × Fin r))) ≤ _ at h
  rw [ofRaw_diagonal_eq_natCast] at h
  change normalizedSpectrum.toRingHom φ _ ≤ _ at h
  simpa [map_natCast, pow_two] using h

/-- The price of a triangle diagonal in any spectral space is at most half
the sum of its three wire distances. -/
theorem SpectralPlacementPrices.diagonal_triangle_le_half_perimeter {K X : Type*}
    [Field K] [PseudoMetricSpace X] (P : SpectralPlacementPrices K X) (a b c : X) :
    P.diagonal {a, b, c} ≤ (dist a b + dist b c + dist c a) / 2 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [P.diagonal_pair, dist_comm c a]
  by_cases hbc : b = c
  · subst c
    simp [P.diagonal_pair, dist_comm b a]
  by_cases hca : c = a
  · subst c
    rw [show ({a, b, a} : Finset X) = {a,b} by ext; simp; tauto, P.diagonal_pair]
    rw [dist_self, dist_comm b a]
    linarith
  let p : Fin 3 → X := ![a,b,c]
  have hp : Function.Injective p := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (simp [p] at h; grind)
  let e : Fin 3 ↪ X := ⟨p,hp⟩
  obtain ⟨φ,d,hd,h⟩ := P.exists_point_diagonal_map e
  have hfull : P.diagonal {a,b,c} = d := by
    have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
    have he := h Finset.univ Finset.univ_nonempty
    rw [ofRaw_maskDiagonal_univ, ofRaw_diagonal_fin_eq_natCast] at he
    have hv := map_natCast (normalizedSpectrum.toRingHom φ) 2
    change φ.val (2 : TensorClass.{0} (Fin 3) K) = 2 at hv
    simpa [hu, Finset.map_insert, e, p, hv] using he
  have hedge (i j : Fin 3) :
      d * Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K {i,j} (Fin 2))) : ℝ) =
        dist (p i) (p j) := by
    rw [← h {i,j} (by simp), Finset.map_insert, Finset.map_singleton, P.diagonal_pair]
    rfl
  have hm := mul_le_mul_of_nonneg_left (two_le_sum_wire_logs K φ) hd
  dsimp only at hm
  rw [mul_add, mul_add, hedge, hedge, hedge] at hm
  rw [hfull]
  change d * 2 ≤ dist a b + dist b c + dist c a at hm
  linarith

end

end SpectralBooks
end LinearAlgebra
end OAI
