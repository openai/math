import OAI.LinearAlgebra.SpectralBooks.SpectralMetricLimit
import OAI.LinearAlgebra.SpectralBooks.SpectralDiagonal
import OAI.LinearAlgebra.SpectralBooks.GridPriceLimit

/-! # The spectral diagonal on the doubled-grid ultralimit

The joint ultralimit of all placed tensor prices and the finite-set
construction for the grids give the same diagonal price on every finite set.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SpectralPlacementPrices

open Filter Topology HyperbolicObstruction MetricLimit SiteTensor
open scoped Classical

variable {K : Type*} [Field K] {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {o : ∀ n, X n}

/-- The binary diagonal of the full spectral structure on the metric ultralimit
agrees with the representative-based finite-set price of the grids. -/
theorem metricLimit_diagonal (U : Ultrafilter ℕ) (P : ∀ n, SpectralPlacementPrices K (X n))
    (S : Finset (Space (U := U) (o := o))) :
    (metricLimit U P).diagonal S = metricLimitDiagonal (fun n ↦ (P n).diagonal) S := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [metricLimitDiagonal]
    exact tendsto_const_nhds.limUnder_eq.symm
  let z (i : Fin S.card) := (S.equivFin.symm i).val
  have : Nonempty (Fin S.card) := Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hS)
  let r (i : Fin S.card) := (SeparationQuotient.surjective_mk (z i)).choose
  have hr (i) : point (r i) = z i := (SeparationQuotient.surjective_mk (z i)).choose_spec
  have hset : Finset.univ.image (point ∘ r) = S := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, hr]
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).prop
    · intro hx
      exact ⟨S.equivFin ⟨x,hx⟩, by simp [z]⟩
  have hd := tendsto_metricLimitDiagonal (fun n ↦ (P n).diagonal)
    (fun n ↦ (P n).diagonal_singleton) (fun n _ p q ↦ (P n).diagonal_transport p q) r
  have hp := metricLimit_price_tendsto U P (Raw.diagonal (Fin S.card) K (Fin 2)) r
  simp only [price_binaryDiagonal_eq, hset] at hp hd
  exact tendsto_nhds_unique hp hd

end SpectralPlacementPrices

end SpectralBooks
end LinearAlgebra
end OAI
