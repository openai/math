import OAI.LinearAlgebra.SpectralBooks.PlacementPullback
import Mathlib.Tactic

namespace OAI
/-! # The price of a tensor of bounded rank at an arbitrary placement -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks SiteTensor

/-- A rank-`R` decomposition gives the diagonal bound at any assignment of its legs,
including repeated sites. -/
theorem price_le_diagonal_mul_log_rank {J : Type} [Fintype J] [Nonempty J]
    {X F : Type*} [MetricSpace X] [Field F] (P : SpectralPlacementPrices F X)
    (T : Raw.{0} J F) (y : J → X) (R : ℕ)
    (hr : T.Restricts (Raw.diagonal J F (Fin R))) :
    P.price T y ≤ P.price (Raw.diagonal J F (Fin 2)) y * Real.logb 2 R := by
  obtain ⟨p, h, hp⟩ := P.exists_spectralPrice_of_placement y
  rw [hp, hp]
  rcases h with rfl | ⟨φ,c,hc,rfl⟩
  · simp
  have natValue (n : ℕ) : φ.val (ofRaw (Raw.diagonal J F (Fin n))) = n := by
    rw [ofRaw_diagonal_fin_eq_natCast]
    exact map_natCast (normalizedSpectrum.toRingHom φ) n
  have binary : (φ.val (ofRaw (Raw.diagonal J F (Fin 2))) : ℝ) = 2 := by
    rw [natValue]
    norm_num
  rw [classPrice_scaled_log, classPrice_scaled_log, binary, Real.logb_self_eq_one (by norm_num), mul_one]
  simpa only [rawLogPrice, natValue, NNReal.coe_natCast] using rawLogPrice_mono φ hc.le hr

end Hierarchy

end OAI
