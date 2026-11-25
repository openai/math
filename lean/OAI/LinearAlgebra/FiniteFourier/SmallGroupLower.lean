import OAI.LinearAlgebra.FiniteFourier.Bounds
import OAI.LinearAlgebra.FiniteFourier.GroupReindex
import OAI.LinearAlgebra.FiniteFourier.PlaneLower
import OAI.LinearAlgebra.FiniteFourier.RadialPlaneLaws
import OAI.LinearAlgebra.SpectralBooks.ConvexOnPrice

/-! # Uniform Fourier lower bounds for finite groups in any universe

The spectral placement has small coordinate types. An arbitrary finite group
has a small isomorphic copy, with the same admissibility conditions and a
character table obtained by permuting rows and columns.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

universe u v

/-- The explicit large-order lower bound in both Fourier directions, without a universe
restriction on the finite group. -/
theorem fourier_border_lower_of_plane_any_universe {G : Type u} {K : Type v}
    [AddCommGroup G] [Fintype G] [Field K]
    (P : SpectralPlacementPrices (AlgebraicClosure K) Plane) (hP : FourierPlaneLaws P)
    (had : Admissible G K) {S : ℕ} (hm : 144 ≤ Real.logb 2 (Fintype.card G))
    (hb : GeometricBorderAtMost (fourierMatrix G K) S ∨
      GeometricBorderAtMost (inverseFourierMatrix G K) S) :
    (2 : ℝ) ^ (-(28 : ℝ)) * Fintype.card G * ⌊Real.sqrt (Real.logb 2 (Fintype.card G)) / 6⌋₊ < S := by
  let e : G ≃+ Shrink.{0} G := Shrink.addEquiv.symm
  have he := Fintype.card_congr e.toEquiv
  have hf := hb.elim id (geometricBorderAtMost_inverseFourierMatrix_iff G K had S).mp
  have hb' := border_fourierMatrix_of_groupEquiv e hf
  exact he ▸ fourier_border_lower_of_plane P hP (had.of_groupEquiv e) (he ▸ hm) (Or.inl hb')

/-- A jointly convex spectral plane over each algebraic closure supplies a single absolute
constant in the border lower bound for every admissible finite abelian group of order at
least two, in arbitrary group and coefficient-field universes. -/
theorem uniformFourierBorderLower_of_jointly_convex_planes
    (plane : ∀ (K : Type v) [Field K], ∃ P : SpectralPlacementPrices (AlgebraicClosure K) Plane,
      ∀ {I : Type} [Fintype I] (T : Raw.{0} I (AlgebraicClosure K)), ConvexOn ℝ Set.univ (P.price T)) :
    UniformFourierBorderLower.{u,v} := by
  apply uniformFourierBorderLower_of_large_orders
  intro G K _ _ _ had _ hm S hb
  obtain ⟨P, hP⟩ := plane K
  exact fourier_border_lower_of_plane_any_universe (tangentPlane P)
    (tangentPlane_fourierPlaneLaws P hP) had hm (Or.inl hb)

/-- A spectral plane over each algebraic closure suffices for the uniform feedback
lower bound. Joint convexity follows from synchronized tensor relocation. -/
theorem uniformFourierBorderLower_of_spectral_planes
    (plane : ∀ (K : Type v) [Field K], Nonempty (SpectralPlacementPrices (AlgebraicClosure K) Plane)) :
    UniformFourierBorderLower.{u,v} := by
  apply uniformFourierBorderLower_of_jointly_convex_planes
  intro K _
  obtain ⟨P⟩ := plane K
  exact ⟨P, fun T => P.convexOn_price T⟩

end FiniteFourier
end LinearAlgebra
end OAI
