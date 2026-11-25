import OAI.Computability.BorderVNP.CoverFrameBins
import OAI.Computability.BorderVNP.CoverFrameNormalizedHaar
import OAI.Computability.BorderVNP.CoverHeckeDensity
import OAI.Computability.BorderVNP.CoverMotionAddress

/-!
# Finite motions of the arithmetic frame host

The compact quaternion frame quotient carries full-support normalized Haar
probability. For any finite set of continuity bins, one finite rational
distribution of integral-denominator motions approximates all their masses,
uniformly in the input frame. Each sample sends a deeper cover to the stated
shallower cover. Projecting the determinant-one frames to projective frames
identifies the two central-sign representatives of a tangent frame.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open MeasureTheory Set Finset Filter BorderVNP.Hecke
open scoped Topology BoundedContinuousFunction

/-- A common, finite rational motion distribution on the actual quaternion frame host. -/
theorem exists_finite_frame_motions :
    ∃ (μ : Measure SL) (D : Set SL), μ.IsHaarMeasure ∧ MeasurableSet D ∧
      ExactTile (lattice 1) D ∧ μ D = 1 ∧
      ∀ {J : Type} [Finite J] (B : J → Set (Cosets (lattice 1))),
        (∀ j, MeasurableSet (B j)) → (∀ j, tileHaar (lattice 1) μ D (frontier (B j)) = 0) →
        ∀ ε > (0 : ℝ), ∃ (a m : ℕ) (w : Fin m → ℚ) (u : Fin m → SL),
          (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, Clears (u i) a) ∧
          ∀ j x, |(∑ i, (w i : ℝ) * (B j).indicator (fun _ => (1:ℝ)) (coset _ (u i*x))) -
            (tileHaar (lattice 1) μ D).real (B j)| < ε := by
  classical
  obtain ⟨μ,D,hm,hD,hd,h1,hprob,hpos⟩ := exists_normalized_frameHaar 1
  refine ⟨μ,D,hm,hD,hd,h1,?_⟩
  intro J _ B hmeas hnull ε hε
  let I := Cosets (intersection (lattice 1) elliptic)
  have : Nonempty I := ⟨coset _ 1⟩
  have : Finite I := finite_elliptic_indices.1
  have : Finite (Cosets (intersection (lattice 1) elliptic⁻¹)) := finite_elliptic_indices.2
  let : Fintype I := Fintype.ofFinite _
  let : Fintype (Cosets (intersection (lattice 1) elliptic⁻¹)) := Fintype.ofFinite _
  let ν := tileHaar (lattice 1) μ D
  have : IsProbabilityMeasure ν := hprob
  have : ν.IsOpenPosMeasure := hpos
  have hstat (f : Cosets (lattice 1) →ᵇ ℝ) : (∫ y, operator (lattice 1) elliptic f y ∂ν) = ∫ y, f y ∂ν :=
    integral_average (lattice 1) μ elliptic hD hd h1 _ f.continuous.measurable
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hden : Dense (Subgroup.closure ((lattice 1 : Set SL) ∪ {elliptic}) : Set SL) := by
    simpa only [Set.union_singleton] using dense_generated
  obtain ⟨n,hn⟩ := (finite_frame_bins (lattice 1) elliptic ν hstat hden B hmeas hnull hε).exists
  let e := Fintype.equivFin (Samples I n)
  let w (i : Fin (Fintype.card (Samples I n))) := weight I n (e.symm i)
  let u (i : Fin (Fintype.card (Samples I n))) := motion (step (lattice 1) elliptic)
    (e.symm i).1.val (e.symm i).2
  refine ⟨n,_,w,u,fun i => weight_pos n _,?_,fun i => (clears_motion _ _).mono
    (Nat.le_of_lt_succ (e.symm i).1.isLt),?_⟩
  · exact (e.symm.sum_comp (weight I n)).trans (sum_weight n)
  · intro j x
    have he := e.symm.sum_comp (fun s : Samples I n => (weight I n s : ℝ) *
      (B j).indicator (fun _ => (1:ℝ)) (coset _ (motion (step (lattice 1) elliptic) s.1 s.2 * x)))
    change |(∑ i, (weight I n (e.symm i) : ℝ) * _) - _| < ε
    rw [he]
    exact hn j x

end Cover.Frame

end BorderVNP
end Computability
end OAI
