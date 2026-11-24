import OAI.Computability.VPVNP.SliceGeometryPencil
import OAI.Computability.VPVNP.SliceGeometryProjection
import Mathlib.RingTheory.Nullstellensatz

/-!
# A nonempty finite geometric slice with short affine cuts

Section 8.2 needs a finite geometric slice whose cardinality and base-field
cardinality have polynomial bit length. The construction here uses the same
effective weak Nullstellensatz bound `H` needed for characteristic descent.
A one-parameter Macaulay matrix detects each coordinate image. Outside the
exceptional roots of two minors its rank comparison is constant. Coordinate
pins consequently suffice to produce a finite slice.

The resulting point bound is `(2 * (H + d + 1)^t)^t`. Section 8.2's
projective Bézout argument gives the sharper bound `d^(t+1)`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceGeometry

open MvPolynomial RadicalCertificate

variable {K E : Type*} [Field K] [Fintype K] [Field E] [Algebra K E]
variable {ι : Type*} [Fintype ι] {t : ℕ}

/-- A monotone upper bound on the exceptional scalar count, independent of
the pins already chosen. -/
def projectionBound (t H d : ℕ) := 2 * (H + d + 1) ^ t

/-- The resulting point-count bound has at most `(tL+1)t+1` binary digits if
`H+d+1 ≤ 2^L`. -/
theorem projectionBound_pow_le {H d L : ℕ} (hL : H + d + 1 ≤ 2 ^ L) :
    projectionBound t H d ^ t ≤ 2 ^ ((L * t + 1) * t) := by
  rw [pow_mul]
  apply Nat.pow_le_pow_left
  dsimp [projectionBound]
  rw [pow_succ, pow_mul, Nat.mul_comm _ 2]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL t)

/-- The ideal of the original system and the selected affine coordinate equations. -/
noncomputable def pinnedIdeal (F : ι → MvPolynomial (Fin t) K) (s : Finset (Fin t))
    (a : Fin t → K) : Ideal (MvPolynomial (Fin t) K) :=
  Ideal.span (Set.range (pinnedEquations F s a))

omit [Fintype K] [Fintype ι] in
theorem zeroLocus_pinnedIdeal (F : ι → MvPolynomial (Fin t) K) (s : Finset (Fin t))
    (a : Fin t → K) : zeroLocus E (pinnedIdeal F s a) =
      pinnedPoints {y : Fin t → E | ∀ j, aeval y (F j) = 0} s a := by
  ext x
  rw [pinnedIdeal, zeroLocus_span, mem_pinnedPoints_iff]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, geometricPinnedEquations, eval_map, aeval_def]

/-- A coordinate pinning with at most `t` base-field coefficients gives a
nonempty finite geometric zero set of explicitly bounded cardinality. -/
theorem exists_finite_coordinate_slice (F : ι → MvPolynomial (Fin t) K) {H d : ℕ}
    (hF : ∀ i, (F i).totalDegree ≤ d) (hd : 1 ≤ d)
    (hK : projectionBound t H d < Fintype.card K)
    (hsol : ∃ x : Fin t → E, ∀ i, aeval x (F i) = 0)
    (bound : WeakCertificateBound E (Option (ι ⊕ Fin t)) t d H) :
    ∃ (s : Finset (Fin t)) (a : Fin t → K),
      let V := zeroLocus E (pinnedIdeal F s a)
      V.Nonempty ∧ V.Finite ∧ V.ncard ≤ projectionBound t H d ^ t := by
  let B := projectionBound t H d
  let W := {y : Fin t → E | ∀ j, aeval y (F j) = 0}
  have hbound : 2 * Fintype.card (BoundedMonomial t (H + d)) ≤ B :=
    Nat.mul_le_mul_left _ (card_boundedMonomial_le t (H + d))
  have hproj (s : Finset (Fin t)) (a : Fin t → K) (i : Fin t) :
      boundedOrCobounded (coordinateImage (pinnedPoints W s a) i) B := by
    let G := geometricPinnedEquations (E := E) F s a
    let M := coordinatePencil G i H (H + d)
    let N := augmentedCoordinatePencil G i H (H + d)
    have he : coordinateImage (pinnedPoints W s a) i =
        {c | (M.map (Polynomial.eval c)).rank < (N.map (Polynomial.eval c)).rank} :=
      Set.ext (fun c => mem_pinnedCoordinateImage_iff_rank_lt F s a i c hF hd bound)
    rw [he]
    have h := boundedOrCobounded_rank_lt M N (coordinatePencil_degree_le G i H (H + d))
      (augmentedCoordinatePencil_degree_le G i H (H + d))
    exact h.imp (fun ⟨hf, hc⟩ => ⟨hf, hc.trans hbound⟩) (fun ⟨hf, hc⟩ => ⟨hf, hc.trans hbound⟩)
  obtain ⟨s, a, hn, hf, hc⟩ := exists_finite_pinned_slice W hsol B
    (by dsimp [B, projectionBound]; positivity) hK hproj
  exact ⟨s, a, by simpa only [zeroLocus_pinnedIdeal] using And.intro hn (And.intro hf hc)⟩

end SliceGeometry

end VPVNP
end Computability
end OAI
