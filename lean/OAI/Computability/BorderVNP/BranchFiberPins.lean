import OAI.Computability.BorderVNP.BranchGridExtension
import OAI.Computability.VPVNP.SliceGeometry
import OAI.Computability.VPVNP.EffectiveNullstellensatz

/-! # Small-field hyperplanes cutting a fiber over its algebraic closure

The equations of a fiber chart may have arbitrary geometric coefficients. Only the
additional hyperplane constants have to be in the small field of advice. A one-parameter
Macaulay pencil over the geometric field controls each partially pinned projection,
uniformly in the number of equations. We apply the effective weak Nullstellensatz in
that field before restricting the available constants.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate VPVNP.SliceGeometry

/-- Number of exceptional constants to avoid when pinning a single coordinate in dimension
`t`. The degree cutoff `d ≥ 3` can be a singly exponential bound. -/
def fiberPinBound (t d : ℕ) : ℕ :=
  projectionBound t ((2 * d) ^ (4 * (t + 2))) d

/-- Geometric equations of bounded degree can be cut to a nonempty finite set using
coordinate hyperplanes with constants in any sufficiently large subfield. -/
theorem finite_fiber_by_subfield_pins {K E I : Type*} [Field K] [Fintype K] [Field E]
    [IsAlgClosed E] [Algebra K E] [Fintype I] {t d : ℕ} (hd : 3 ≤ d)
    (F : I → MvPolynomial (Fin t) E) (hF : ∀ j, (F j).totalDegree ≤ d)
    (hsol : ∃ x : Fin t → E, ∀ j, eval x (F j) = 0) (hK : fiberPinBound t d < Fintype.card K) :
    ∃ (s : Finset (Fin t)) (a : Fin t → K),
      let V := pinnedPoints {y : Fin t → E | ∀ j, eval y (F j) = 0} s a
      V.Nonempty ∧ V.Finite ∧ V.ncard ≤ fiberPinBound t d ^ t := by
  let W := {y : Fin t → E | ∀ j, eval y (F j) = 0}
  let H := (2 * d) ^ (4 * (t + 2))
  have hbound : 2 * Fintype.card (BoundedMonomial t (H + d)) ≤ fiberPinBound t d :=
    Nat.mul_le_mul_left _ (card_boundedMonomial_le t (H + d))
  apply exists_finite_pinned_slice W hsol _ (by unfold fiberPinBound projectionBound; positivity) hK
  intro s a i
  let A : Fin t → E := fun j ↦ algebraMap K E (a j)
  have hpin : pinnedPoints W s a =
      pinnedPoints {y : Fin t → E | ∀ j, aeval y (F j) = 0} s A := by
    ext x
    simp only [pinnedPoints, W, A, aeval_eq_eval, Algebra.algebraMap_self, RingHom.id_apply]
  let G := geometricPinnedEquations (E := E) F s A
  let M := coordinatePencil G i H (H + d)
  let N := augmentedCoordinatePencil G i H (H + d)
  have he : coordinateImage (pinnedPoints W s a) i =
      {c | (M.map (Polynomial.eval c)).rank < (N.map (Polynomial.eval c)).rank} := by
    rw [hpin]
    exact Set.ext fun c ↦ mem_pinnedCoordinateImage_iff_rank_lt F s A i c hF (by omega)
      (effective_weakCertificateBound E _ hd)
  rw [he]
  exact (boundedOrCobounded_rank_lt M N (coordinatePencil_degree_le G i H (H + d))
    (augmentedCoordinatePencil_degree_le G i H (H + d))).imp
    (fun ⟨hf, hc⟩ ↦ ⟨hf, hc.trans hbound⟩) (fun ⟨hf, hc⟩ ↦ ⟨hf, hc.trans hbound⟩)

/-- Both the grid-side requirement and the finite-slice point count have polynomially
many bits when `d` has polynomially many bits. This bound does not involve the number
of coordinates of the original coefficient vector. -/
theorem fiberPinBound_pow_le {t d L : ℕ} (hd : d ≤ 2 ^ L) :
    fiberPinBound t d ^ t ≤ 2 ^ ((((L + 1) * (4 * (t + 2)) + 2) * t + 1) * t) := by
  apply projectionBound_pow_le
  let m := 4 * (t + 2)
  have hm : 1 ≤ m := by dsimp [m]; omega
  have h₂ : 2 * d ≤ 2 ^ (L + 1) := by simpa [pow_succ', Nat.mul_comm] using Nat.mul_le_mul_left 2 hd
  have hpow : (2 * d) ^ m ≤ 2 ^ ((L + 1) * m) := by
    rw [pow_mul 2 (L + 1) m]
    exact Nat.pow_le_pow_left h₂ _
  have hbase : d ≤ 2 ^ ((L + 1) * m) := hd.trans (Nat.pow_le_pow_right (by decide)
    (by nlinarith only [hm]))
  change (2 * d) ^ m + d + 1 ≤ 2 ^ ((L + 1) * m + 2)
  rw [pow_add]
  have hp := Nat.two_pow_pos ((L + 1) * m)
  omega

/-- Choose the subfield for all coordinate cuts inside the prescribed algebraic closure. -/
theorem exists_small_fiber_pins (E₀ E : Type*) [Field E₀] [Fintype E₀] [Field E]
    [IsAlgClosed E] [Algebra E₀ E] {I : Type*} [Fintype I] {t d : ℕ} (hd : 3 ≤ d)
    (F : I → MvPolynomial (Fin t) E) (hF : ∀ j, (F j).totalDegree ≤ d)
    (hsol : ∃ x : Fin t → E, ∀ j, eval x (F j) = 0) :
    ∃ K : IntermediateField E₀ E, Finite K ∧
      Nat.card K ≤ Fintype.card E₀ * max (fiberPinBound t d) 1 ∧
      ∃ (s : Finset (Fin t)) (a : Fin t → K),
        let V := pinnedPoints {y : Fin t → E | ∀ j, eval y (F j) = 0} s a
        V.Nonempty ∧ V.Finite ∧ V.ncard ≤ fiberPinBound t d ^ t := by
  obtain ⟨K, hfin, hcard, hupper⟩ := exists_gridExtension E₀ E (fiberPinBound t d)
  let := Fintype.ofFinite K
  exact ⟨K, hfin, hupper, finite_fiber_by_subfield_pins hd F hF hsol
    (by simpa only [Nat.card_eq_fintype_card] using hcard)⟩

end Branch

end BorderVNP
end Computability
end OAI
