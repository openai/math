import OAI.Computability.BorderVNP.ShortenPackMotionMean
import Mathlib.MeasureTheory.Measure.Real

/-!
# Deck-uniform ideal bin probabilities in the moved pack

The ideal single-wire law samples a configuration from its continuous
position/direction law and a destination tile uniformly. Its normalization
uses the measurable partition into the actual relative configuration bins.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PackMotions

open Crossing Epoch Packing MeasureTheory Set
open scoped BigOperators Classical

variable {X : Type*} {B T : Type} [MeasurableSpace X] [Fintype B] [Fintype T]

/-- Ideal probability of a destination tile and a relative bin under the continuous
configuration measure and the independent uniform final deck translation. -/
noncomputable def tileBinLaw (μ : Measure X) (code : X → B) (a : T × B) : ℝ :=
  μ.real (code ⁻¹' {a.2}) / Fintype.card T

/-- All actual relative bins and tiles account for one unit of ideal mass. -/
theorem tileBinLaw_sum [Nonempty T] (μ : Measure X) [IsProbabilityMeasure μ]
    (code : X → B) (hm : ∀ b, MeasurableSet (code ⁻¹' {b})) :
    ∑ a : T × B, tileBinLaw μ code a = 1 := by
  rw [Fintype.sum_prod_type]
  have h : (∑ b, μ.real (code ⁻¹' {b})) = 1 := by
    simpa using (sum_measureReal_preimage_singleton (μ := μ) Finset.univ (f := code) (fun b _ => hm b))
  simp only [tileBinLaw, ← Finset.sum_div, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hT : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [Fintype B] in
/-- A nonzero ideal bin mass has a configuration carrying that address. -/
theorem tileBinLaw_support (μ : Measure X) (code : X → B) (a : T × B) :
    tileBinLaw μ code a ≠ 0 → ∃ x, code x = a.2 := by
  intro h
  by_contra! he
  have hem : code ⁻¹' {a.2} = ∅ := by ext x; simp [he x]
  simp [tileBinLaw,hem] at h

variable {D copies : ℕ} [NeZero D] {P : Type} {bits : P → ℕ} {K : Type*} {M : Type} [Fintype M]
variable (input : Fin copies → Pack D P bits K)
variable (charged : ∀ i, (input i).layout.Edge → Bool)
variable (movedBin : ∀ i, M → (input i).layout.Edge → Option (T × B))
variable (prob : Fin copies → M → ℝ)
variable {Q : Type*} [PseudoMetricSpace Q] (place : ∀ i, M → (input i).layout.Site → Q)

/-- Applying continuous configuration-bin estimates and uniform deck translation to the actual
pack counts proves the required half-length bound. The length labels and signed-permutation
invariance concern the individual geometric bins, before aggregation into any pack mean. -/
theorem half_binMean_of_measure [Nonempty T] (ω : Fin copies → M) (perm : Fin D → Equiv.Perm (T × B))
    (length : T × B → ℝ) (wireLength : Active input charged → ℝ)
    (μ : Active input charged → Measure X) [∀ w, IsProbabilityMeasure (μ w)]
    (code : Active input charged → X → B)
    (hmask : ∀ i m e, (movedBin i m e).isSome = charged i e)
    (hmove : ∀ (w : Active input charged) m, dist (place w.1 m ((input w.1).layout.src w.2.val))
      (place w.1 m ((input w.1).layout.dst w.2.val)) = wireLength w)
    (hbin : ∀ a, 0 ≤ length a) (hlen : ∀ j a, length (perm j a) = length a)
    (htag : ∀ (w : Active input charged) m a, movedBin w.1 m w.2.val = some a → length a = wireLength w)
    (hm : ∀ w b, MeasurableSet ((code w) ⁻¹' {b}))
    (hgeom : ∀ w t x, length (t, code w x) = wireLength w)
    (hinv : ∀ w j a, μ w ((code w) ⁻¹' {(perm j a).2}) = μ w ((code w) ⁻¹' {a.2}))
    (hclose : ∀ w, ∑ a, |finiteWireLaw input charged movedBin prob w a - tileBinLaw (μ w) (code w) a|
      ≤ 1 / (2 * D)) :
    (chargedLength (parallelPacks input).layout (fun v => place v.1 (ω v.1) v.2)
        (fun c => (jointBin input movedBin ω c).isSome) / copies) / 2 ≤
      matchedLength perm length (binMean input movedBin prob) := by
  apply half_binMean input charged movedBin prob place ω perm length wireLength
    (fun w => tileBinLaw (μ w) (code w)) hmask hmove _ hbin hlen htag _ _ _ hclose
  · intro w
    rw [← hmove w (ω w.1)]
    exact dist_nonneg
  · intro w
    exact tileBinLaw_sum (μ w) (code w) (hm w)
  · intro w a h
    obtain ⟨x,hx⟩ := tileBinLaw_support (μ w) (code w) a h
    rw [← hgeom w a.1 x, hx]
  · intro w j a
    exact congrArg (fun mass => ENNReal.toReal mass / Fintype.card T) (hinv w j a)

end Shortening.PackMotions

end BorderVNP
end Computability
end OAI
