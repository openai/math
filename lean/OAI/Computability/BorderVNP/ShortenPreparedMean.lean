import OAI.Computability.BorderVNP.ShortenCubeEnumeration
import OAI.Computability.BorderVNP.ShortenPreparedLabels
import OAI.Computability.BorderVNP.ShortenEpochSampleMean

/-!
# The norm of the sampled bin mean for prepared segment types

Uniform post-translation divides the total active width equally among tiles.
The shortest prepared length then bounds this width by the normalized
charged length. The resulting multiplier is fixed before the cover level,
the fan-in and the sampled motions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Crossing Epoch Cover Cover.Frame Hecke Framed Packing PackMotions Set Filter
open scoped Classical Topology BorderVNP.Epoch.Cube

variable {D : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
variable (B : PreparedBins D S h η) {copies d n : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
variable (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
variable (kind : Active input active → B.types) (b : Active input active → Cube D → gamma 1)

/-- Each tagged relative classifier fiber is either a regular bin of its type
or the empty set when the two public type indices differ. -/
theorem measurable_catalogCode (t : B.types) (u : B.Bin) :
    MeasurableSet ((fun x => (⟨t,(B.chart t).code x⟩ : B.Bin)) ⁻¹' {u}) := by
  rcases u with ⟨u,b⟩
  by_cases he : t = u
  · subst u
    simpa only [Set.preimage,mem_singleton_iff,Sigma.mk.inj_iff,heq_eq_eq,true_and] using (B.regular t b).1
  · have hf : (fun x => (⟨t,(B.chart t).code x⟩ : B.Bin)) ⁻¹' {⟨u,b⟩} = ∅ := by
      ext x
      simp [Sigma.ext_iff,he]
    rw [hf]; exact MeasurableSet.empty

set_option maxHeartbeats 600000 in
/-- The true mean norm bound for the chosen whole-pack sample, directly in terms
of the charged length of the actual measured union of input sites. -/
theorem tag_mean_norm {δ : ℝ} (hδ : 0 < δ) (hmin : ∀ t : B.types, δ ≤ B.length t)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n))
    (ω : Fin copies → PackSample (lattice 1) elliptic (Cube D) d n)
    (hl : ∀ w : Active input active, ∀ s : PackSample (lattice 1) elliptic (Cube D) d n,
      dist (sampleMove s (sites w.1 ((input w.1).layout.src w.2.val)))
        (sampleMove s (sites w.1 ((input w.1).layout.dst w.2.val))) = B.length (kind w)) :
    let mb := B.tag (d := d) (n := n) input active kind b
    Real.sqrt (Fintype.card (Cube D → Deck d)) * Real.sqrt (binEnergy (binMean input mb (sampleProb d n))) ≤
      δ⁻¹ * (chargedLength (parallelPacks input).layout (movedOld input ω sites)
        (fun c => (jointBin input mb ω c).isSome) / copies) := by
  intro mb
  have H := sampledBinMean_norm_le_chargedLength (I := Cube D) (B := B.Bin) (depth := d) (n := n) (Q := SurfaceHost (Cube D) d) input active (fun w => speed (kind w).val)
    (fun w x => (⟨kind w,(B.chart (kind w)).code x⟩ : B.Bin))
    (fun w => sourceFrame (kind w).val (b w)) (fun w => movedCarry (kind w).val (b w))
    (fun w => B.measurable_catalogCode (kind w))
    (fun i s v => sampleMove s (sites i v)) ω (fun w => B.length (kind w)) hδ (fun w => hmin (kind w)) hl
  dsimp only [mb,tag,movedOld]
  rw [inv_mul_eq_div]
  exact H

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
