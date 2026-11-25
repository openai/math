import OAI.Computability.BorderVNP.ShortenNetworkBundle
import OAI.Computability.BorderVNP.ShortenNetworkHost
import Mathlib.Data.Sigma.Order

/-!
# The saving of the physical histogram network after insertion

A bundle can be assembled from any finite set of intervals with the
required width in each direction. Sorting the public cable names and
then the within-cable indices gives the common order used at both ends.
After placement, the saving includes each interval's individual hooks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Bundle

open Crossing Epoch
open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
variable {S : Finset N.Edge} {w : ℕ}

/-- Sort matched intervals by cable name, then by the bit index within a cable.
Matching the width in each axis suffices to construct a bundle. -/
noncomputable def sorted [LinearOrder N.Edge] (axis : ↥S → Fin D) (positive : ↥S → Bool)
    (hw : ∀ d, (∑ e : {e : ↥S // axis e = d}, N.width e.val.val) = w) : Bundle N S w where
  axis := axis
  positive := positive
  order d :=
    let W := Σₗ e : {e : ↥S // axis e = d}, Fin (N.width e.val.val)
    (Fintype.orderIsoFinOfCardEq W (by
      change Fintype.card (Σ e : {e : ↥S // axis e = d}, Fin (N.width e.val.val)) = w
      simpa using hw d)).symm.toEquiv

/-- Width in each matched direction is the common terminal width. -/
theorem axisWidth (b : Bundle N S w) (d : Fin D) :
    (∑ e : {e : ↥S // b.axis e = d}, N.width e.val.val) = w := by
  simpa using Fintype.card_congr (b.order d)

/-- Matched bit width, with one copy per old cable. -/
theorem totalWidth (b : Bundle N S w) : (∑ e : ↥S, N.width e.val) = D * w := by
  rw [← Fintype.sum_fiberwise b.axis (fun e : ↥S => N.width e.val)]
  simp [b.axisWidth]

/-- Width delivered to the replacement, counting both endpoint hooks. -/
theorem hookWidth (b : Bundle N S w) :
    (∑ p : N.CutPorts S, (N.cutWidths S p : ℝ)) = 2 * (D : ℝ) * w := by
  rw [Fintype.sum_sum_type]
  have h : (∑ e : ↥S, (N.width e.val : ℝ)) = (D : ℝ) * w := by exact_mod_cast b.totalWidth
  change (∑ e : ↥S, (N.width e.val : ℝ)) + (∑ e : ↥S, (N.width e.val : ℝ)) = _
  linarith only [h]

/-- For equal-length old segments the matched length is exactly half the
segment length times the sum of the widths of the individual endpoint hooks. -/
theorem selectedLength_eq {H : Type*} [PseudoMetricSpace H] (b : Bundle N S w) (place : N.Site → H) (s : ℝ)
    (hlen : ∀ e : ↥S, dist (place (N.src e.val)) (place (N.dst e.val)) = 2*s) :
    selectedLength N place S = s * ∑ p : N.CutPorts S, (N.cutWidths S p : ℝ) := by
  unfold selectedLength
  simp_rw [hlen]
  rw [← Finset.sum_mul, b.hookWidth]
  have h : (∑ e : ↥S, (N.width e.val : ℝ)) = (D : ℝ) * w := by exact_mod_cast b.totalWidth
  rw [h]; ring

variable {I : Type*} [Fintype I]

/-- Each paid identity admits a single strictly positive saving and radius
for every group of matched intervals and every attained histogram. The charged
output is the sewn network on the original external ports. -/
theorem paid_host_saving {K : Type*} [Field K] {m : ℕ} (e : PaidIdentity K D m)
    (hD : 0 < D) (hm : 0 < m) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ h : ℝ, 0 < h ∧ ∀ s ∈ Set.Icc (0 : ℝ) h,
      ∀ {P : Type*} {bits : P → ℕ} (N : Network D P bits)
        (place : N.Site → HyperbolicHost I) (charged : N.Edge → Bool) (S : Finset N.Edge),
      (∀ c ∈ S, charged c = true) → ∀ j (b : Bundle N S (j*m))
        (hist : Fin e.count → ℕ), (∑ a, hist a) = j →
      ∀ (axes : EuclideanSpace ℝ (Fin D) →ₗᵢ[ℝ] PiLp 2 (fun _ : I => ℂ))
        (center : HyperbolicHost I),
      (∀ c : ↥S, dist (place (N.src c.val)) (place (N.dst c.val)) = 2*s) →
      (∀ q : N.CutPorts S, dist (oldEndpoint N S place q)
        (shiftTo center (productLine (axes (antipodalPosition (b.terminal q))) s)) ≤ ν/4*s) →
      let G := b.expose (e.profile j hist)
      let sites := fun v => shiftTo center (productChart (s • axes (G.position v)))
      chargedLength ((N.cut S).sew G) (Sum.elim place sites) (profileCharges N S G charged) ≤
        chargedLength N place charged - (ν/2) * selectedLength N place S := by
  obtain ⟨ν, hν, hbudget⟩ := e.profile_uniform_saving hD hm
  obtain ⟨h, hh, hscale⟩ := place_profile_saving (I := I) hν
  refine ⟨ν, hν, h, hh, ?_⟩
  intro s hs P bits N place charged S hc j b hist hj axes center hlen hnear G sites
  apply chargedLength_replace_le N place charged S hc G sites
  have hcost : G.cost ≤ (1-ν) * ∑ q : N.CutPorts S, (N.cutWidths S q : ℝ) := by
    rw [b.hookWidth, Nat.cast_mul]
    change (e.profile j hist).cost ≤ _
    convert hbudget j hist hj using 1
    ring
  have hnear' (q : N.CutPorts S) : dist (oldEndpoint N S place q)
      (shiftTo center (productLine (axes (G.position (G.attach q))) s)) ≤ ν/4*s := by
    change dist _ (shiftTo center (productLine
      (axes ((e.profile j hist).position ((e.profile j hist).attach (b.terminal q)))) s)) ≤ _
    rw [e.profile_placedAt j hist (b.terminal q)]
    exact hnear q
  have hactual := hscale s hs G axes center (oldEndpoint N S place) hcost hnear'
  rw [b.selectedLength_eq place s hlen]
  simpa only [mul_assoc] using hactual

end Shortening.Bundle

end BorderVNP
end Computability
end OAI
