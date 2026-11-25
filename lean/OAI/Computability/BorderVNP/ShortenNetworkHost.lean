import OAI.Computability.BorderVNP.ShortenNetworkIntervals
import OAI.Computability.BorderVNP.ShortenEpochPlacement

/-!
# Charging an actual profile replacement in the product host

Only the selected, charged intervals are removed. The retained exterior
includes all old local and uncharged wires. Every hook and every wire of
the inserted profile (including its selectors) is added to the charge.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Crossing
open scoped BigOperators Classical

variable {H : Type*} [PseudoMetricSpace H] {D : ℕ} {P : Type*} {bits : P → ℕ}

/-- Total width-weighted length of the designated charged wires at their host sites. -/
noncomputable def chargedLength (N : Network D P bits) (place : N.Site → H)
    (charged : N.Edge → Bool) : ℝ :=
  ∑ e, if charged e then (N.width e : ℝ) * dist (place (N.src e)) (place (N.dst e)) else 0

/-- Cost of the selected old segments before a joint replacement. -/
noncomputable def selectedLength (N : Network D P bits) (place : N.Site → H)
    (S : Finset N.Edge) : ℝ :=
  ∑ e : ↥S, (N.width e.val : ℝ) * dist (place (N.src e.val)) (place (N.dst e.val))

/-- The actual retained endpoint of a hook. -/
noncomputable def oldEndpoint (N : Network D P bits) (S : Finset N.Edge) (place : N.Site → H)
    (i : N.CutPorts S) := place ((N.cut S).attach (.inr i))

/-- Charge every new hook and profile cable, and inherit the old mask on the exterior. -/
def profileCharges (N : Network D P bits) (S : Finset N.Edge)
    (G : Network D (N.CutPorts S) (N.cutWidths S)) (charged : N.Edge → Bool) :
    ((N.cut S).sew G).Edge → Bool :=
  Sum.elim (fun _ => true) (Sum.elim (fun e => charged e.val) (fun _ => true))

/-- Exact accounting for the network that computes a profile summand. -/
theorem chargedLength_replace (N : Network D P bits) (place : N.Site → H)
    (charged : N.Edge → Bool) (S : Finset N.Edge) (hc : ∀ e ∈ S, charged e = true)
    (G : Network D (N.CutPorts S) (N.cutWidths S)) (sites : G.Site → H) :
    chargedLength ((N.cut S).sew G) (Sum.elim place sites) (profileCharges N S G charged) =
      chargedLength N place charged - selectedLength N place S +
        (placedCost G sites + hookCost G sites (oldEndpoint N S place)) := by
  let old := fun e : N.Edge => if charged e then
    (N.width e : ℝ) * dist (place (N.src e)) (place (N.dst e)) else 0
  let sides : ↥S ⊕ {e : N.Edge // e ∉ S} ≃ N.Edge := Equiv.sumCompl (fun e => e ∈ S)
  have hsplit := sides.sum_comp old
  rw [Fintype.sum_sum_type] at hsplit
  change (∑ e : ↥S, old e.val) + (∑ e : {e : N.Edge // e ∉ S}, old e.val) = ∑ e, old e at hsplit
  have hsel : (∑ e : ↥S, old e.val) = selectedLength N place S := by
    unfold selectedLength
    exact Finset.sum_congr rfl fun e _ => by simp [old, hc e.val e.property]
  rw [hsel] at hsplit
  unfold chargedLength
  change (∑ e : N.CutPorts S ⊕ ({e : N.Edge // e ∉ S} ⊕ G.Edge), _) = _
  rw [Fintype.sum_sum_type]
  conv_lhs => rhs; rw [Fintype.sum_sum_type]
  change hookCost G sites (oldEndpoint N S place) +
    ((∑ e : {e : N.Edge // e ∉ S}, old e.val) + placedCost G sites) =
    (∑ e, old e) - selectedLength N place S + _
  linarith only [hsplit]

/-- A fractional profile saving (including its hooks) subtracts that same
fraction of the selected old length from the total charged length of the pack. -/
theorem chargedLength_replace_le (N : Network D P bits) (place : N.Site → H)
    (charged : N.Edge → Bool) (S : Finset N.Edge) (hc : ∀ e ∈ S, charged e = true)
    (G : Network D (N.CutPorts S) (N.cutWidths S)) (sites : G.Site → H)
    {ν : ℝ} (hs : placedCost G sites + hookCost G sites (oldEndpoint N S place) ≤
      (1 - ν) * selectedLength N place S) :
    chargedLength ((N.cut S).sew G) (Sum.elim place sites) (profileCharges N S G charged) ≤
      chargedLength N place charged - ν * selectedLength N place S := by
  rw [chargedLength_replace N place charged S hc]
  linarith only [hs]

end Epoch

end BorderVNP
end Computability
end OAI
