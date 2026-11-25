import OAI.Hierarchy.DescentGadgetNetwork
import OAI.Hierarchy.DescentMotifClasses
import OAI.Hierarchy.DescentNetworkPartition

namespace OAI
/-! # Cable width of the contracted six-party network -/

namespace Hierarchy.DescentSixParty.GadgetNetwork

open Computability.BorderVNP.Crossing DescentNetworkPartition
open scoped BigOperators Classical
noncomputable section

variable {I C : Type} [Fintype I] {D d : ℕ} {P : Type*} {bits : P → ℕ}
variable (N : Network D P bits) (pick : I × Fin 2 ↪ N.Edge) (sw : I → Fin 8 → ℕ)
variable (layout : Bool) (pack : N.Site → C)
variable (pos : Merged N pick layout pack → EuclideanSpace ℝ (Fin d)) (hpos : ∀ c, ‖pos c‖ ≤ 1)

/-- The true quotient of the installed motif graph, with the chosen placement of its parts. -/
abbrev merged : Network d P bits :=
  quotient (physical N pick sw) (newSite N pick layout pack) pos hpos

local notation "Q" => merged N pick sw layout pack pos hpos
local notation "M" => physical N pick sw
local notation "loc" => newSite N pick layout pack

/-- An original site represents each new site, even in a part containing auxiliary parties. -/
theorem merged_sites_le : Fintype.card (Q).Site ≤ Fintype.card N.Site :=
  merged_card N pick layout pack

/-- Budget charged to an old physical edge before contracting equal endpoints. -/
def chargedWidth : Edge (I:=I) N → ℕ
  | .inl e => if e ∈ (Finset.univ.map pick)ᶜ then N.width e else 0
  | .inr (.inl _) => 0
  | .inr (.inr t) => if retained layout t.2 then sw t.1 t.2 else 0

theorem external_width (e : (M).Edge) (crosses : loc ((M).src e) ≠ loc ((M).dst e)) :
    (M).width e = chargedWidth N pick sw layout e := by
  rcases e with e | (⟨i,s⟩ | ⟨i,e⟩)
  · by_cases hit : e ∈ Finset.univ.map pick
    · obtain ⟨⟨i,s⟩, _, rfl⟩ := Finset.mem_map.mp hit
      exact (crosses (by
        simpa only [physical, source, target, selected_pick] using
          source_merge N pick layout pack i s)).elim
    · simp [physical, width, chargedWidth, hit]
  · exact (crosses (target_merge N pick layout pack i s).symm).elim
  · by_cases keep : retained layout e
    · simp [physical, width, chargedWidth, keep]
    · exact (crosses (private_merge N pick layout pack i e keep)).elim

/-- Restriction to the remaining cables can only lower a nonnegative sum. -/
theorem crossing_sum_le (cost : (M).Edge → ℕ) : (∑ e : (Q).Edge, cost e.val) ≤ ∑ e : (M).Edge, cost e := by
  classical
  let crosses (e : (M).Edge) := loc ((M).src e) ≠ loc ((M).dst e)
  change (∑ e : {e : (M).Edge // crosses e}, cost e.val) ≤ _
  rw [← Fintype.sum_subtype_add_sum_subtype crosses cost]
  exact Nat.le_add_right _ _

/-- Only untouched original cables and retained supply cables can cross between parts. -/
theorem merged_width_le :
    (∑ e : (Q).Edge, (Q).width e) ≤ (∑ e ∈ (Finset.univ.map pick)ᶜ, N.width e) + surviving sw layout := by
  classical
  let cost := chargedWidth N pick sw layout
  calc
    _ = ∑ e : (Q).Edge, cost e.val :=
      Finset.sum_congr rfl fun e _ => external_width N pick sw layout pack e.val e.property
    _ ≤ ∑ e : (M).Edge, cost e := crossing_sum_le N pick sw layout pack pos hpos cost
    _ = _ := by
      change (∑ e : Edge (I:=I) N, chargedWidth N pick sw layout e) = _
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, chargedWidth, Finset.sum_const_zero,
        zero_add, Finset.sum_ite_mem_eq, surviving]

theorem picked_width (b : ℕ) (z : I → ℕ) (fit : ∀ i s, N.width (pick (i,s)) = z i * b) :
    (∑ e ∈ Finset.univ.map pick, N.width e) = 2*b*(∑ i, z i) := by
  classical
  rw [Finset.sum_map, Fintype.sum_prod_type]
  simp only [fit, Fin.sum_univ_two, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

/-- The two selected old demands of each instance pay exactly twice its input width. -/
theorem merged_width_paid (b : ℕ) (z : I → ℕ) (fit : ∀ i s, N.width (pick (i,s)) = z i * b) :
    (∑ e : (Q).Edge, (Q).width e) + 2*b*(∑ i, z i) ≤ (∑ e : N.Edge, N.width e) + surviving sw layout := by
  classical
  have paid := picked_width N pick b z fit
  have total := Finset.sum_compl_add_sum (Finset.univ.map pick) N.width
  have bound := merged_width_le N pick sw layout pack pos hpos
  omega

end
end Hierarchy.DescentSixParty.GadgetNetwork

end OAI
