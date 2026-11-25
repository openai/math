import OAI.Computability.BorderVNP.PackedGridPlacement
import OAI.Computability.BorderVNP.PackedInitialLayout
import OAI.Computability.BorderVNP.ParseFanoutBounds

/-! # Ordered initial placement of the actual bit network

Each input leaf keeps its input ordinal. Other vertices cycle through the cells.
A tile thus sees only the incidences of its two bounded blocks, and the resulting
private routing realizes the public Cayley grid without changing its port numbering.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open BorderVNP.Packing BorderVNP.Packing.GridPlacement Finset
open scoped Classical
variable {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits)

/-- The physical fine sites other than the attached external leaves. -/
abbrev OtherSite := {v : N.Site // v ∉ Set.range N.attach}

/-- Number the distinct input leaves in the prescribed order and then the other sites. -/
noncomputable def siteOrder {n : ℕ} (input : P ≃ Fin n) (inject : Function.Injective N.attach) :
    N.Site ≃ Fin n ⊕ Fin (Fintype.card N.OtherSite) :=
  (Equiv.Set.sumCompl (Set.range N.attach)).symm.trans
    (((Equiv.ofInjective N.attach inject).symm.trans input).sumCongr (Fintype.equivFin _))

/-- The leaf numbering on each external port is exactly its specified public ordinal. -/
theorem siteOrder_attach {n : ℕ} (input : P ≃ Fin n) (inject : Function.Injective N.attach) (p : P) :
    N.siteOrder input inject (N.attach p) = Sum.inl (input p) := by
  simp [siteOrder,Equiv.Set.sumCompl_symm_apply_of_mem]

variable {G : Type} [Group G] [Fintype G]

/-- Public block placement for the fine sites after choosing the external and tile orders. -/
noncomputable def initialPlace {n : ℕ} (input : P ≃ Fin n) (inject : Function.Injective N.attach)
    (order : Fin (Fintype.card G) ≃ G) (v : N.Site) : G :=
  order ((initialAddress (Fintype.card_pos (α := G)) n (Fintype.card N.OtherSite)
    (N.siteOrder input inject v)).1)

/-- The public leaf slots are consecutive blocks in the given input order. -/
theorem initialPlace_attach {n : ℕ} (input : P ≃ Fin n) (inject : Function.Injective N.attach)
    (order : Fin (Fintype.card G) ≃ G) (p : P) :
    N.initialPlace input inject order (N.attach p) =
      order ((leafSlot (Fintype.card_pos (α := G)) n (input p)).1) := by
  rw [initialPlace,siteOrder_attach]; rfl

/-- Each endpoint multiplicity is at most three times the two block capacities at a tile. -/
noncomputable def initialLoad {n : ℕ} (_ : P ≃ Fin n) (G : Type) [Fintype G] :=
  3 * (blockWidth n (Fintype.card G) + blockWidth (Fintype.card N.OtherSite) (Fintype.card G))

/-- A bit network with distinct external leaves and internal degree at most three has
the required physical routing after the external leaf slots have been fixed. -/
theorem routed_initial {J : Type} (step : J → G) (invStep : ∀ j, ∃ k, step k = (step j)⁻¹)
    {n h : ℕ} (input : P ≃ Fin n) (inject : Function.Injective N.attach)
    (order : Fin (Fintype.card G) ≃ G)
    (degree : ∀ v, (univ.filter fun e => N.src e = v).card + (univ.filter fun e => N.dst e = v).card ≤ 3)
    (short : ∀ u : G, ∃ w : List J, w.length ≤ h ∧ (w.map step).prod = u) :
    Nonempty (Routed N (N.initialPlace input inject order) step invStep (N.initialLoad input G) h) := by
  obtain ⟨p,hp⟩ := CayleyPaths.simple_paths step invStep h short
  let idx := N.siteOrder input inject
  have hd (v) : (univ.filter fun e => idx (N.src e) = v).card +
      (univ.filter fun e => idx (N.dst e) = v).card ≤ 3 := by
    simpa only [← Equiv.eq_symm_apply] using degree (idx.symm v)
  have hs (u : G) : (CayleyPaths.sites step invStep p u).card ≤ h+1 := by
    rw [CayleyPaths.sites,List.toFinset_card_of_nodup (p u).nodup_support,(p u).val.length_support]
    exact Nat.succ_le_succ (hp u)
  obtain ⟨mid,hm⟩ := exists_initial_routing order (CayleyPaths.sites step invStep p)
    (fun e => idx (N.src e)) (fun e => idx (N.dst e)) hd hs
  let cell := N.initialPlace input inject order
  let left := cell ∘ N.src
  let right := cell ∘ N.dst
  refine ⟨fun e => CayleyPaths.route step invStep p (left e) (right e) (mid e), fun g => ?_⟩
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_sum]
  apply le_trans (Finset.sum_le_sum fun e _ => Nat.cast_le.mpr (CayleyPaths.count_route
    step invStep p left right e (mid e) g))
  apply (hm g).trans
  apply le_trans _ (real_bound_le_cableWidth G (N.initialLoad input G) h)
  simp only [initialLoad,Nat.cast_add,Nat.cast_one]
  rfl

end Crossing.Network

namespace ParseBatch.Layout

open Finset
open scoped Classical
variable {X W T : Type} [Fintype X] [Fintype W] [Fintype T] (L : Layout X W T)

/-- Distinct public input pins of the fanout network occupy distinct leaf sites. -/
theorem distinct_input_leaves : Function.Injective L.network.attach :=
  fun _ _ h => Sum.inl.inj (Sum.inl.inj (Sum.inr.inj h))

/-- The sum of source and destination counts includes both ends of loops and is bounded
by the degree bound that also charges external pins. -/
theorem internal_degree (v : L.Site) :
    (univ.filter fun e => L.network.src e = v).card + (univ.filter fun e => L.network.dst e = v).card ≤
      (univ.filter fun e => L.incident e = v).card := by
  simp only [card_eq_sum_ones,sum_filter]
  change _ ≤ ∑ e : X ⊕ (L.Edge × Bool), if L.incident e = v then 1 else 0
  conv_rhs => rw [Fintype.sum_sum_type, Fintype.sum_prod_type_right (fun e : L.Edge × Bool => if L.incident (.inr e) = v then 1 else 0), Fintype.sum_bool]
  simp only [incident,Bool.false_eq_true,ite_false,ite_true]
  omega

end ParseBatch.Layout

end BorderVNP
end Computability
end OAI
