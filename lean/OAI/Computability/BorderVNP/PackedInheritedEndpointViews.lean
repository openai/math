import OAI.Computability.BorderVNP.PackedInheritedLayerCircuit

/-! # Site-incidence scans before persistent work widths are known

Singleton-cell scans use only endpoint names and live widths. Their output
therefore computes the new incoming sizes from which the actual stage widths
are subsequently formed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Views

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical CellAddressViews
open ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork
open private literals eval_literals capacity from OAI.Computability.BorderVNP.PackedInheritedAddress
open private zero_value from OAI.Computability.BorderVNP.PackedCellAddressCircuit
open scoped Classical

variable {D s m n C d k w : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)
variable (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- The physical endpoint pins, including zero-width holes. All site staging and
placement columns are ignored by this virtual scan. -/
structure EndpointData (x : σ → Bool) : Prop where
  /-- The named source of a present cable. -/
  src : ∀ z, value (x ∘ F.ptr (.inl (.inl (edgeID z)))) = (F.sites (siteID (N.src z))).val
  /-- The named destination of a present cable. -/
  dst : ∀ z, value (x ∘ F.ptr (.inl (.inr (edgeID z)))) = (F.sites (siteID (N.dst z))).val
  /-- The site to which an exterior port is attached. -/
  attach : ∀ p, value (x ∘ F.ptr (.inr (portID p))) = (F.sites (siteID (N.attach p))).val
  /-- Cable word width. -/
  edge : ∀ z, value (x ∘ F.edgeWidth (edgeID z)) = N.width z
  /-- Exterior argument width. -/
  port : ∀ p, value (x ∘ F.portWidth (portID p)) = bits p
  /-- Unoccupied old cable slots contribute no lanes. -/
  edgeHole : ∀ i, i ∉ Set.range edgeID → value (x ∘ F.edgeWidth i) = 0
  /-- Unoccupied exterior port slots contribute no lanes. -/
  portHole : ∀ i, i ∉ Set.range portID → value (x ∘ F.portWidth i) = 0

omit [Fintype σ] in
/-- A complete physical directory supplies every field consumed by the virtual scan. -/
theorem EndpointData.of_rep {cell : N.Site → Fin C} {aux : N.Site → ℕ} {x : σ → Bool}
    (h : Represents N cell aux siteID edgeID portID F x) : EndpointData N F siteID edgeID portID x :=
  ⟨h.src,h.dst,h.attach,h.edge,h.port,h.edgeHole,h.portHole⟩

variable {x : σ → Bool} (h : EndpointData N F siteID edgeID portID x)

include h in
private theorem virtual_rep : Represents N siteID (fun _ => 0) siteID edgeID portID (fields F) (literals.eval x) := by
  constructor
  · intro v
    simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inr,id_eq] using value_encode (F.sites (siteID v))
  · intro e; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.src e
  · intro e; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.dst e
  · intro p; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.attach p
  · intro e; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.edge e
  · intro _; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inr,id_eq] using zero_value w
  · intro p; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.port p
  · intro i hi; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.edgeHole i hi
  · intro i _; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inr,id_eq] using zero_value w
  · intro i hi; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.portHole i hi

variable [Fintype P] (fit : ∀ v, incoming N v < 2^w)
include h fit

/-- Read the exact beginning of any incident word, selecting the source for a loop. -/
theorem incident_value (v : N.Site) (z : Incident N v) :
    value (fun j => (Views.frame F).eval x (.inl (Layer.edgeEnd (edgeID z.val) (decide (N.src z.val = v))),j)) =
    wireStart N edgeID portID v z := by
  obtain ⟨z,hz⟩ := z
  have hv := virtual_rep N F siteID edgeID portID h
  by_cases hs : N.src z = v
  · subst v
    simp only [decide_true,Layer.edgeEnd,ite_true,Views.frame,Frame.subst_eval]
    exact (CellAddressViews.source_value N siteID (fun _ => 0) siteID edgeID portID (fields F) hv
      (capacity N siteID fit) z).trans (wire_relabel N siteID edgeID portID _ _)
  · have hd := hz.resolve_left hs
    subst v
    simp only [hs,decide_false,Layer.edgeEnd,Views.frame,Frame.subst_eval]
    exact (CellAddressViews.dest_value N siteID (fun _ => 0) siteID edgeID portID (fields F) hv
      (capacity N siteID fit) z).trans (wire_relabel N siteID edgeID portID _ _)

/-- Every exterior port can be read directly from the endpoint directory. -/
theorem attached_value (v : N.Site) (p : Attached N v) :
    value (fun j => (Views.frame F).eval x (.inl (.inr (portID p.val)),j)) = portStart N edgeID portID v p := by
  obtain ⟨p,rfl⟩ := p
  simp only [Views.frame,Frame.subst_eval]
  exact (CellAddressViews.port_value N siteID (fun _ => 0) siteID edgeID portID (fields F)
    (virtual_rep N F siteID edgeID portID h) (capacity N siteID fit) p).trans (port_relabel N siteID edgeID portID _ _)

/-- The exact incoming width is available before any per-site auxiliary width has been installed. -/
theorem input_size (v : N.Site) :
    value (fun j => (Views.frame F).eval x (.inr (.inr (2,siteID v)),j)) = incoming N v := by
  have hv := CellAddressViews.marker_value N siteID (fun _ => 0) siteID edgeID portID (fields F)
    (virtual_rep N F siteID edgeID portID h) (capacity N siteID fit) (siteID v) 2
  simpa [Views.frame,incoming,siteSize,guessed_relabel,supplied_relabel] using hv

end Packing.Inherited.Views

end BorderVNP
end Computability
end OAI
