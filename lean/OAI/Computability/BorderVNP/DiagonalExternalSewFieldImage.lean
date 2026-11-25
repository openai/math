import OAI.Computability.BorderVNP.DiagonalExternalSewFieldRows

/-! # Physical field representation after exterior sewing and free-port grouping -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FieldExport

open Crossing Packing.CellAddressCircuit Packing.CellAddressPhysical ParseBatchSort RoutingISA
open scoped Classical

/-- Site and internal-cable columns of a sparse pack, independent of how its
external slots are grouped or subsequently sewn. -/
structure CoreColumns {D s m n C d k w : ℕ} {P : Type*} {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m)
    {σ : Type*} (F : Fields s m n C d k w σ) (x : σ → Bool) : Prop where
  /-- Original site placement words. -/
  owner : ∀ v, value (x ∘ F.owner (siteID v)) = (F.cells (cell v)).val
  /-- Old source pointers. -/
  src : ∀ e, value (x ∘ F.ptr (.inl (.inl (edgeID e)))) = (F.sites (siteID (N.src e))).val
  /-- Old destination pointers. -/
  dst : ∀ e, value (x ∘ F.ptr (.inl (.inr (edgeID e)))) = (F.sites (siteID (N.dst e))).val
  /-- Cable width register in each occupied row. -/
  edge : ∀ e, value (x ∘ F.edgeWidth (edgeID e)) = N.width e
  /-- Staging width at each site. -/
  stage : ∀ v, value (x ∘ F.auxWidth (siteID v)) = aux v
  /-- No cable lanes in a vacant old row. -/
  edgeHole : ∀ i ∉ Set.range edgeID, value (x ∘ F.edgeWidth i) = 0
  /-- No staging words in an absent site row. -/
  stageHole : ∀ i ∉ Set.range siteID, value (x ∘ F.auxWidth i) = 0

/-- A previously verified placement supplies all the surviving sparse columns. -/
theorem CoreColumns.of_represents {D s m n C d k w : ℕ} {P : Type*} {bits : P → ℕ}
    {N : Network D P bits} {cell : N.Site → Fin C} {aux : N.Site → ℕ} {siteID : N.Site ↪ Fin s}
    {edgeID : N.Edge ↪ Fin m} {portID : P ↪ Fin n} {σ : Type*} {F : Fields s m n C d k w σ}
    {x : σ → Bool} (h : Represents N cell aux siteID edgeID portID F x) :
    CoreColumns N cell aux siteID edgeID F x :=
  ⟨h.owner,h.src,h.dst,h.edge,h.stage,h.edgeHole,h.stageHole⟩

/-- The actual layout underlying `BlockHosts.grouped`, with one free block per
team and site and the union of old and true exterior cables. -/
noncomputable abbrev finalLayout {D : ℕ} (p : Params) {P : Type} {N : Network D P (fun _ => 1)}
    {phys : PublicPort p.R p.processors p.literal p.link ≃ P} (h : BlockHosts N phys p.g) :=
  h.bundle.layout.packExternal (fun _ : FreeBlock p.R p.sites => p.g) h.groupOwner

private theorem input_value {σ : Type*} [Fintype σ] (x : σ → Bool) {b : ℕ} (pins : Fin b → σ) :
    value ((constants σ).eval x ∘ (fun j => .inl (pins j))) = value (x ∘ pins) := by
  rw [constants_eval]; rfl

/-- Exact sparse field representation of the sewn terminal pack. Old branch-dependent
columns are read from the incoming frame. The exterior row names depend only on the
retained original block hosts; the same site and edge ordinal maps can feed the prefix
scan, the cable triples and the cell evaluator. -/
theorem sewn_represents {D s old n C d k w : ℕ} (p : Params) (hp : p.Valid)
    {P : Type} {N : Network D P (fun _ => 1)} {phys : PublicPort p.R p.processors p.literal p.link ≃ P}
    (h : BlockHosts N phys p.g) (cell : N.Site → Fin C) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin old)
    {σ : Type*} [Fintype σ] (F : Fields s old n C d k w σ) (x : σ → Bool)
    (core : CoreColumns N cell aux siteID edgeID F x) (name : ℕ → ℕ → ℕ)
    (host : ∀ (u : Fin (p.R+1)) i, i < p.sites → name u.val i = (F.sites (siteID (h.host (u,i)))).val)
    (word : p.g < 2^w) :
    Packing.CellAddressPhysical.Represents (finalLayout p h) cell aux siteID (mergedEdges p hp edgeID)
      finProdFinEquiv.toEmbedding (fields F p name) ((constants σ).eval x) := by
  have bound (c : p.Wires) (side : Bool) :=
    fieldBlock_lt p.literal (2*p.literal+p.R*p.link) p.link p.g p.sites hp.block
      (show p.literal+p.R*p.link ≤ 2*p.literal+p.R*p.link by omega) hp.room c side
  have keyLow (c : p.Wires) : name c.1.1.val.1.val c.2.val.1 =
      (F.sites (siteID (h.bundle.endpoint c false))).val :=
    host c.1.1.val.1 c.2.val.1 (bound c false)
  have keyHigh (c : p.Wires) : name c.1.1.val.2.val c.2.val.2 =
      (F.sites (siteID (h.bundle.endpoint c true))).val :=
    host c.1.1.val.2 c.2.val.2 (bound c true)
  constructor
  · intro v; exact (input_value x _).trans (core.owner v)
  · rintro (e|c)
    · change value ((constants σ).eval x ∘ (fields F p name).ptr (.inl (.inl (finSumFinEquiv (.inl (edgeID e)))))) = (F.sites (siteID (N.src e))).val
      simp only [fields,Equiv.symm_apply_apply,Sum.elim_inl]
      exact (input_value x _).trans (core.src e)
    · change value ((constants σ).eval x ∘ (fields F p name).ptr (.inl (.inl (finSumFinEquiv (.inr (p.ordinal hp c)))))) = (F.sites (siteID (h.bundle.endpoint c false))).val
      simp only [fields,Equiv.symm_apply_apply,Sum.elim_inr,(p.ordinal_fields hp name c).1,keyLow]
      exact constPins_value x d _ (F.sites _).isLt
  · rintro (e|c)
    · change value ((constants σ).eval x ∘ (fields F p name).ptr (.inl (.inr (finSumFinEquiv (.inl (edgeID e)))))) = (F.sites (siteID (N.dst e))).val
      simp only [fields,Equiv.symm_apply_apply,Sum.elim_inl]
      exact (input_value x _).trans (core.dst e)
    · change value ((constants σ).eval x ∘ (fields F p name).ptr (.inl (.inr (finSumFinEquiv (.inr (p.ordinal hp c)))))) = (F.sites (siteID (h.bundle.endpoint c true))).val
      simp only [fields,Equiv.symm_apply_apply,Sum.elim_inr,(p.ordinal_fields hp name c).2.1,keyHigh]
      exact constPins_value x d _ (F.sites _).isLt
  · intro a
    change value ((constants σ).eval x ∘ (fields F p name).ptr (.inr (finProdFinEquiv a))) =
      (F.sites (siteID (h.groupOwner a))).val
    simp only [fields,Equiv.symm_apply_apply,host a.1 a.2.val a.2.isLt]
    exact constPins_value x d _ (F.sites _).isLt
  · rintro (e|c)
    · change value ((constants σ).eval x ∘ (fields F p name).edgeWidth (finSumFinEquiv (.inl (edgeID e)))) = N.width e
      simp only [fields,Equiv.symm_apply_apply,Sum.elim_inl]
      exact (input_value x _).trans (core.edge e)
    · change value ((constants σ).eval x ∘ (fields F p name).edgeWidth (finSumFinEquiv (.inr (p.ordinal hp c)))) = cableWidth c
      simp only [fields,Equiv.symm_apply_apply,Sum.elim_inr,(p.ordinal_fields hp name c).2.2]
      exact constPins_value x w _ ((pieceWidth_le _ _ hp.block c).trans_lt word)
  · intro v; exact (input_value x _).trans (core.stage v)
  · intro _; exact constPins_value x _ _ word
  · intro i hole
    have inactive := merged_hole p hp edgeID i hole
    rcases key : (finSumFinEquiv.symm i : Fin old ⊕ Fin p.slots) with j|j
    · simp only [key] at inactive
      simp only [fields,key,Sum.elim_inl,input_value]
      exact core.edgeHole j inactive
    · simp only [key] at inactive
      simp only [fields,key,Sum.elim_inr,p.width_unused hp j inactive]
      exact constPins_value x _ _ (Nat.two_pow_pos _)
  · intro i hole; exact (input_value x _).trans (core.stageHole i hole)
  · intro i hole; exact (hole ⟨finProdFinEquiv.symm i,finProdFinEquiv.apply_symm_apply i⟩).elim

end Diagonal.ExternalSew.FieldExport

end BorderVNP
end Computability
end OAI
