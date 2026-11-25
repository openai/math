import OAI.Computability.BorderVNP.PackedSewnWireRoster
import OAI.Computability.BorderVNP.PackedSewnFragmentProjection

/-! # Exact physical cable intervals in the actual exterior-sewn directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.WireFragments

open Crossing Inherited CellAddressCircuit CellAddressPhysical ParseBatchSort VPVNP.VerifierNetwork
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport
open scoped Classical

variable {D s m n C k w : ℕ} {A : Type} [Fintype A] {bits : A → ℕ} (L : Network D A bits)
variable (siteID : L.Site ↪ Fin s) (edgeID : L.Edge ↪ Fin m) (portID : A ↪ Fin n)
variable {σ : Type} [Fintype σ] (F : Fields s m n C w k w σ) (p : Params) (name : ℕ → ℕ → ℕ)
variable (present : Fin m → σ)

/-- The stable appended cable rectangle begins after all retained cable slots. -/
def retainedRow (m extra : ℕ) (i : Fin m) : Fin (m+extra) := finSumFinEquiv (.inl i : Fin m ⊕ Fin extra)

/-- The public four-word fragment rows on the concrete pre-sew and appended post-sew fields. -/
noncomputable def sewnFrame : Frame (σ ⊕ Bool) (Fragment.Pin (2*m) w) :=
  frame F (FieldExport.fields F p name) Sum.inl present (retainedRow m p.slots)

variable (hp : p.Valid) {P : Type} (lane : P ↪ Σ a, Fin (bits a))
variable {physical : PublicPort p.R p.processors p.literal p.link ≃ P}
variable (hosts : BlockHosts (FineView.layout L lane) physical p.g)
variable (x : σ ⊕ Bool → Bool)
variable (pre : Views.EndpointData L F siteID edgeID portID (x ∘ Sum.inl))
variable (post : Views.EndpointData (finalLayout p hosts) (FieldExport.fields F p name)
    siteID (mergedEdges p hp edgeID) finProdFinEquiv.toEmbedding x)
variable (oldFit : ∀ v, incoming L v < 2^w) (newFit : ∀ v, incoming (finalLayout p hosts) v < 2^w)

local notation3 (prettyPrint := false) "interval" => wireInterval L lane hosts.bundle (fun _ : FreeBlock p.R p.sites => p.g)
  hosts.groupOwner edgeID portID (mergedEdges p hp edgeID) finProdFinEquiv.toEmbedding

include pre post oldFit newFit in
/-- At its genuine row the decoded fragment is exactly the old cable's affine interval,
with the source ordinal taken at the same site's new sparse cable slot. -/
theorem sewn_parse (v : L.Site) (z : Incident L v) :
    Fragment.parse ((sewnFrame F p name present).eval x) (ordinal (edgeID z.val,decide (L.src z.val=v))) =
      ⟨(F.sites (siteID v)).val,interval v z⟩ := by
  let src := decide (L.src z.val=v)
  let output := finalLayout p hosts
  let rows := mergedEdges p hp edgeID
  let newWire : Incident output v := ⟨.inl z.val,z.property⟩
  have oldStart := Views.incident_value L F siteID edgeID portID pre oldFit v z
  have newStart := Views.incident_value output (FieldExport.fields F p name) siteID rows finProdFinEquiv.toEmbedding
    post newFit v newWire
  have owner : value ((x ∘ Sum.inl) ∘ F.ptr (Layer.edgeEnd (edgeID z.val) src)) = (F.sites (siteID v)).val := by
    by_cases h : L.src z.val=v
    · simpa only [src,h,decide_true,Layer.edgeEnd,ite_true] using (pre.src z.val).trans (congrArg (fun u => (F.sites (siteID u)).val) h)
    · simpa only [src,h,decide_false,Layer.edgeEnd,Bool.false_eq_true,ite_false] using (pre.dst z.val).trans
        (congrArg (fun u => (F.sites (siteID u)).val) (z.property.resolve_left h))
  have moved : rows newWire.val = retainedRow m p.slots (edgeID z.val) := rfl
  change value (fun j => (Views.frame (FieldExport.fields F p name)).eval x
    (.inl (Layer.edgeEnd (rows newWire.val) src),j)) = wireStart output rows finProdFinEquiv.toEmbedding v newWire at newStart
  rw [moved] at newStart
  rw [sewnFrame,frame_parse]
  change Fragment.Parsed.mk (value ((x ∘ Sum.inl) ∘ F.ptr (Layer.edgeEnd (edgeID z.val) src)))
    ⟨value (fun j => (Views.frame F).eval (x ∘ Sum.inl) (.inl (Layer.edgeEnd (edgeID z.val) src),j)),
     value ((x ∘ Sum.inl) ∘ F.edgeWidth (edgeID z.val)),some (value (fun j => (Views.frame (FieldExport.fields F p name)).eval x
      (.inl (Layer.edgeEnd (retainedRow m p.slots (edgeID z.val)) src),j)))⟩ = _
  rw [owner,oldStart,pre.edge,newStart]
  rfl

private theorem projected {n w : ℕ} (y : Fragment.Pin n w → Bool) (v : ℕ) :
    Fragment.siteRuns v (Fragment.list y) =
      ((List.finRange n).filter (fun i => Fragment.active y i && decide ((Fragment.parse y i).site=v))).map
        (fun i => (Fragment.parse y i).run) := by
  unfold Fragment.siteRuns Fragment.list
  induction List.finRange n with
  | nil => rfl
  | cons i l ih =>
    cases h : Fragment.active y i <;> by_cases hs : (Fragment.parse y i).site=v <;> simp [h,hs,ih]

variable (live : ∀ i, x (.inl (present i)) = true ↔ i ∈ Set.range edgeID)

include pre post oldFit newFit live in
/-- Filtering the actual enabled rows at one named site gives precisely its positive-width
old cable intervals in any duplicate-free enumeration of that site's true incident cables. -/
theorem sewn_siteRuns (v : L.Site) (wires : List (Incident L v)) (nodup : wires.Nodup)
    (all : ∀ z, z ∈ wires) :
    (Fragment.siteRuns (F.sites (siteID v)).val (Fragment.list ((sewnFrame F p name present).eval x))).Perm
      ((wires.filter (fun z => decide (0<L.width z.val))).map (interval v)) := by
  let y := (sewnFrame F p name present).eval x
  let owner := (F.sites (siteID v)).val
  let key (z : Incident L v) := ordinal (edgeID z.val,decide (L.src z.val=v))
  let on := (List.finRange (2*m)).filter (fun i => Fragment.active y i && decide ((Fragment.parse y i).site=owner))
  let pos := wires.filter fun z => decide (0<L.width z.val)
  have unique : Function.Injective key := fun a b h => Subtype.ext (edgeID.injective (congrArg Prod.fst (ordinal.injective h)))
  have enabled := active_range L edgeID F (FieldExport.fields F p name) Sum.inl present (retainedRow m p.slots)
    siteID portID x pre live
  have parse := sewn_parse L siteID edgeID portID F p name present hp lane hosts x pre post oldFit newFit
  have mem (i) : i ∈ on ↔ i ∈ pos.map key := by
    simp only [on,List.mem_filter,List.mem_finRange,true_and,Bool.and_eq_true,decide_eq_true_eq,List.mem_map,pos]
    constructor
    · rintro ⟨h,here⟩
      obtain ⟨⟨u,⟨z,hz⟩⟩,rfl⟩ := (enabled i).mp h
      have pz := parse u z
      have he : (F.sites (siteID u)).val = owner := (congrArg Fragment.Parsed.site pz).symm.trans here
      have eq : u=v := siteID.injective (F.sites.injective (Fin.ext he))
      subst u
      exact ⟨z,⟨all z,hz⟩,rfl⟩
    · rintro ⟨z,⟨_,hz⟩,rfl⟩
      exact ⟨(enabled (key z)).mpr ⟨⟨v,⟨z,hz⟩⟩,rfl⟩,congrArg Fragment.Parsed.site (parse v z)⟩
  have eq := (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) ((nodup.filter _).map unique)).mpr mem
  rw [projected]
  change (on.map (fun i => (Fragment.parse y i).run)).Perm (pos.map (interval v))
  have out := eq.map fun i => (Fragment.parse y i).run
  rw [List.map_map] at out
  exact out.trans (List.Perm.of_eq (List.map_congr_left fun z _ => congrArg Fragment.Parsed.run (parse v z)))

end Packing.SewnField.WireFragments

end BorderVNP
end Computability
end OAI
