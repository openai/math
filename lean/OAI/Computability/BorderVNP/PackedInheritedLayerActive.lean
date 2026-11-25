import OAI.Computability.BorderVNP.PackedInheritedLayerInputs
import OAI.Computability.BorderVNP.PackedInheritedEndpointViews
import OAI.Computability.BorderVNP.PackedInheritedLayerFilter

/-! # Exact enable and owner bits of inherited sparse rows

The physical flags exclude unoccupied edges and ports. A present loop uses only its
source column. For every retained site the remaining columns with its pointer key
are exactly its incident cable bands and attached external ports.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Layer

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open CellAddressCircuit CellAddressPhysical ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m s old np seeds C C' d d' k k' w : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {σ : Type*} [Fintype σ]
variable (oldF : CellAddressCircuit.Fields s old np C d k w σ)
variable (newF : CellAddressCircuit.Fields (siteCapacity e s seeds) (edgeCapacity e old seeds) np C' d' k' w σ)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))
variable (work extent : Fin s → Fin w → σ)
variable (occupied : Fin old → σ) (portUsed : Fin np → Bool) (successor : Fin (edgeCapacity e old seeds) → σ)
local notation3 "src" => inputs e oldF newF cut work extent occupied portUsed successor

variable {x : σ → Bool}

/-- Boolean predicate applied to the actual enable wire and owner word of a rectangular slot. -/
noncomputable def selectedAt (key : ℕ) (r : Row old D np) : Bool :=
  (src).eval x (r,.inl ()) && decide (value (fun j => (src).eval x (r,.inr (.inl j))) = key)

private theorem owner (r : Row old D np) :
    value (fun j => (src).eval x (r,.inr (.inl j))) = value (x ∘ oldF.ptr (endpoint r)) := by
  simp only [inputs,Frame.subst_eval,source_owner,tableFields,table,Frame.withInput_eval_inl,Function.comp_def]

private theorem edge_live (i : Fin old) (b : Band D) (side : Bool) :
    (src).eval x (.inl ((i,b),side),.inl ()) = true ↔ x (occupied i) = true ∧
      (side = true ∨ value (x ∘ oldF.ptr (.inl (.inl i))) ≠ value (x ∘ oldF.ptr (.inl (.inr i)))) := by
  simp only [inputs,Frame.subst_eval,source_live,tableFields,table,Frame.withInput_eval_inl,Function.comp_def]

private theorem port_live (i : Fin np) : (src).eval x (.inr i,.inl ()) = portUsed i := by
  simp only [inputs,Frame.subst_eval,source_port_live,tableFields]

variable {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
variable (siteID : p.layout.Site ↪ Fin s) (oldID : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np)
variable (data : Views.EndpointData p.layout oldF siteID oldID portID x)
variable (used : ∀ i, x (occupied i) = true ↔ i ∈ Set.range oldID)
variable (ports : ∀ i, portUsed i = true ↔ i ∈ Set.range portID)

omit [Fintype P] in
include data used ports in
/-- A physical source is enabled for a retained site exactly when it is one of that
site's canonical names. The criterion handles all inactive holes and both ends of loops. -/
theorem selectedAt_iff (v : p.layout.Site) (r : Row old D np) :
    selectedAt e oldF newF cut work extent occupied portUsed successor (x:=x) (oldF.sites (siteID v)).val r = true ↔
      ∃ a, name p oldID portID v a = r := by
  simp only [selectedAt,Bool.and_eq_true,decide_eq_true_eq,owner]
  have eqSite (a b : p.layout.Site) :
      (oldF.sites (siteID a)).val = (oldF.sites (siteID b)).val ↔ a=b := by
    simp only [Fin.val_inj,oldF.sites.injective.eq_iff,siteID.injective.eq_iff]
  rcases r with ⟨⟨i,b⟩,side⟩ | i
  · rw [edge_live]
    constructor
    · rintro ⟨⟨alive,nonloop⟩,key⟩
      obtain ⟨z,rfl⟩ := (used _).mp alive
      rw [data.src,data.dst] at nonloop
      cases side
      · have hd := (eqSite _ _).mp ((data.dst z).symm.trans key)
        have hs : p.layout.src z ≠ v := by
          intro h; rcases nonloop with bad | diff
          · cases bad
          · exact diff ((eqSite _ _).mpr (h.trans hd.symm))
        refine ⟨.inl (⟨z,.inr hd⟩,b),?_⟩
        change Sum.inl ((oldID z,b),decide (p.layout.src z = v)) = _
        rw [decide_eq_false hs]
      · have hs := (eqSite _ _).mp ((data.src z).symm.trans key)
        refine ⟨.inl (⟨z,.inl hs⟩,b),?_⟩
        change Sum.inl ((oldID z,b),decide (p.layout.src z = v)) = _
        rw [decide_eq_true hs]
    · rintro ⟨⟨z,b'⟩ | u,eqn⟩
      · change Sum.inl ((oldID z.val,b'),decide (p.layout.src z.val = v)) = Sum.inl ((i,b),side) at eqn
        obtain ⟨⟨rfl,rfl⟩,rfl⟩ := Prod.mk.inj (Sum.inl.inj eqn)
        have alive := (used _).mpr ⟨z.val,rfl⟩
        by_cases hs : p.layout.src z.val = v
        · exact ⟨⟨alive,.inl (decide_eq_true hs)⟩,by simpa [endpoint,edgeEnd,hs] using data.src z.val⟩
        · have hd := z.property.resolve_left hs
          have hn : value (x ∘ oldF.ptr (.inl (.inl (oldID z.val)))) ≠
              value (x ∘ oldF.ptr (.inl (.inr (oldID z.val)))) := by
            rw [data.src,data.dst]; exact fun h => hs (((eqSite _ _).mp h).trans hd)
          exact ⟨⟨alive,.inr hn⟩,by simpa [endpoint,edgeEnd,hs,hd] using data.dst z.val⟩
      · cases eqn
  · rw [port_live]
    constructor
    · rintro ⟨alive,key⟩
      obtain ⟨a,rfl⟩ := (ports _).mp alive
      have h := (eqSite _ _).mp ((data.attach a).symm.trans key)
      exact ⟨.inr ⟨a,h⟩,rfl⟩
    · rintro ⟨⟨z,b'⟩ | u,eqn⟩
      · cases eqn
      · change Sum.inr (portID u.val) = Sum.inr i at eqn
        obtain rfl := Sum.inr.inj eqn
        exact ⟨(ports _).mpr ⟨u.val,rfl⟩,by simpa [endpoint,u.property] using data.attach u.val⟩

include data used ports in
/-- Stable filtering of the actual circuit's flags and pointer keys returns the exact
local ordered rectangle names, with each eligible slot once. -/
theorem selectedAt_names (v : p.layout.Site) :
    let keep := selectedAt e oldF newF cut work extent occupied portUsed successor (x:=x) (oldF.sites (siteID v)).val
    ((List.finRange (Fintype.card (Row old D np))).filter (fun i => keep (order.symm i))).map order.symm =
      List.ofFn (fun i => name p oldID portID v (index p oldID portID v i)) :=
  filtered_names p oldID portID v _ (selectedAt_iff e oldF newF cut work extent occupied portUsed successor
    p siteID oldID portID data used ports v)

end Packing.Inherited.Layer

end BorderVNP
end Computability
end OAI
