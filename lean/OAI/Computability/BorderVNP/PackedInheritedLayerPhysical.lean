import OAI.Computability.BorderVNP.PackedInheritedLayerEndpoints
import OAI.Computability.BorderVNP.PackedInheritedLayerEmit

/-! # Reading a retained site's actual clipped command from the two public directories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Layer

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open CellAddressCircuit CellAddressPhysical ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m s old np seeds C C' d d' k k' w : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {σ : Type*} [Fintype σ]
variable (oldF : CellAddressCircuit.Fields s old np C d k w σ)
variable (newF : CellAddressCircuit.Fields (siteCapacity e s seeds) (edgeCapacity e old seeds) np C' d' k' w σ)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))
variable (work extent : Fin s → Fin w → σ)
variable (occupied : Fin old → σ) (portUsed : Fin np → Bool) (successor : Fin (edgeCapacity e old seeds) → σ)
variable {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
variable {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
variable (binName : A → ℕ) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
variable (siteID : p.layout.Site ↪ Fin s) (oldID : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np) (seed : A ↪ Fin seeds)
local notation3 "G" => (output e p bin perm positive first q).layout
local notation3 "nextSite" => siteRows e p siteID seed
local notation3 "nextID" => outputRows e p bin perm positive first q oldID seed
local notation3 "src" => inputs e oldF newF cut work extent occupied portUsed successor
local notation3 "F" => tableFields e oldF occupied portUsed successor
variable {x : σ → Bool} (oldData : Views.EndpointData p.layout oldF siteID oldID portID x)
variable (newData : Views.EndpointData (output e p bin perm positive first q).layout newF
  (siteRows e p siteID seed) (outputRows e p bin perm positive first q oldID seed) portID x)
variable (oldFits : ∀ v, incoming p.layout v < 2^w) (newFits : ∀ v, incoming (output e p bin perm positive first q).layout v < 2^w)
variable (states : p.layout.Site → Site)
variable (workRead : ∀ v, value (x ∘ work (siteID v)) = (states v).work)
variable (extentRead : ∀ v, value (x ∘ extent (siteID v)) = (states v).size)
variable (cuts : ∀ z b a, value (fun j => cut.eval x ((oldID z,b),a,j)) =
  a.read (priorDescriptor (m := m) p bin perm binName z b))
variable (success : ∀ i, x (successor i) = true ↔ i ∈ Set.range (outputRows e p bin perm positive first q oldID seed))

local notation3 "st" => (table e oldF newF cut work extent).eval x

omit [NeZero D] [Field K] [Fintype P] [Fintype σ] in
include oldData in
/-- The source-first name of a real local interval points to its actual owner. -/
theorem named_pointer (v : p.layout.Site) (r : LayerRow p v) :
    value (x ∘ oldF.ptr (endpoint (name p oldID portID v r))) = (oldF.sites (siteID v)).val := by
  rcases r with ⟨z,b⟩ | u
  · change value (x ∘ oldF.ptr (edgeEnd (oldID z.val) (decide (p.layout.src z.val = v)))) = _
    by_cases h : p.layout.src z.val = v
    · simpa [edgeEnd,h] using oldData.src z.val
    · have hd := z.property.resolve_left h
      simpa [edgeEnd,h,hd] using oldData.dst z.val
  · change value (x ∘ oldF.ptr (.inr (portID u.val))) = _
    simpa only [u.property] using oldData.attach u.val

/-- Numeric values emitted at a fixed rectangle slot by the assembled sparse reader. -/
noncomputable def readArgs (r : Row old D np) (a : Arg) := value (fun j => (src).eval x (r,.inr (.inr (a,j))))

omit [NeZero D] in
private theorem readArgs_eq (r : Row old D np) (a : Arg) :
    readArgs e oldF newF cut work extent occupied portUsed successor (x := x) r a = argValue e F st r a := by
  simp only [readArgs,inputs,Frame.subst_eval,source_value]

local notation3 "args" => readArgs e oldF newF cut work extent occupied portUsed successor (x := x)
local notation3 "sl" => layerSlice e p bin perm binName positive first q

omit [NeZero D] [Fintype P] in
include oldData workRead extentRead in
private theorem site_prefixes (v : p.layout.Site) (r : LayerRow p v) :
    args (name p oldID portID v r) .work = (states v).work ∧
    args (name p oldID portID v r) .extent = (states v).size := by
  let u := endpoint (name p oldID portID v r)
  have hu := named_pointer oldF p siteID oldID portID oldData v r
  have hw := prefix_value oldF work x (siteID v) u hu
  have ht := prefix_value oldF extent x (siteID v) u hu
  simp only [readArgs_eq,argValue,tableFields,Function.comp_def,table,Frame.withInput_eval_inr,parallelFrame_eval_inr,
    parallelFrame_eval_inl]
  exact ⟨hw.trans (workRead v),ht.trans (extentRead v)⟩

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
include oldData newData oldFits newFits cuts success in
private theorem slice_args (v : p.layout.Site) (r : LayerRow p v) :
    let nr := name p oldID portID v r
    let slice := sl v oldID nextID portID r
    args nr .oldBase + args nr .clip = slice.oldStart ∧
      args nr .newBase = slice.newStart ∧ args nr .width = slice.width := by
  intro nr slice
  rcases r with ⟨z,b⟩ | u
  · let side := decide (p.layout.src z.val = v)
    let new := oldBandWire e p bin perm positive first q v z b
    let desc := priorDescriptor (m := m) p bin perm binName z.val b
    let sel := (z.val,b) ∈ (partition p.layout bin perm m).selected
    have hs : x (successor (bandCandidate e seeds 0 (oldID z.val) b)) = true ↔ sel :=
      (success _).trans (candidate_zero e p bin perm positive first q oldID seed z.val b)
    let address : End (edgeCapacity e old seeds) np :=
      if sel then edgeEnd (bandCandidate e seeds (if side then 0 else 1) (oldID z.val) b) true
      else edgeEnd (bandCandidate e seeds 2 (oldID z.val) b) side
    have addr : address = edgeEnd (nextID new.val) (decide ((G).src new.val = .inl v)) :=
      chosen_end e p bin perm positive first q oldID seed v z b
    have hn : value (fun j => (Views.frame newF).eval x (.inl address,j)) = wireStart G nextID portID (.inl v) new := by
      rw [addr]
      exact Views.incident_value G newF nextSite nextID portID newData newFits (.inl v) new
    have ho := Views.incident_value p.layout oldF siteID oldID portID oldData oldFits v z
    have hc : value (fun j => cut.eval x ((oldID z.val,b),.start,j)) = desc.localStart := cuts z.val b .start
    have hw : value (fun j => cut.eval x ((oldID z.val,b),.span,j)) = desc.span := cuts z.val b .span
    simp only [nr,slice,layerSlice,readArgs_eq,name,Function.Embedding.coeFn_mk,argValue,endpoint,tableFields,
      table,Function.comp_def,Frame.withInput_eval_inr,Frame.withInput_eval_inl,parallelFrame_eval_inr,parallelFrame_eval_inl,
      Sum.elim_inl,hs]
    refine ⟨congrArg₂ (· + ·) ho hc,?_,hw⟩
    by_cases hsel : sel <;> simpa only [address,hsel,ite_true,ite_false,side,new] using hn
  · have ho := Views.attached_value p.layout oldF siteID oldID portID oldData oldFits v u
    have hn := Views.attached_value G newF nextSite nextID portID newData newFits (.inl v)
      (portOfOld e p bin perm positive first q v u)
    simp only [nr,slice,layerSlice,readArgs_eq,name,Function.Embedding.coeFn_mk,argValue,endpoint,tableFields,
      table,Function.comp_def,Frame.withInput_eval_inr,Frame.withInput_eval_inl,parallelFrame_eval_inr,parallelFrame_eval_inl,
      Sum.elim_inr,Nat.add_zero]
    exact ⟨ho,hn,oldData.port u.val⟩

include oldData newData oldFits newFits workRead extentRead cuts success in
/-- The emitted command is precisely the site's genuine retained clipped record, in
its immutable local coordinates. -/
theorem input_command (v : p.layout.Site) (r : LayerRow p v) :
    command (args (name p oldID portID v r)) =
    (sl v oldID nextID portID r).record (states v) := by
  have hh := site_prefixes e oldF newF cut work extent occupied portUsed successor p siteID oldID portID oldData states
    workRead extentRead v r
  have hv := slice_args e oldF newF cut work extent occupied portUsed successor p bin perm binName positive first q
    siteID oldID portID seed oldData newData oldFits newFits cuts success v r
  dsimp only at hv
  simp only [command,Slice.record,hh.1,hh.2,hv.1,hv.2.1,hv.2.2]

end Packing.Inherited.Layer

end BorderVNP
end Computability
end OAI
