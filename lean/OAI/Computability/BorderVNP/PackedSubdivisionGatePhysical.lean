import OAI.Computability.BorderVNP.PackedSubdivisionGateActive

/-! # Actual ownership and nine physical scalar fields of each live subdivision command -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision.Gates

open Crossing Shortening Shortening.PublicCapacity ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical
open private limits from OAI.Computability.BorderVNP.PackedSubdivisionSlices

variable {D np extra C C' d d' k k' w : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} {s : Shape} {σ : Type*} [Fintype σ]
variable (old : Rows s N) (route : N.WireRoutes) (fit : ∀ e, route.interior e ≤ extra)
variable (portID : P ↪ Fin np)
variable (oldF : CellAddressCircuit.Fields s.sites s.edges np C d k w σ)
variable (newF : CellAddressCircuit.Fields (s.sites+extra*s.edges) ((extra+1)*s.edges) np C' d' k' w σ)
variable (work extent : Fin s.sites → Fin w → σ) (present : Fin ((extra+1)*s.edges) → σ)
local notation3 "G" => N.subdivide route
local notation3 "rows" => old.subdivide route extra fit
variable {x : σ → Bool}
local notation3 "st" => (table oldF newF work extent).eval x
local notation3 "F" => tableFields oldF newF present
variable (prior : N.Site → Site)
variable (oldData : Views.EndpointData N oldF old.site old.edge portID x)
variable (newData : Views.EndpointData (N.subdivide route) newF (old.subdivide route extra fit).site
  (old.subdivide route extra fit).edge portID x)
variable (oldFit : ∀ v, incoming N v < 2^w) (newFit : ∀ v, incoming (N.subdivide route) v < 2^w)
variable (live : ∀ i, x (present i) = true ↔ i ∈ Set.range (old.subdivide route extra fit).edge)
variable (shape : ∀ e, route.interior e = 0 ∨ route.interior e = extra)
variable (hw : ∀ v, value (x ∘ work (old.site v)) = (prior v).work)
variable (he : ∀ v, value (x ∘ extent (old.site v)) = (prior v).size)

omit [Fintype σ] in
private theorem ptr {S M n V a t u : ℕ} {T : Type*} {pbits : T → ℕ} (A : Network D T pbits)
    (f : CellAddressCircuit.Fields S M n V a t u σ) (sites : A.Site ↪ Fin S) (edges : A.Edge ↪ Fin M)
    (ports : T ↪ Fin n) (data : Views.EndpointData A f sites edges ports x) (v : A.Site) (z : Incident A v) :
    value (x ∘ f.ptr (Layer.edgeEnd (edges z.val) (decide (A.src z.val=v)))) = (f.sites (sites v)).val := by
  by_cases hs : A.src z.val=v
  · simpa [Layer.edgeEnd,hs] using data.src z.val
  · simpa [Layer.edgeEnd,hs,z.property.resolve_left hs] using data.dst z.val

omit [Fintype P] in
include live shape in
private theorem target (v : N.Site) (e : Incident N v) :
    oldTarget (nameOld old portID v (.inl e)) (long F st (nameOld old portID v (.inl e))) =
      Layer.edgeEnd ((rows).edge (endpoint N route v e).val) (decide ((G).src (endpoint N route v e).val = .inl v)) := by
  apply old_target_eq old route fit v e _ (shape e.val)
  change st (.inl (present (hop (old.edge e.val) (Fin.last extra)))) = true ↔ _
  simpa only [table,Frame.withInput_eval_inl] using live (hop (old.edge e.val) (Fin.last extra))

omit [Fintype P] [Fintype σ] in
include oldData in
private theorem old_ptr (v : N.Site) (r : Placement.Row N v) :
    value (x ∘ oldF.ptr (oldEnd (nameOld old portID v r))) = (oldF.sites (old.site v)).val := by
  cases r with
  | inl e => exact ptr N oldF old.site old.edge portID oldData v e
  | inr p => exact (oldData.attach p.val).trans (congrArg (fun u => (oldF.sites (old.site u)).val) p.property)

private theorem oldViewRead (a : CellAddressCircuit.End s.edges np) :
    value (st ∘ (F).oldView a) = value (fun j => (Views.frame oldF).eval x (.inl a,j)) := by
  simp only [tableFields,table,Function.comp_def,Frame.withInput_eval_inr,parallelFrame_eval_inl]

private theorem newViewRead (a : CellAddressCircuit.End ((extra+1)*s.edges) np) :
    value (st ∘ (F).newView a) = value (fun j => (Views.frame newF).eval x (.inl a,j)) := by
  simp only [tableFields,table,Function.comp_def,Frame.withInput_eval_inr,parallelFrame_eval_inr,parallelFrame_eval_inl]

private theorem newPtrRead (a : CellAddressCircuit.End ((extra+1)*s.edges) np) :
    value (st ∘ (F).newPtr a) = value (x ∘ newF.ptr a) := by
  simp only [tableFields,table,Function.comp_def,Frame.withInput_eval_inl]

set_option maxHeartbeats 800000 in
omit [Fintype P] in
include oldData in
private theorem widthRead (v : N.Site) (r : Placement.Row N v) :
    value (st ∘ widthPins F (nameOld old portID v r)) = Placement.width N v r := by
  cases r with
  | inl e =>
    change value (st ∘ (F).edgeWidth (old.edge e.val)) = N.width e.val
    simpa only [tableFields,table,Frame.withInput_eval_inl,Function.comp_def] using oldData.edge e.val
  | inr p =>
    change value (st ∘ (F).portWidth (portID p.val)) = bits p.val
    simpa only [tableFields,table,Frame.withInput_eval_inl,Function.comp_def] using oldData.port p.val

set_option maxHeartbeats 1800000 in
include oldData newData oldFit newFit live shape hw he in
/-- The circuit's retained command is exactly the original site's sparse copy,
with the true work prefixes and chosen endpoint starts in its immutable local bank. -/
theorem old_command (v : N.Site) (r : Placement.Row N v) :
    Layer.command (values F st (.inl (nameOld old portID v r))) =
      (slice N route v old.edge (rows).edge portID r).record (prior v) := by
  let u := oldEnd (nameOld old portID v r)
  have addr := old_ptr old portID oldF oldData v r
  have workAt := (Layer.prefix_value oldF work x (old.site v) u addr).trans (hw v)
  have extentAt := (Layer.prefix_value oldF extent x (old.site v) u addr).trans (he v)
  have sizes : values F st (.inl (nameOld old portID v r)) .work = (prior v).work ∧
      values F st (.inl (nameOld old portID v r)) .extent = (prior v).size := by
    simpa only [values,tableFields,table,Function.comp_def,Frame.withInput_eval_inr,parallelFrame_eval_inr,
      parallelFrame_eval_inl,u] using And.intro workAt extentAt
  have oldAt : value (st ∘ (F).oldView (oldEnd (nameOld old portID v r))) =
      (slice N route v old.edge (rows).edge portID r).oldStart := by
    rw [oldViewRead]
    cases r with
    | inl e => exact Views.incident_value N oldF old.site old.edge portID oldData oldFit v e
    | inr p => exact Views.attached_value N oldF old.site old.edge portID oldData oldFit v p
  have newAt : value (st ∘ (F).newView (oldTarget (nameOld old portID v r) (long F st (nameOld old portID v r)))) =
      (slice N route v old.edge (rows).edge portID r).newStart := by
    rw [newViewRead]
    cases r with
    | inl e =>
      rw [target old route fit portID oldF newF work extent present live shape v e]
      exact Views.incident_value G newF (rows).site (rows).edge portID newData newFit (.inl v) (endpoint N route v e)
    | inr p => exact Views.attached_value G newF (rows).site (rows).edge portID newData newFit (.inl v) (attached N route v p)
  rw [Layer.command,sizes.1,sizes.2]
  simp only [values,add_zero,widthRead old portID oldF newF work extent present oldData,
    oldAt,newAt,Slice.record]
  rfl

set_option maxHeartbeats 800000 in
omit [Fintype P] in
include newData live shape in
/-- The owner of a retained command is the new directory code of its true retained site. -/
theorem old_owner (v : N.Site) (r : Placement.Row N v) :
    owner F st (.inl (nameOld old portID v r)) = (newF.sites ((rows).site (.inl v))).val := by
  change value (st ∘ (F).newPtr (oldTarget (nameOld old portID v r) (long F st (nameOld old portID v r)))) = _
  rw [newPtrRead]
  cases r with
  | inl z =>
    rw [target old route fit portID oldF newF work extent present live shape v z]
    exact ptr G newF (rows).site (rows).edge portID newData (.inl v) (endpoint N route v z)
  | inr p =>
    exact (newData.attach p.val).trans (congrArg (fun a => (newF.sites ((rows).site (.inl a))).val) p.property)

variable (j : (e : N.Edge) × Fin (route.interior e))
local notation3 "slot" => (Sum.inr (old.edge j.1,j.2.castLE (fit j.1)) : Row s.edges np extra)
omit [Fintype P] in
include newData in
/-- A relay is owned by the destination of its physical predecessor hop. -/
theorem relay_owner : owner F st slot = (newF.sites ((rows).site (.inr j))).val := by
  have ht := relay_left_eq (np := np) old route fit j
  simp only [owner,Sum.elim_inr,ht,tableFields,table,Function.comp_def,Frame.withInput_eval_inl]
  exact ptr G newF (rows).site (rows).edge portID newData (.inr j) (leftHop N route j)

include oldData newData newFit in
/-- Both strided port fields of the emitted relay row are the adjacent hop views.
Its one-copy program has no private prefix and no opaque factor. -/
theorem relay_command : Layer.command (values F st slot) = relayRecord N route (rows).edge portID j := by
  have hl := Views.incident_value G newF (rows).site (rows).edge portID newData newFit (.inr j) (leftHop N route j)
  have hr := Views.incident_value G newF (rows).site (rows).edge portID newData newFit (.inr j) (rightHop N route j)
  have wl : value (st ∘ (F).edgeWidth (old.edge j.1)) = N.width j.1 := by
    simpa only [tableFields,table,Function.comp_def,Frame.withInput_eval_inl] using oldData.edge j.1
  have left : value (st ∘ (F).newView (relayLeft (old.edge j.1) (j.2.castLE (fit j.1)))) =
      wireStart G (rows).edge portID (.inr j) (leftHop N route j) := by
    rw [newViewRead,relay_left_eq (np := np) old route fit j]; exact hl
  have right : value (st ∘ (F).newView (relayRight (old.edge j.1) (j.2.castLE (fit j.1)))) =
      wireStart G (rows).edge portID (.inr j) (rightHop N route j) := by
    rw [newViewRead,relay_right_eq (np := np) old route fit j]; exact hr
  simp only [Layer.command,values,add_zero,zero_add,wl,left,right]
  rfl

private def starts : CellSparse.Record → ℕ × ℕ
  | .equal _ _ l r => (l.base,r.base)
  | _ => (0,0)

include oldData newData oldFit newFit live shape hw he in
/-- Every encoded address at an original site fits its declared word as soon as
the whole installed slab does. No additional per-record range premise is needed. -/
theorem old_room (v : N.Site) (r : Placement.Row N v) (size : (prior v).incoming = incoming N v)
    (fits : (prior v).size + incoming G (.inl v) < 2^w) :
    let arg := values F st (.inl (nameOld old portID v r))
    arg .work+(arg .oldBase+arg .clip) < 2^w ∧ arg .extent+arg .newBase < 2^w := by
  intro arg
  have cmd := old_command old route fit portID oldF newF work extent present prior
    oldData newData oldFit newFit live shape hw he v r
  let sl := slice N route v old.edge (rows).edge portID r
  have bases : (arg .work+(arg .oldBase+arg .clip),arg .extent+arg .newBase) =
      ((prior v).work+sl.oldStart,(prior v).size+sl.newStart) := congrArg starts cmd
  have lim := limits N route v old.edge (rows).edge portID r
  have l : sl.oldStart ≤ (prior v).incoming := size.symm ▸ ((Nat.le_add_right ..).trans lim.1)
  have rr : sl.newStart ≤ incoming G (.inl v) := (Nat.le_add_right ..).trans lim.2
  exact ⟨(congrArg Prod.fst bases).trans_lt (((Nat.add_le_add_left l _).trans (Nat.le_add_right (prior v).size _)).trans_lt fits),
    (congrArg Prod.snd bases).trans_lt ((Nat.add_le_add_left rr _).trans_lt fits)⟩

include oldData newData newFit in
/-- At a relay both published addresses lie inside its actual incidence array. -/
theorem relay_room :
    let arg := values F st slot
    arg .work+(arg .oldBase+arg .clip) < 2^w ∧ arg .extent+arg .newBase < 2^w := by
  intro arg
  have cmd := relay_command old route fit portID oldF newF work extent present oldData newData newFit j
  have l := wireEnd_le G (rows).edge portID (.inr j) (leftHop N route j)
  have r := wireEnd_le G (rows).edge portID (.inr j) (rightHop N route j)
  have bases : (arg .work+(arg .oldBase+arg .clip),arg .extent+arg .newBase) =
      (wireStart G (rows).edge portID (.inr j) (leftHop N route j),
       wireStart G (rows).edge portID (.inr j) (rightHop N route j)) := congrArg starts cmd
  exact ⟨(congrArg Prod.fst bases).trans_lt (((Nat.le_add_right ..).trans l).trans_lt (newFit _)),
    (congrArg Prod.snd bases).trans_lt (((Nat.le_add_right ..).trans r).trans_lt (newFit _))⟩

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
