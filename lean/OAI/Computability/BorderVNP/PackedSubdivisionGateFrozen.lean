import OAI.Computability.BorderVNP.PackedSubdivisionGateOwners
import OAI.Computability.BorderVNP.PackedInheritedLayerFreeze

/-! # Actual nine-field stable sections of the fixed subdivision row emitter -/

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

/-- The fixed emitted Boolean program is chosen before any network instance,
routing data, or private state. -/
noncomputable def frozen : Frame σ (Row s.edges np extra × Layer.Output d' w) :=
  Classical.choose (emit_subdivision oldF newF work extent present)

/-- Gate charge of the frozen subdivision packet source. -/
theorem frozen_size : (frozen oldF newF work extent present).size ≤
    (inputs oldF newF work extent present).size+1+Fintype.card (Row s.edges np extra)*(4500*(w+1)^2) :=
  (Classical.choose_spec (emit_subdivision oldF newF work extent present)).1

local notation3 "out" => frozen oldF newF work extent present

/-- The actual stored candidate flag is the same gate used to eliminate duplicate loops and holes. -/
theorem frozen_enable (t : Row s.edges np extra) : (out).eval x (t,.inl ()) =
    (inputs oldF newF work extent present).eval x (t,.inl ()) :=
  (Classical.choose_spec (emit_subdivision oldF newF work extent present)).2.1 x t

/-- The complete owner word returned by the emitted program is the true successor-site pointer. -/
theorem frozen_owner (t : Row s.edges np extra) (j : Fin d') : (out).eval x (t,.inr (.inl j)) =
    (inputs oldF newF work extent present).eval x (t,.inr (.inl j)) :=
  (Classical.choose_spec (emit_subdivision oldF newF work extent present)).2.2.1 x t j

/-- The nine physical scalar fields and their relocation roles, in native packet order. -/
noncomputable def markedFields (f : Frame σ (Row s.edges np extra × Layer.Output d' w)) (x : σ → Bool)
    (r : Row s.edges np extra) :=
  List.ofFn (fun i => (Layer.kind i,value (fun j => f.eval x (r,.inr (.inr (i,j))))))

/-- Read the actual per-site section of complete commands from a frozen subdivision frame. -/
noncomputable def atSite (f : Frame σ (Row s.edges np extra × Layer.Output d' w)) (x : σ → Bool) (key : ℕ) :=
  (selected (fun r => f.eval x (r,.inl ()) && decide (value (fun j => f.eval x (r,.inr (.inl j))) = key))).map
    (markedFields f x)

include oldData newData oldFit newFit live shape hw he in
/-- Stable extraction for a retained site yields its actual endpoint-copy block, with
the original program's work prefix and the successor's site-local addresses. -/
theorem frozen_old (v : N.Site) (size : (prior v).incoming = incoming N v)
    (room : (prior v).size + incoming G (.inl v) < 2^w) (one : 1 < 2^w) :
    atSite (out) x (newF.sites ((rows).site (.inl v))).val =
      (cuts N route v old.edge (rows).edge portID).map (fun z => marked (z.record (prior v))) := by
  simp only [atSite,frozen_enable,frozen_owner]
  change (selected (selectedAt oldF newF work extent present (x:=x) _)).map _ = _
  rw [selectedAt_oldRows old route fit portID oldF newF work extent present oldData newData live shape]
  simp only [oldRows,cuts,List.map_map]
  apply List.map_congr_left
  intro r _
  have fit' := old_room old route fit portID oldF newF work extent present prior oldData newData oldFit newFit
    live shape hw he v r size room
  have h := (Classical.choose_spec (emit_subdivision oldF newF work extent present)).2.2.2 x
    (.inl (nameOld old portID v r)) one fit'.1 fit'.2
  have eqn := old_command old route fit portID oldF newF work extent present prior oldData newData oldFit newFit
    live shape hw he v r
  exact h.trans (congrArg marked eqn)

include oldData newData newFit live shape in
/-- A genuine inserted relay yields its single intrinsic predecessor/successor equality,
including its two concrete wire addresses, for the stored scalar rectangle. -/
theorem frozen_relay (j : (e : N.Edge) × Fin (route.interior e)) (one : 1 < 2^w) :
    atSite (out) x (newF.sites ((rows).site (.inr j))).val =
      [marked (relayRecord N route (rows).edge portID j)] := by
  simp only [atSite,frozen_enable,frozen_owner]
  change (selected (selectedAt oldF newF work extent present (x:=x) _)).map _ = _
  rw [selectedAt_relayRows old route fit portID oldF newF work extent present oldData newData live shape]
  simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true]
  have fit' := relay_room old route fit portID oldF newF work extent present oldData newData newFit j
  have h := (Classical.choose_spec (emit_subdivision oldF newF work extent present)).2.2.2 x
    (nameRelay old route fit j) one fit'.1 fit'.2
  exact h.trans (congrArg marked (relay_command old route fit portID oldF newF work extent present
    oldData newData newFit j))

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
