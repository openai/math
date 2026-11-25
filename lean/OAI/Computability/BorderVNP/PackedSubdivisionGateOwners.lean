import OAI.Computability.BorderVNP.PackedSubdivisionGateOrder
import OAI.Computability.BorderVNP.PackedSubdivisionGatePhysical

/-! # Stable physical source names at every original and inserted subdivision site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision.Gates

open Crossing Shortening Shortening.PublicCapacity ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D np extra C C' d d' k k' w : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} {s : Shape} {σ : Type*} [Fintype σ]
variable (old : Rows s N) (route : N.WireRoutes) (fit : ∀ e, route.interior e ≤ extra)
variable (portID : P ↪ Fin np)
variable (oldF : CellAddressCircuit.Fields s.sites s.edges np C d k w σ)
variable (newF : CellAddressCircuit.Fields (s.sites+extra*s.edges) ((extra+1)*s.edges) np C' d' k' w σ)
variable (work extent : Fin s.sites → Fin w → σ) (present : Fin ((extra+1)*s.edges) → σ)
local notation3 "G" => N.subdivide route
local notation3 "rows" => old.subdivide route extra fit
variable {x : σ → Bool} (oldData : Views.EndpointData N oldF old.site old.edge portID x)
variable (newData : Views.EndpointData (N.subdivide route) newF (old.subdivide route extra fit).site (old.subdivide route extra fit).edge portID x)
variable (live : ∀ i, x (present i) = true ↔ i ∈ Set.range (old.subdivide route extra fit).edge)
variable (shape : ∀ e, route.interior e = 0 ∨ route.interior e = extra)
local notation3 "ins" => inputs oldF newF work extent present

/-- Fixed rectangle name of an actual interior hop equality. -/
def nameRelay (j : (e : N.Edge) × Fin (route.interior e)) : Row s.edges np extra :=
  .inr (old.edge j.1,j.2.castLE (fit j.1))

/-- The true rows installed at a given site after one physical subdivision. -/
def Candidate : (G).Site → Row s.edges np extra → Prop
  | .inl v,t => ∃ r : Placement.Row N v, 0 < Placement.width N v r ∧ .inl (nameOld old portID v r) = t
  | .inr j,t => t = nameRelay (np:=np) old route fit j

/-- Physical owner test applied to the same public enable and destination-pointer pins as the emitter. -/
noncomputable def selectedAt (siteKey : ℕ) (r : Row s.edges np extra) : Bool :=
  (ins).eval x (r,.inl ()) && decide (value (fun j => (ins).eval x (r,.inr (.inl j))) = siteKey)

include oldData live in
/-- Every enabled source names an actual command at an actual site of the chosen
subdivision, and every such command is enabled. -/
theorem active_iff (t : Row s.edges np extra) :
    (ins).eval x (t,.inl ()) = true ↔ ∃ v, Candidate old route fit portID v t := by
  rcases t with a | ⟨i,j⟩
  · rw [old_enabled_iff old portID oldF newF work extent present oldData]
    constructor
    · rintro ⟨v,r,hw,h⟩
      exact ⟨.inl v,r,hw,congrArg Sum.inl h⟩
    · rintro ⟨v | j,h⟩
      · obtain ⟨r,hw,he⟩ := h
        exact ⟨v,r,hw,Sum.inl.inj he⟩
      · cases h
  · rw [relay_enabled_iff old oldF newF work extent present route fit live]
    constructor
    · rintro ⟨e,rfl,hi⟩
      exact ⟨.inr ⟨e,⟨j.val,hi⟩⟩,rfl⟩
    · rintro ⟨v | u,h⟩
      · obtain ⟨_,_,he⟩ := h
        cases he
      · obtain ⟨e,ui⟩ := u
        change Sum.inr (i,j) = Sum.inr (old.edge e,ui.castLE (fit e)) at h
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Sum.inr.inj h)
        exact ⟨e,rfl,ui.isLt⟩

omit [Fintype P] in
include newData live shape in
/-- Every eligible command carries its unique actual successor site's sparse code. -/
theorem candidate_owner (v : (G).Site) (t : Row s.edges np extra) (h : Candidate old route fit portID v t) :
    value (fun j => (ins).eval x (t,.inr (.inl j))) = (newF.sites ((rows).site v)).val := by
  simp only [inputs,Frame.subst_eval,source_owner]
  cases v with
  | inl a =>
    obtain ⟨r,_,rfl⟩ := h
    exact old_owner old route fit portID oldF newF work extent present newData live shape a r
  | inr j =>
    change t = nameRelay (np:=np) old route fit j at h
    rw [h]
    exact relay_owner old route fit portID oldF newF work extent present newData j

include oldData newData live shape in
/-- The enable bit and actual owner word select exactly the named commands at a site. -/
theorem selectedAt_iff (v : (G).Site) (t : Row s.edges np extra) :
    selectedAt oldF newF work extent present (x:=x) (newF.sites ((rows).site v)).val t = true ↔
      Candidate old route fit portID v t := by
  simp only [selectedAt,Bool.and_eq_true,decide_eq_true_eq]
  have gate := active_iff old route fit portID oldF newF work extent present oldData live t
  have own := candidate_owner old route fit portID oldF newF work extent present newData live shape
  constructor
  · rintro ⟨alive,key⟩
    obtain ⟨v',hc⟩ := gate.mp alive
    obtain rfl := (rows).site.injective (newF.sites.injective (Fin.ext ((own v' t hc).symm.trans key)))
    exact hc
  · intro hc
    exact ⟨gate.mpr ⟨v,hc⟩,own v t hc⟩

include oldData newData live shape in
/-- Stable filtering for each retained original site gives exactly its positive-width
endpoint and port copy rows, in its own canonical original table order. -/
theorem selectedAt_oldRows (v : N.Site) :
    selected (selectedAt oldF newF work extent present (x:=x) (newF.sites ((rows).site (.inl v))).val) =
      (oldRows old portID v).map (fun r => .inl (nameOld old portID v r)) :=
  selected_old old portID v _ (selectedAt_iff old route fit portID oldF newF work extent present
    oldData newData live shape (.inl v))

include oldData newData live shape in
/-- A relay receives exactly its own one physical command, even when the original
edge has zero width. -/
theorem selectedAt_relayRows (j : (e : N.Edge) × Fin (route.interior e)) :
    selected (selectedAt oldF newF work extent present (x:=x) (newF.sites ((rows).site (.inr j))).val) =
      [nameRelay old route fit j] :=
  selected_relay _ _ (selectedAt_iff old route fit portID oldF newF work extent present
    oldData newData live shape (.inr j))

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
