import OAI.Computability.BorderVNP.PackedSubdivisionGateFrozen
import OAI.Computability.BorderVNP.PackedFrozenNineWords
import OAI.Computability.BorderVNP.PackedFrozenTapeRekey

/-! # Exact immutable record block for physical cable subdivision -/

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

open FrozenTape

/-- Public scalar and row order of the complete subdivision rectangle. -/
def tapeSchema (m np extra w : ℕ) :
    Schema (Row m np extra) (Row m np extra × Fin 9 × Fin w) :=
  NineWords.schema ((List.finRange ((m*2+np)+m*extra)).map ordinal.symm) w

/-- The actual fixed circuit wired into a frozen tape for this stage. -/
noncomputable def tapeFrame :
    Frame σ (FrozenTape.Pins (Row s.edges np extra) (Row s.edges np extra × Fin 9 × Fin w) d') :=
  NineWords.adapt (frozen oldF newF work extent present)

/-- Relocation adds no gates to the original fixed nine-field emitter. -/
theorem tapeFrame_size : (tapeFrame oldF newF work extent present).size =
    (frozen oldF newF work extent present).size := NineWords.adapt_size _

/-- Intrinsic commands contributed by this stage, excluding the stored earlier layers. -/
noncomputable def addedRecords : (G).Site → List CellSparse.Record
  | .inl v => (cuts N route v old.edge (rows).edge portID).map (Slice.record (prior v))
  | .inr j => [relayRecord N route (rows).edge portID j]

include oldData newData oldFit newFit live shape hw he in
/-- The emitted subdivision block owns no spurious rows, and each site's frozen
record list is exactly the list actually installed at that site by the subdivided
private programs, including empty original lists and the single record at each relay. -/
theorem tapeBlock (size : ∀ v, (prior v).incoming = incoming N v)
    (room : ∀ v, (prior v).size + incoming G (.inl v) < 2^w) (one : 1 < 2^w) :
    (tapeSchema s.edges np extra w).Block ((tapeFrame oldF newF work extent present).eval x)
      (fun v => (newF.sites ((rows).site v)).val)
      (fun v => (addedRecords old route fit portID prior v).map marked) := by
  let f := frozen oldF newF work extent present
  constructor
  · intro t _ alive
    simp only [tapeFrame,NineWords.adapt,Frame.select_eval,NineWords.pin,frozen_enable] at alive
    obtain ⟨v,cv⟩ := (active_iff old route fit portID oldF newF work extent present oldData live t).mp alive
    refine ⟨v,?_⟩
    simp only [FrozenTape.owner,tapeFrame,NineWords.adapt,Frame.select_eval,NineWords.pin,frozen_owner]
    exact candidate_owner old route fit portID oldF newF work extent present newData live shape v t cv
  · intro v
    rw [tapeSchema,tapeFrame,NineWords.atSite,List.filter_map]
    change atSite f x (newF.sites ((rows).site v)).val = _
    cases v with
    | inl a =>
      simp only [addedRecords,List.map_map,Function.comp_def]
      exact frozen_old old route fit portID oldF newF work extent present prior oldData newData oldFit newFit
        live shape hw he a (size a) (room a) one
    | inr j =>
      exact frozen_relay old route fit portID oldF newF work extent present oldData newData newFit live shape j one

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
