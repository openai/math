import OAI.Computability.BorderVNP.DiagonalSignedPinnedHost

/-! # Simultaneous signed host tables on the original owners -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open VPVNP BurstRAM Crossing Packing Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical
open Packing.RoutingOutputs BorderVNP.Cube Cube.Physical Cube.NativeIntervals Cube.HostScatter
open RoutingISA RoutingISA.Evaluator FiniteEvaluator ParseBatchSort PackedHistoryCircuit
open scoped Classical
set_option maxHeartbeats 1000000

variable {D R sz n d k b w geo base gap A : ℕ} {P σ : Type} [Fintype P] [Fintype σ]
    {bits : P → ℕ} (task : SignedTaskArena.Layout) (dir : Directory.Layout)

variable (N : Network D P bits) (cell : N.Site → Fin task.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin sz) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin n)
    (F : Fields sz task.cube.cables n task.cube.cells d k b σ) {old : Fin dir.entries → Fin sz} {ports : Fin A → Fin n}
    (pub : Fin (R+1) → Arg → Word w) (profile mid out : Fin (R+1) → Memory w)
    (pp lp : Fin (R+1) → ℕ → ℕ × ℕ) (x : Fin (R+1) → σ → Bool)
    (B : Fin (R+1) → BroadcastFrame) {pin : Fin (R+1) → Pins.Layout}
    (fields : ∀ u, Pins.ProcessorFields (pin u)) {guess : Fin (R+1) → ℕ → Bool}
    {controls : Fin (R+1) → ℕ}

local notation3 (prettyPrint := false) "frame(" u ")" => (pub u 0).val
local notation3 (prettyPrint := false) "published(" u ")" => Directory.ISA.publish (mid u) (frame(u)) base (dir.directory (pp u) (lp u))
local notation3 (prettyPrint := false) "pr(" u ")" => privateLayout (frame(u)) geo task.cube.cables task.cube.cells dir.entries dir.description gap

variable (label : Fin task.cube.cells → Label (task.cube.n+1) task.cube.header.d)
    (owners : (Packet task.cube.n task.cube.header.d task.cube.header.blocks → Selector task.cube.n task.cube.K task.cube.h) → Fin task.cube.header.d → Fin (R+1))
    (q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) owners)
set_option quotPrecheck false in
local notation "axis" => chosen task.cube.b task.cube.s q.1
local notation3 (prettyPrint := false) "Cables" => Fintype.card (N.CrossingEdge cell)


/-- Assemble the independently reached signed hosts on the common frame of the joint
writer. Each tuple is produced by `SharedWriters.signed_pinned_host` from its original
publication and writer path. The ordered rows and interval memories can differ
between teams before the native sparse ordinals are identified. -/
theorem HostTables.ofSignedHosts {common : ℕ} (frames : ∀ u,frame(u)=common)
    (rep : ∀ u, Represents N cell aux siteID edgeID portID F (x u)) (ids : ∀ c,(F.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (img : ∀ u, Image F old ports (x u) geo (readings (profile u)))
    (place : ∀ u, (pr(u)).Image (readings (profile u)) dir.entries (readings (mid u)))
    (hdr : ∀ u, Header (frame(u)) geo task.cube.cables task.cube.cells dir.entries (readings (profile u)))
    (first : ∀ u, frame(u)+112 ≤ base) (reserve : base+7*dir.candidates ≤ geo)
    (endGeo : geo+5*task.cube.cables ≤ task.cube.header.header)
    (source : ∀ u, ProfileRouteInputs (fields u) (B u) (pub u) (guess u) (published(u)))
    (team : ∀ u,(B u).team=u.val)
    {original : Fin dir.entries → N.Site}
    (capacity : ∀ c, suppliedSize N cell c+gap+(∑ j,if cell (original j)=c then dir.description else 0) ≤ task.cube.cellStride)
    (attained : ∀ u, ∃ written input scan : ℕ → ℕ,
      CubeAllocation.HostRetention task.cube (frame(u)) (readings (published(u))) written (readings (out u)) ∧
      NativeEntry task.cube (frame(u)) (controls u) axis R input (readings (published(u))) written ∧
      (∀ c : Fin task.cube.cells,(task.cube.receivingOwner (frame(u)) axis R input c.val).val=
        SignedPrep.routedOwnerWord task.cube owners label q c.val) ∧
      readings (published(u)) ((frame(u))+72)=task.cube.hostDirectory ∧
      ∃ earlier : ℕ → ℕ, ∃ row : Fin Cables ↪o Fin task.cube.cables,
        (∀ e,(row (NativeDemands.cableOrder N cell edgeID e)).val=(edgeID e.val).val) ∧
        PhysicalRows N cell (SignedPrep.signedChooserLayout task.cube (frame(u)) geo) earlier
          (NativeDemands.cableOrder N cell edgeID) row Fin.valEmbedding label
          (productCode task.cube.n task.cube.header.d task.cube.alphabet rfl) ∧
        (SignedPrep.signedChooserLayout task.cube (frame(u)) geo).Image earlier task.cube.cables scan ∧
        ResidentRows (hostLayout pub out u) (SignedPrep.signedChooserLayout task.cube (frame(u)) geo) earlier scan
          (readings (out u)) task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.K task.cube.s) :
    ∃ scan before : Fin (R+1) → ℕ → ℕ, ∃ row : Fin Cables ↪o Fin task.cube.cables,
      HostTables (blocks:=task.cube.header.blocks) (b:=task.cube.b) (h:=task.cube.h) (K:=task.cube.K) (s:=task.cube.s)
        N cell edgeID portID (SignedPrep.signedChooserLayout task.cube common geo) (NativeDemands.cableOrder N cell edgeID)
        row label axis (owners q.1) Fin.valEmbedding pub out task.cube.cellBank task.cube.cellStride before scan rfl := by
  classical
  choose written input scan keep entry selected pointer earlier row aligned phy interval resident using attained
  refine ⟨scan,HostTables.ofPublications task dir N cell aux siteID edgeID portID F pub profile mid out pp lp x B fields
    label owners q rep ids fieldRoom img place hdr first reserve endGeo keep entry source team selected pointer capacity
    (SignedPrep.signedChooserLayout task.cube common geo) rfl rfl scan ?_⟩
  intro u
  rw [←frames u]
  exact ⟨earlier u,NativeDemands.cableOrder N cell edgeID,row u,aligned u,phy u,interval u,resident u⟩

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
