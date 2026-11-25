import OAI.Computability.BorderVNP.DiagonalExternalFragmentCables
import OAI.Computability.BorderVNP.DiagonalReportPublishedExtent
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostRetention

/-! # The host's cable rows after the actual placement, publication, and owned pass -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open RoutingISA VPVNP.BurstRAM Crossing

variable {dir : Directory.Layout} {frame origin cables cells base gap w : ℕ}
    {profile placed : Memory w} (pp lp : ℕ → ℕ × ℕ)

local notation3 (prettyPrint := false) "pr" => privateLayout frame origin cables cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "pubMem" => readings (Directory.ISA.publish placed frame base (dir.directory pp lp))

/-- The cable triples and endpoint pointers precede every private-placement write,
and follow the actual sparse demand directory. -/
theorem published_cable_words (place : (pr).Image (readings profile) dir.entries (readings placed))
    (first : frame+112 ≤ base) (reserve : base+7*dir.candidates ≤ origin) :
    ∀ a, origin ≤ a → a < origin+5*cables → pubMem a=readings profile a := by
  intro a lo hi
  have plen := Nat.mul_le_mul_left 7 (dir.directory_length_le pp lp)
  have p := place.outside a (fun j hj => by dsimp only [privateLayout,bases]; omega)
    (.inl (by dsimp only [privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied]; omega))
  exact (congrArg Fin.val (CableTriples.published_outside placed frame base (dir.directory pp lp) a
    (by omega) (.inr (by omega)))).trans p

/-- Publication rewrites one header entry. All six routing header fields of the
actual emitted geometry survive both private placement and directory publication. -/
theorem published_routing_header (place : (pr).Image (readings profile) dir.entries (readings placed))
    (hdr : Header frame origin cables cells dir.entries (readings profile))
    (first : frame+112 ≤ base) (reserve : base+7*dir.candidates ≤ origin) :
    Header frame origin cables cells dir.entries pubMem := by
  have keep (i : ℕ) (lt : i<112) (ne : i≠9) : pubMem (frame+i)=readings profile (frame+i) := by
    have p := place.outside (frame+i) (fun j hj => by dsimp only [privateLayout,bases]; omega)
      (.inl (by dsimp only [privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied]; omega))
    exact (congrArg Fin.val (CableTriples.published_outside placed frame base (dir.directory pp lp) (frame+i)
      (by omega) (.inl (by omega)))).trans p
  exact ⟨(keep 6 (by decide) (by decide)).trans hdr.cables,
    (keep 7 (by decide) (by decide)).trans hdr.edges,
    (keep 11 (by decide) (by decide)).trans hdr.cells,
    (keep 64 (by decide) (by decide)).trans hdr.privatePairs,
    (keep 65 (by decide) (by decide)).trans hdr.livePairs,
    (keep 87 (by decide) (by decide)).trans hdr.ends⟩

end Packing.RoutingOutputs

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical
open Packing.RoutingOutputs BorderVNP.Cube RoutingISA ParseBatchSort VPVNP.BurstRAM FiniteEvaluator
open scoped Classical

variable {D sz n d k b w frame origin base gap : ℕ} {P σ : Type*} [Fintype P] [Fintype σ]
    {bits : P → ℕ} {ar : CubeArena.Layout} {dir : Directory.Layout}
    (N : Network D P bits) (cell : N.Site → Fin ar.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin sz) (edgeID : N.Edge ↪ Fin ar.cables) (portID : P ↪ Fin n)
    (F : Fields sz ar.cables n ar.cells d k b σ) {x : σ → Bool} {A : ℕ}
    {old : Fin dir.entries → Fin sz} {ports : Fin A → Fin n}
    {profile placed : Memory w} {written out : ℕ → ℕ}
local notation3 (prettyPrint := false) "pr" => privateLayout frame origin ar.cables ar.cells dir.entries dir.description gap

/-- The two cable passes at the owned return see the true cable and endpoint addresses
from the emitted geometry, including vacant ordinals and zero-width edges. -/
theorem CableRows.ofPublished (rep : Represents N cell aux siteID edgeID portID F x)
    (ids : ∀ c,(F.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (img : Image F old ports x origin (readings profile))
    (pp lp : ℕ → ℕ × ℕ)
    (place : (pr).Image (readings profile) dir.entries (readings placed))
    (hdr : Header frame origin ar.cables ar.cells dir.entries (readings profile))
    (first : frame+112 ≤ base) (reserve : base+7*dir.candidates ≤ origin)
    (endGeo : origin+5*ar.cables ≤ ar.header.header)
    (retention : CubeAllocation.HostRetention ar frame
      (readings (Directory.ISA.publish placed frame base (dir.directory pp lp))) written out) :
    CableRows N cell edgeID portID (HostScatter.Layout.fromFrame frame out) out := by
  have pointers := retention.header (published_routing_header pp lp place hdr first reserve)
  apply CableRows.ofImage N cell edgeID portID _ _ aux siteID F rep ids fieldRoom img
    pointers.cables pointers.ends pointers.edges
  intro a lo hi
  exact (retention.geometry (by omega) a lo (hi.trans_le endGeo)).trans
    (published_cable_words pp lp place first reserve a lo hi)

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
