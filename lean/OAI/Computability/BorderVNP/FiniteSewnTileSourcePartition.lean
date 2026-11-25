import OAI.Computability.BorderVNP.FiniteSewnTileCount
import OAI.Computability.BorderVNP.FiniteSewnPortWordDisjoint
import OAI.Computability.BorderVNP.DiagonalExternalTileDisjoint

/-! # The exact old-input partition of every grouped physical exterior-sewn host -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Grid

open Crossing Inherited TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open private disjoint_run from OAI.Computability.BorderVNP.DiagonalExternalTileDisjoint
open scoped Classical
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

variable {D R r t pins link inner n V groups copies : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (hV : 0 < V) (count : groups*copies = R+1)
    (N : Network D (Fin groups × Fin V) (fun _ => copies*blockWidth (r*n) V))
    (h : BlockHosts (FineView.layout N (groupedLane G V hV groups copies count))
      (Equiv.refl (PublicPort R r (G.program.length+t) link)) (blockWidth (r*n) V))
    (hg : 0 < blockWidth (r*n) V)

local notation "g" => blockWidth (r*n) V
local notation "literalWidth" => G.program.length+t
local notation "groupLane" => groupedLane G V hV groups copies count
local notation "room" => gridRoom G hV
local notation "free" => freeLane hg room
local notation "owner" => BlockHosts.groupOwner (N := FineView.layout N groupLane) (V := V) h
local notation "out" => Network.packExternal (Bundle.layout (BlockHosts.bundle h)) (fun _ : FreeBlock R V => g) owner
local notation "tm" => teamBlocks groups copies count

variable {ae ap be bp : ℕ} (oldEdge : N.Edge ↪ Fin ae) (oldPort : (Fin groups × Fin V) ↪ Fin ap)
    (edge : (N.Edge ⊕ Cables R r (G.program.length+t) link (blockWidth (r*n) V)) ↪ Fin be)
    (port : FreeBlock R V ↪ Fin bp) (v : N.Site)

local notation "ord" => sourceOrder N oldEdge oldPort v
local notation "read₀" => sewnRead N groupLane (BlockHosts.bundle h) (fun _ : FreeBlock R V => g) free
  owner (BlockHosts.groupAligned h hg room) oldEdge oldPort edge port v
local notation "piece₀" => fragment G hV count N h hg oldEdge oldPort edge port v

/-- The affine descriptors of one retained tile in one original copy, with the actual
post-sewing source pointer for its free, linked, or clamped lanes. -/
noncomputable def copyRoster (small : g ≤ link) (a : Attached N v) (i : Fin copies) : List Interval :=
  (TileRuns.runs (r:=r) (w:=literalWidth) ((tm).symm (a.val.1,i)) a.val.2.val hg small).map (piece₀ a i)

local notation "copyList" => copyRoster G hV count N h hg oldEdge oldPort edge port v

/-- Distinct physical source kinds inside a single copy never claim the same old lane. -/
theorem copyRoster_separate (small : g ≤ link) (a : Attached N v) (i : Fin copies) :
    (copyList small a i).Pairwise Interval.Separate := by
  let u := (tm).symm (a.val.1,i)
  let tile := a.val.2
  apply List.pairwise_map.mpr
  have nodup := (TileRuns.runs_nodup_kind (r:=r) (w:=literalWidth) u tile.val hg small).of_map TileRuns.Run.kind
  apply nodup.imp_of_mem
  intro a b ha hb ne k ka kb
  change a.first ≤ k ∧ k < a.first+a.width at ka
  change b.first ≤ k ∧ k < b.first+b.width at kb
  have sep := disjoint_run u tile hg small ha hb ne (by omega) (by omega)
  omega

/-- The complete per-site raw roster before suppression of zero-width reservations. Each
old cable appears once at this host, and each attached original tile contributes its
true per-copy descriptors with their old and new physical ordinals. -/
noncomputable def siteRoster (small : g ≤ link) : List Interval :=
  (Finset.univ.toList.map (wireInterval N groupLane h.bundle (fun _ : FreeBlock R V => g) owner oldEdge oldPort edge port v)) ++
    (Finset.univ.toList.flatMap fun a : Attached N v =>
      (copyIntervals copies g (copyList small a)).map (atOffset (portStart N oldEdge oldPort v a)))

local notation "roster" => siteRoster G hV count N h hg oldEdge oldPort edge port v

/-- The old incidence offsets of this site's entire physical descriptor roster give a
complete source map, and no two physical occurrences use the same old lane. -/
theorem siteRoster_partition (small : g ≤ link) :
    Covers (roster small) read₀ ∧ (roster small).Pairwise Interval.Separate := by
  let chunks (a : Attached N v) := copyIntervals copies g (copyList small a)
  have localCover (a : Attached N v) (i : Fin copies) := tile_cover G hV count N h hg oldEdge oldPort edge port v a i small
  have words (a : Attached N v) : Covers (chunks a) (fun k : Fin (copies*g) => read₀ (ord (.inr ⟨a,k⟩))) :=
    copies_cover _ (copyList small a) (localCover a)
  refine ⟨covers_port_words N groupLane h.bundle (fun _ : FreeBlock R V => g) free owner (h.groupAligned hg room)
    oldEdge oldPort edge port v chunks words,?_⟩
  apply port_words_separate N groupLane h.bundle (fun _ : FreeBlock R V => g) owner oldEdge oldPort edge port v chunks
    (fun a => (words a).oldFit)
  intro a
  exact copyIntervals_separate _ (fun i => (localCover a i).oldFit)
    (fun i => copyRoster_separate G hV count N h hg oldEdge oldPort edge port v small a i)

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
