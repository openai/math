import OAI.Computability.BorderVNP.FiniteSewnTileCovers
import OAI.Computability.BorderVNP.FiniteSewnFieldDirectory

/-! # Public row charge of the real finite candidate's sewn programs

For each site, the final incidence stage uses at most one interval for
each retained incident edge and six for each copy of an attached original
grouped word. Free and linked words are read at the true new row ordinals.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Grid

open Crossing Inherited TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
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

/-- The real candidate's exterior sewing supplies a complete public
interval cover with the explicit per-site row bound. -/
theorem sewn_intervals_le (small : g ≤ link) :
    (intervals read₀).length ≤ Fintype.card (Incident N v) + 6*copies*Fintype.card (Attached N v) := by
  let who (a : Attached N v) (i : Fin copies) := (tm).symm (a.val.1,i)
  let perCopy (a : Attached N v) (i : Fin copies) :=
    (TileRuns.runs (r:=r) (w:=literalWidth) (who a i) a.val.2.val hg small).map (piece₀ a i)
  let chunks (a : Attached N v) := copyIntervals copies g (perCopy a)
  have covers (a : Attached N v) : Covers (chunks a)
      (fun k : Fin (copies*g) => read₀ (ord (.inr ⟨a,k⟩))) :=
    copies_cover _ (perCopy a) fun i => tile_cover G hV count N h hg oldEdge oldPort edge port v a i small
  have bounded (a : Attached N v) : (chunks a).length ≤ 6*copies := by
    rw [show (chunks a).length = ∑ i, (perCopy a i).length from copyIntervals_length _]
    calc
      _ ≤ ∑ _ : Fin copies, 6 := Finset.sum_le_sum fun i _ => by
        simpa only [perCopy,List.length_map] using (TileRuns.runs_length (r:=r) (w:=literalWidth) (who a i) a.val.2.val hg small)
      _ = 6*copies := by simp [Nat.mul_comm]
  calc
    _ ≤ Fintype.card (Incident N v) + ∑ a, (chunks a).length :=
      port_words_count N groupLane h.bundle (fun _ : FreeBlock R V => g) free owner (h.groupAligned hg room)
        oldEdge oldPort edge port v chunks covers
    _ ≤ Fintype.card (Incident N v) + ∑ _ : Attached N v, 6*copies := Nat.add_le_add_left
      (Finset.sum_le_sum fun a _ => bounded a) _
    _ = _ := by simp [Nat.mul_comm]

private theorem intervals_cast {a b c : ℕ} (h : a=b) (read : Fin b → Option (Fin c)) :
    intervals (fun k : Fin a => read (Fin.cast h k)) = intervals read := by
  subst b
  rfl

/-- The sparse physical program adds only these new descriptors to its
previous public rows, with no changes to its old ordered box visits. -/
theorem sewnSite_rows_le {F : Type*} [Field F] {T : N.Tables F} (S : FiniteDiagonal.FieldSiteDirectory N T)
    (small : g ≤ link) :
    (sewnSite N groupLane h.bundle (fun _ : FreeBlock R V => g) free owner (h.groupAligned hg room)
      edge port S v).rows.length ≤ (S.site v).rows.length +
      (Fintype.card (Incident N v) + 6*copies*Fintype.card (Attached N v)) := by
  change (stage (S.site v) (incoming out v) (intervals (programRead N groupLane h.bundle (fun _ : FreeBlock R V => g)
    free owner (h.groupAligned hg room) edge port S v))).rows.length ≤ _
  rw [stage_rows,List.length_append,List.length_map]
  apply Nat.add_le_add_left
  change (intervals (fun k => sewnRead N groupLane h.bundle (fun _ : FreeBlock R V => g) free owner
    (h.groupAligned hg room) S.edgeID S.portID edge port v (Fin.cast (S.incoming v) k))).length ≤ _
  rw [intervals_cast]
  exact sewn_intervals_le G hV count N h hg S.edgeID S.portID edge port v small

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
