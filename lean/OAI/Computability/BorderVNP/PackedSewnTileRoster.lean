import OAI.Computability.BorderVNP.PackedSewnTileSemantic
import OAI.Computability.BorderVNP.PackedSewnFragmentProjection
import OAI.Computability.BorderVNP.FiniteSewnTileSourcePartition

/-! # Decoding the six genuine exterior-sewing probes at an original port

Each physical copy contributes the occupied intervals of its tile, in the
tile's original order. The two old offsets are applied separately, first for
the original copy and then for its physical port inside the site's input.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment.Tile

/-- What one physical fragment contributes at the requested site. -/
def pick {n w : ℕ} (y : Pin n w → Bool) (v : ℕ) (j : Fin n) : Option Interval :=
  if active y j then if (parse y j).site=v then some (parse y j).run else none else none

theorem siteRuns_eq_pick {n w : ℕ} (y : Pin n w → Bool) (v : ℕ) :
    siteRuns v (list y) = (List.finRange n).filterMap (pick y v) := by
  rw [siteRuns,list,List.filterMap_filterMap]
  apply List.filterMap_congr
  intro j _
  cases h : active y j <;> simp [pick,h]

/-- Reading all the reserved addresses once discards only the unused suffix. -/
theorem readSlots {α : Type*} (n : ℕ) (xs : List α) (fits : xs.length≤n) :
    (List.finRange n).filterMap (fun i => xs[i.val]?) = xs := by
  induction n generalizing xs with
  | zero => have h := List.eq_nil_of_length_eq_zero (by omega : xs.length=0); subst xs; rfl
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      rw [List.finRange_succ]
      rw [List.filterMap_cons_some (b:=a) (by rfl),List.filterMap_map]
      exact congrArg (a::·) (ih xs (by simpa using fits))

/-- Retaining positive members of a list after applying their true interval coordinates. -/
theorem positiveMap {α : Type*} (xs : List α) (f : α → Interval) :
    xs.filterMap (fun a => if 0<(f a).width then some (f a) else none) =
      (xs.map f).filter (fun z => decide (0<z.width)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => by_cases h : 0<(f a).width <;> simp [h,ih]

end Packing.SewnField.Fragment.Tile

namespace Packing.SewnField.Grid

open Crossing Inherited TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open Fragment.Tile CellAddressCircuit VPVNP.VerifierNetwork
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 4500
set_option quotPrecheck false

variable {D R r t pins link inner n V groups copies old : ℕ} {E : Type}
    (G : Wiring R r t pins link inner n E) (hV : 0 < V) (count : groups*copies = R+1)
    (N : Network D (Fin groups × Fin V) (fun _ => copies*blockWidth (r*n) V))
    (h : BlockHosts (FineView.layout N (groupedLane G V hV groups copies count))
      (Equiv.refl (PublicPort R r (G.program.length+t) link)) (blockWidth (r*n) V))
    (hg : 0 < blockWidth (r*n) V) (small : blockWidth (r*n) V ≤ link)
local notation "g" => blockWidth (r*n) V
local notation "w₀" => G.program.length+t
open private tile_room from OAI.Computability.BorderVNP.PackedSewnTileSemantic
local notation "room" => tile_room G hV
local notation "tm" => teamBlocks groups copies count
local notation "params" => (⟨R,r,w₀,link,g,V⟩ : FieldExport.Params)
variable (oldEdge : N.Edge ↪ Fin old) (oldPort : (Fin groups × Fin V) ↪ Fin (groups*V))
local notation "edge" => FieldExport.mergedEdges params (⟨hg,small,room⟩ : (params).Valid) oldEdge
local notation "port" => (finProdFinEquiv : FreeBlock R V ≃ Fin ((R+1)*V)).toEmbedding

variable {σ : Type*} [Fintype σ] {w : ℕ} (f : Inputs σ (groups*V) (old+4*(R+1)*V) ((R+1)*V) w)
    (x : σ → Bool) (owner : N.Site → ℕ) (cols : TileColumns G hV count N h hg small oldEdge oldPort f x owner)
    (v : N.Site) (a : Attached N v) (i : Fin copies)
local notation "u" => (tm).symm (a.val.1,i)
local notation "tile" => a.val.2
local notation "tileRows" => TileRuns.runs (r:=r) (w:=w₀) u (tile).val hg small
local notation "runspec" => TileRuns.Run R r w₀ link g u (tile).val
local notation "rangeOf" => fragment G hV count N h hg oldEdge oldPort edge port v a i
local notation "shiftRun" => fun q : runspec => atOffset (portStart N oldEdge oldPort v a) (atOffset (i.val*g) (rangeOf q))
local notation "itemAt" => item count u tile old hg small room
local notation "y" => (frame f (slot count old hg small room)).eval x

include cols in
/-- One addressed probe either contributes its authentic shifted interval at
the old site or contributes no output, including the tail of a padded tile. -/
theorem tile_pick (fits : ∀ q : runspec, 0<q.width → f.Fits x (itemAt q)) (requested : ℕ) (j : Fin 6) :
    pick y requested (ordinal R V (u,tile,j)) =
      (tileRows[j.val]?).bind (fun q => if 0<q.width ∧ owner v=requested then some (shiftRun q) else none) := by
  let key := ordinal R V (u,tile,j)
  have sl : slot count old hg small room key = (tileRows[j.val]?).map itemAt := by
    unfold key Fragment.Tile.slot
    rw [Equiv.symm_apply_apply]
  have active := active_iff f (slot count old hg small room) x key
  rw [sl] at active
  change pick y requested key = _
  cases get : tileRows[j.val]? with
  | none =>
    rw [get] at active
    have off : Fragment.active y key = false := Bool.eq_false_iff.mpr (by simpa using active)
    simp [pick,off]
  | some q =>
    rw [get] at sl active
    have enabled : Fragment.active y key = true ↔ 0<q.width := by simpa [item] using active
    by_cases positive : 0<q.width
    · have fields := (parse_eq f (slot count old hg small room) x (by simpa using sl) (fits q positive)).trans
          (tileItem_parsed G hV count N h hg small oldEdge oldPort f x owner v a i cols q positive)
      simp only [pick,enabled.mpr positive,ite_true,fields,Option.bind_some,positive,true_and]
      rfl
    · have off := Bool.eq_false_iff.mpr (fun on => positive (enabled.mp on))
      simp [pick,off,positive]

include cols in
/-- All six probes at an original copy produce exactly its positive
site-local intervals. Filtering at any other site yields the empty list. -/
theorem tile_picks (fits : ∀ q : runspec, 0<q.width → f.Fits x (itemAt q)) (requested : ℕ) :
    (List.finRange 6).filterMap (fun j => pick y requested (ordinal R V (u,tile,j))) =
      if owner v = requested then ((tileRows).map shiftRun).filter (fun z => decide (0<z.width)) else [] := by
  have lookup := readSlots 6 tileRows (TileRuns.runs_length (r:=r) (w:=w₀) u (tile).val hg small)
  simp_rw [tile_pick G hV count N h hg small oldEdge oldPort f x owner cols v a i fits requested]
  rw [← List.filterMap_filterMap,lookup]
  by_cases same : owner v=requested
  · simp only [same,and_true,ite_true]
    refine Eq.trans ?_ (positiveMap tileRows shiftRun)
    apply List.filterMap_congr
    intro q _
    have size : ((shiftRun) q).width=q.width := rfl
    by_cases pos : 0<q.width <;> simp [size,pos]
  · simp [same]

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
