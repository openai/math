import OAI.Computability.BorderVNP.FiniteSewnTileCovers
import OAI.Computability.BorderVNP.PackedSewnTileFragments
import OAI.Computability.BorderVNP.DiagonalExternalSewFieldRows

/-! # Scalar meaning of the emitted reconstruction row of a real terminal tile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Grid

open Crossing Inherited TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open Fragment.Tile CellAddressCircuit ParseBatchSort
open scoped Classical
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option quotPrecheck false

variable {D R r t pins link inner n V groups copies old : ℕ} {E : Type}
    (G : Wiring R r t pins link inner n E) (hV : 0 < V) (count : groups*copies = R+1)
    (N : Network D (Fin groups × Fin V) (fun _ => copies*blockWidth (r*n) V))
    (h : BlockHosts (FineView.layout N (groupedLane G V hV groups copies count))
      (Equiv.refl (PublicPort R r (G.program.length+t) link)) (blockWidth (r*n) V))
    (hg : 0 < blockWidth (r*n) V) (small : blockWidth (r*n) V ≤ link)
local notation "g" => blockWidth (r*n) V
local notation "w₀" => G.program.length+t
local notation "lane" => groupedLane G V hV groups copies count
include hV in
private theorem tile_room : r*(2*w₀+R*link) ≤ V*g := gridRoom G hV
local notation "room" => tile_room G hV
local notation "out" => Network.packExternal (Bundle.layout (BlockHosts.bundle h)) (fun _ : FreeBlock R V => g) (BlockHosts.groupOwner (N := FineView.layout N lane) (V := V) h)
local notation "tm" => teamBlocks groups copies count
local notation "params" => (⟨R,r,w₀,link,g,V⟩ : FieldExport.Params)
variable (oldEdge : N.Edge ↪ Fin old) (oldPort : (Fin groups × Fin V) ↪ Fin (groups*V))
local notation "edge" => FieldExport.mergedEdges params (⟨hg,small,room⟩ : (params).Valid) oldEdge
local notation "port" => (finProdFinEquiv : FreeBlock R V ≃ Fin ((R+1)*V)).toEmbedding

/-- The appended physical row ID is the sparse exterior slot selected by the fixed four-slot naming. -/
theorem tile_piece_id (c : Cables R r w₀ link g) :
    (edge) (.inr c) = FourSlot.pieceOrdinal old V hg small (by omega) room c := rfl

variable {σ : Type*} {W : ℕ} (f : Inputs σ (groups*V) (old+4*(R+1)*V) ((R+1)*V) W)
    (x : σ → Bool) (owner : N.Site → ℕ)

/-- Values of the physical endpoint columns consumed by the tile fragment frame. -/
structure TileColumns : Prop where
  /-- The name of the site that originally hosts the grouped input port. -/
  site : ∀ p, value (x ∘ f.owner (finProdFinEquiv p)) = owner (N.attach p)
  /-- The old site-local input offset of the entire grouped port. -/
  original : ∀ v (a : Attached N v), value (x ∘ f.oldStart (finProdFinEquiv a.val)) =
    portStart N oldEdge oldPort v a
  /-- The new site-local offset of each remaining port. -/
  live : ∀ v (a : Attached out v), value (x ∘ f.newStart (.inr (port a.val))) =
    portStart out edge port v a
  /-- The new site-local offset of the low endpoint, including a shared loop. -/
  source : ∀ c : Cables R r w₀ link g, value (x ∘ f.newStart (Layer.edgeEnd (edge (.inr c)) true)) =
    wireStart out edge port ((out).src (.inr c)) ⟨.inr c,Or.inl rfl⟩
  /-- The new site-local offset of the high endpoint, including a shared loop. -/
  dest : ∀ c : Cables R r w₀ link g, value (x ∘ f.newStart (Layer.edgeEnd (edge (.inr c)) false)) =
    wireStart out edge port ((out).dst (.inr c)) ⟨.inr c,Or.inr rfl⟩

variable (v : N.Site) (a : Attached N v) (i : Fin copies)
local notation "u" => (tm).symm (a.val.1,i)
local notation "runspec" => TileRuns.Run R r w₀ link g u a.val.2.val
local notation "readAt" => copyRead G hV count N h hg oldEdge oldPort edge port v a i
local notation "fr" => fragment G hV count N h hg oldEdge oldPort edge port v a i
local notation "itemAt" => item count u a.val.2 old hg small room

include hg in
private theorem endpoint_at (s : Bool) (c : Cables R r w₀ link g) (j : Fin (cableWidth c)) (k : Fin g)
    (hk : TileRuns.lookup u a.val.2.val k = some (.inr (s,⟨c,j⟩))) :
    (if s then (out).dst (.inr c) else (out).src (.inr c)) = v := by
  have eq := (lookup_grouped_iff G hV count hg a.val i k (.inr (s,⟨c,j⟩))).mp hk
  have ht := (congrArg (fun p : Σ _ : Fin groups × Fin V, Fin (copies*g) => N.attach p.1) eq).trans a.property
  have endSite := (h.bundle.atEnd c s j).symm.trans ht
  cases s <;> exact endSite

/-- The live endpoint operand in a positive physical range is the source of the real affine `Grid.fragment`. -/
theorem tile_source (cols : TileColumns G hV count N h hg small oldEdge oldPort f x owner)
    (q : runspec) (pos : 0 < q.width) :
    (itemAt q).endpoint.map (fun e => value (x ∘ f.newStart e)+(itemAt q).displacement) = (fr q).source := by
  have fit := q.fit
  have low : q.first < g := by omega
  let k : Fin g := ⟨q.first,low⟩
  have live := q.read 0 pos k (Nat.add_zero _).symm
  simp only [fragment,dite_eq_left low]
  change _ = (readAt k).map Fin.val
  cases kind : q.kind with
  | zero =>
    rw [kind] at live
    rw [copyRead_zero G hV count N h hg oldEdge oldPort edge port v a i k live]
    simp [item,kind]
  | «free» =>
    rw [kind] at live
    obtain ⟨z,hz⟩ := live
    obtain ⟨p,eq,rd⟩ := copyRead_free G hV count N h hg oldEdge oldPort edge port v a i k z hz
    have dest := cols.live v p
    change value (x ∘ f.newStart (.inr (finProdFinEquiv p.val))) = _ at dest
    rw [eq] at dest
    simp only [item,kind,Option.map_some,rd,dest,k]
    rfl
  | cable side c =>
    rw [kind] at live
    obtain ⟨j,hj,hj'⟩ := live
    obtain ⟨e,eq,rd⟩ := copyRead_cable G hV count N h hg oldEdge oldPort edge port v a i k side c j hj'
    simp only [hj,Nat.add_zero] at rd
    rw [rd]
    have vt := endpoint_at G hV count N h hg v a i side c j k hj'
    obtain ⟨z,inc⟩ := e
    change z = Sum.inr c at eq
    subst z
    have named : (edge) (.inr c) = FourSlot.pieceOrdinal old V hg small (by omega) room c := rfl
    cases side
    · change (out).src (.inr c) = v at vt
      subst v
      have hs := cols.source c
      rw [named] at hs
      simp only [item,kind,Bool.not_false,Option.map_some,Nat.add_zero]
      exact congrArg some hs
    · change (out).dst (.inr c) = v at vt
      subst v
      have hs := cols.dest c
      rw [named] at hs
      simp only [item,kind,Bool.not_true,Option.map_some,Nat.add_zero]
      exact congrArg some hs

/-- A parsed public tile item is the scalar-valued site name and the true old-port fragment after its two old offsets are added. -/
theorem tileItem_parsed (cols : TileColumns G hV count N h hg small oldEdge oldPort f x owner)
    (q : runspec) (pos : 0 < q.width) :
    f.parsed x (itemAt q) = ⟨owner v,⟨portStart N oldEdge oldPort v a+(i.val*g+q.first),q.width,(fr q).source⟩⟩ := by
  have team := (tm).apply_symm_apply (a.val.1,i)
  have previous := cols.original v a
  have site := (cols.site a.val).trans (congrArg owner a.property)
  have target := tile_source G hV count N h hg small oldEdge oldPort f x owner v a i cols q pos
  change Fragment.Parsed.mk _ (Interval.mk _ _ _) = _
  congr 1
  · simpa only [item,team,Prod.mk.eta] using site
  · congr 1
    · simpa only [item,team,Prod.mk.eta] using congrArg (·+(i.val*g+q.first)) previous

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
