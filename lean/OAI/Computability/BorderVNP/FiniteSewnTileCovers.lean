import OAI.Computability.BorderVNP.FiniteSewnTileSources
import OAI.Computability.BorderVNP.FiniteSewnFieldCopyCover
import OAI.Computability.BorderVNP.DiagonalExternalTileRuns

/-! # At most six exterior staging intervals per original tile and copy

The true physical pieces, contiguous free region, and clamped tail of one
tile give a complete interval cover of the sparse executable site's old
input. Their source ordinals use the new physical wire and port rows.
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
    (port : FreeBlock R V ↪ Fin bp) (v : N.Site) (a : Attached N v) (i : Fin copies)

local notation "ord" => sourceOrder N oldEdge oldPort v
local notation "read₀" => sewnRead N groupLane (BlockHosts.bundle h) (fun _ : FreeBlock R V => g) free
  owner (BlockHosts.groupAligned h hg room) oldEdge oldPort edge port v
local notation "u" => Equiv.symm tm (Prod.fst (Subtype.val a),i)
local notation "slots" => TileRuns.Slot R r literalWidth link g

local notation "readAt" => copyRead G hV count N h hg oldEdge oldPort edge port v a i
local notation "tileRun" => TileRuns.Run R r literalWidth link g u (Fin.val (Prod.snd (Subtype.val a)))

/-- Convert a genuine tile fragment into its physical source interval. Empty
fragments at the upper endpoint have no source, and do not access the bank. -/
noncomputable def fragment (q : tileRun) : Interval :=
  ⟨q.first,q.width,if h : q.first<g then (readAt ⟨q.first,h⟩).map Fin.val else none⟩

local notation "fr" => fragment G hV count N h hg oldEdge oldPort edge port v a i

private theorem fragment_agrees (q : tileRun) (j : ℕ) (hj : j<q.width) (k : Fin g) (hk : k.val=q.first+j) :
    (readAt k).map Fin.val = (fr q).source.map (·+j) := by
  have fit := q.fit
  let first : Fin g := ⟨q.first,by omega⟩
  have hfirst : q.first<g := first.isLt
  rw [fragment]
  simp only [dite_eq_left hfirst]
  change (readAt k).map Fin.val = ((readAt first).map Fin.val).map (·+j)
  have r₀ := q.read 0 (by omega) first (Nat.add_zero _).symm
  have r₁ := q.read j hj k hk
  cases kind : q.kind with
  | zero =>
    rw [kind] at r₀ r₁
    rw [copyRead_zero G hV count N h hg oldEdge oldPort edge port v a i first r₀,
      copyRead_zero G hV count N h hg oldEdge oldPort edge port v a i k r₁]
    rfl
  | «free» =>
    rw [kind] at r₀ r₁
    obtain ⟨f₀,h₀⟩ := r₀
    obtain ⟨f₁,h₁⟩ := r₁
    obtain ⟨p₀,v₀,b₀⟩ := copyRead_free G hV count N h hg oldEdge oldPort edge port v a i first f₀ h₀
    obtain ⟨p₁,v₁,b₁⟩ := copyRead_free G hV count N h hg oldEdge oldPort edge port v a i k f₁ h₁
    have same : p₁ = p₀ := Subtype.ext (v₁.trans v₀.symm)
    rw [b₀,b₁,same,hk]
    simp [first,Nat.add_assoc]
  | cable side c =>
    rw [kind] at r₀ r₁
    obtain ⟨j₀,v₀,h₀⟩ := r₀
    obtain ⟨j₁,v₁,h₁⟩ := r₁
    obtain ⟨e₀,ve₀,b₀⟩ := copyRead_cable G hV count N h hg oldEdge oldPort edge port v a i first side c j₀ h₀
    obtain ⟨e₁,ve₁,b₁⟩ := copyRead_cable G hV count N h hg oldEdge oldPort edge port v a i k side c j₁ h₁
    have same : e₁=e₀ := Subtype.ext (ve₁.trans ve₀.symm)
    simp [b₀,b₁,same,v₀,v₁]

/-- The physical field, pin and cable pieces cover every live or clamped
old lane in this copy of the retained tile word. -/
theorem tile_cover (small : g ≤ link) :
    Covers ((TileRuns.runs (r:=r) (w:=literalWidth) u a.val.2.val hg small).map fr) readAt := by
  constructor
  · intro p hp
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
    exact q.fit
  · intro p hp z hz
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
    by_cases positive : 0<q.width
    · have fit := q.fit
      let last : Fin g := ⟨q.first+(q.width-1),by omega⟩
      have eqn := fragment_agrees G hV count N h hg oldEdge oldPort edge port v a i q (q.width-1) (by omega) last rfl
      rw [hz] at eqn
      cases he : readAt last with
      | none => simp [he] at eqn
      | some s =>
        simp [he] at eqn
        have hs := s.isLt
        change z+q.width ≤ _
        omega
    · have zero : q.width=0 := by omega
      change (if h : q.first<g then (readAt ⟨q.first,h⟩).map Fin.val else none) = some z at hz
      change z+q.width ≤ _
      rw [zero,Nat.add_zero]
      split at hz
      next hl =>
        cases hs : readAt ⟨q.first,hl⟩ with
        | none => simp [hs] at hz
        | some s =>
          simp [hs] at hz
          exact hz ▸ Nat.le_of_lt s.isLt
      next => cases hz
  · intro p hp
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
    exact fragment_agrees G hV count N h hg oldEdge oldPort edge port v a i q
  · intro k
    obtain ⟨q,hq,j,hj,hk⟩ := TileRuns.runs_cover (r:=r) (w:=literalWidth) u a.val.2.val hg small k
    exact ⟨fr q,List.mem_map.mpr ⟨q,hq,rfl⟩,j,hj,hk⟩

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
