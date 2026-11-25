import OAI.Computability.BorderVNP.FiniteSewnTileSourcePartition
import OAI.Computability.BorderVNP.PackedSewnFragmentJoin
import OAI.Computability.BorderVNP.PackedSewnFragmentMaximal

/-! # Exact old-lane coverage and maximal row image of the joined physical sewing operand -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open VPVNP.VerifierNetwork (Frame)

/-- A gate-free join transfers the disjoint complete cover of the two mathematical
rosters to the filtered lists of actual positive descriptors at each site. -/
theorem joinFrame_cover {σ : Type} [Fintype σ] {l r w old next : ℕ}
    (a : Frame σ (Pin l w)) (b : Frame σ (Pin r w)) (x : σ → Bool) (v : ℕ)
    (xs ys : List Interval) (read : Fin old → Option (Fin next))
    (one : Covers (xs++ys) read ∧ (xs++ys).Pairwise Interval.Separate)
    (pre : (siteRuns v (list (a.eval x))).Perm (xs.filter fun p => decide (0<p.width)))
    (post : (siteRuns v (list (b.eval x))).Perm (ys.filter fun p => decide (0<p.width))) :
    let rows := siteRuns v (list ((joinFrame a b).eval x))
    Covers rows read ∧ UniqueCover old rows := by
  intro rows
  let pos := fun p : Interval => decide (0<p.width)
  have eq : rows.Perm ((xs++ys).filter pos) := by
    dsimp only [rows]
    rw [joinFrame_siteRuns,List.filter_append]
    exact pre.append post
  have cov := one.1.keep_positive
  have full : Covers rows read := by
    refine ⟨fun p hp => cov.oldFit p (eq.subset hp),fun p hp => cov.newFit p (eq.subset hp),
      fun p hp => cov.agrees p (eq.subset hp),?_⟩
    intro k
    obtain ⟨p,hp,j,hj,he⟩ := cov.covers k
    exact ⟨p,eq.symm.subset hp,j,hj,he⟩
  have sep : rows.Pairwise Interval.Separate := (eq.pairwise_iff fun h k hk hl => h k hl hk).mpr (one.2.filter _)
  exact ⟨full,full.unique_index sep⟩

end Packing.SewnField.Fragment

namespace Packing.SewnField.Grid

open Crossing Inherited TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open VPVNP.VerifierNetwork (Frame)
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

local notation "wires" => Finset.univ.toList.map (wireInterval N groupLane h.bundle (fun _ : FreeBlock R V => g)
  owner oldEdge oldPort edge port v)
local notation "copyList" => copyRoster G hV count N h hg oldEdge oldPort edge port v
local notation "roster" => siteRoster G hV count N h hg oldEdge oldPort edge port v

variable (small : blockWidth (r*n) V ≤ link)
local notation "portRows" => Finset.univ.toList.flatMap (fun a : Attached N v =>
  List.map (atOffset (portStart N oldEdge oldPort v a)) (copyIntervals copies g (copyList small a)))
local notation "positive" => (fun q : Interval => decide (0 < Interval.width q))
variable {σ : Type} [Fintype σ] {left right w : ℕ} (wireFrame : Frame σ (Fragment.Pin left w))
    (portFrame : Frame σ (Fragment.Pin right w)) (x : σ → Bool) (siteID : ℕ)
local notation "input" => Frame.eval (Fragment.joinFrame wireFrame portFrame) x
local notation "site" => Fragment.siteRuns siteID (Fragment.list input)

/-- The two physical gate images combine to give the exact set of original ordinals at
this site, with a unique physical row index for each lane. All actual source ranges fit
and agree with the true sewn map, including clamps and retained cable loops. -/
theorem joined_source_image
    (wireImage : (Fragment.siteRuns siteID (Fragment.list (wireFrame.eval x))).Perm ((wires).filter positive))
    (portImage : (Fragment.siteRuns siteID (Fragment.list (portFrame.eval x))).Perm ((portRows).filter positive))
    : Covers site read₀ ∧ Fragment.UniqueCover (incoming N v) site := by
  exact Fragment.joinFrame_cover wireFrame portFrame x siteID wires portRows read₀
    (siteRoster_partition G hV count N h hg oldEdge oldPort edge port v small) wireImage portImage

/-- The emitted maximal staging rows of this actual joined source are the canonical
intervals of the genuine exterior-sewn site map. -/
theorem joined_maximal_image
    (wireImage : (Fragment.siteRuns siteID (Fragment.list (wireFrame.eval x))).Perm ((wires).filter positive))
    (portImage : (Fragment.siteRuns siteID (Fragment.list (portFrame.eval x))).Perm ((portRows).filter positive))
    (fit : ∀ a ∈ Fragment.list input, 0 < a.run.width → a.Fits w) :
    Fragment.siteRuns siteID (Fragment.list ((Fragment.maximal (left+right) w).eval input)) = intervals read₀ := by
  have data := joined_source_image G hV count N h hg oldEdge oldPort edge port v small wireFrame portFrame x siteID wireImage portImage
  exact Fragment.maximal_siteRuns_of_cover _ fit siteID _ data.1 data.2

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
