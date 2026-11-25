import OAI.Computability.BorderVNP.FiniteSewnTileOrdinal
import OAI.Computability.BorderVNP.DiagonalExternalFreePhysical

/-! # Affine terminal reads on a genuine finite candidate's tile runs -/

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

/-- A copy-local port lane as seen at the old site's actual physical ordinal. -/
noncomputable def copyRead (k : Fin g) : Option (Fin (incoming out v)) :=
  read₀ (ord (.inr ⟨a,finProdFinEquiv (i,k)⟩))

local notation "readAt" => copyRead G hV count N h hg oldEdge oldPort edge port v a i

private theorem live (k : Fin g) (s : slots) (hs : TileRuns.lookup u a.val.2.val k = some s) :
    ∃ ht : (FineView.layout N groupLane).attach (h.bundle.ports s) = v,
      readAt k = some (sourceOrder out edge port v
        (bundleLane N groupLane h.bundle (fun _ : FreeBlock R V => g) free owner (h.groupAligned hg room) v s ht)) := by
  have lane : groupLane (h.bundle.ports s) = ⟨a.val,finProdFinEquiv (i,k)⟩ :=
    (lookup_grouped_iff G hV count hg a.val i k s).mp hs
  let ht := (congrArg (fun j : Σ _ : Fin groups × Fin V, Fin (copies*g) => N.attach j.1) lane).trans a.property
  refine ⟨ht,?_⟩
  have ex : ∃ p, groupLane p = ⟨a.val,finProdFinEquiv (i,k)⟩ := ⟨h.bundle.ports s,lane⟩
  have unique : ex.choose = h.bundle.ports s := (groupLane).injective (ex.choose_spec.trans lane.symm)
  simp only [copyRead,sewnRead,Equiv.symm_apply_apply,sewnLane,dite_eq_left ex,unique,Equiv.symm_apply_apply,
    Option.map_some]

/-- Unoccupied old lanes are precisely zero clamps. -/
theorem copyRead_zero (k : Fin g) (hs : TileRuns.lookup (r:=r) (w:=literalWidth) (link:=link) u a.val.2.val k = none) :
    readAt k = none := by
  have no : ¬ ∃ p, groupLane p = ⟨a.val,finProdFinEquiv (i,k)⟩ := by
    rintro ⟨p,hp⟩
    let s := (TileRuns.port R r literalWidth link g).symm p
    have eqn : TileRuns.lookup u a.val.2.val k = some s :=
      (lookup_grouped_iff G hV count hg a.val i k s).mpr (by simpa [s] using hp)
    simp [hs] at eqn
  simp [copyRead,sewnRead,sewnLane,no]

/-- A live free slot reads its old tile offset inside the actual named
free-port word of the retained host. -/
theorem copyRead_free (k : Fin g) (f : FreePort R r literalWidth) (hs : TileRuns.lookup (link:=link) u a.val.2.val k = some (.inl f)) :
    ∃ p : Attached out v, p.val = (u,a.val.2) ∧
      (readAt k).map Fin.val = some (portStart out edge port v p+k.val) := by
  obtain ⟨ht,yes⟩ := live G hV count N h hg oldEdge oldPort edge port v a i k (.inl f) hs
  let p : Attached out v := ⟨(free f).1,(h.groupAligned hg room f).trans ht⟩
  have coord := TileRuns.lookup_free_lane hg room u a.val.2 k f hs
  have lane : (free f).2 = k := congrArg (fun z : Σ _ : FreeBlock R V, Fin g => z.2) coord
  refine ⟨p,congrArg Sigma.fst coord,?_⟩
  rw [yes,Option.map_some]
  apply congrArg some
  exact (portOrdinal out edge port v p (free f).2).trans (congrArg (portStart out edge port v p+·) (congrArg Fin.val lane))

/-- A linked bit reads the given lane of its real interval cable, at the
physical named source or target incidence (including a shared loop). -/
theorem copyRead_cable (k : Fin g) (side : Bool) (c : Cables R r literalWidth link g) (j : Fin (cableWidth c))
    (hs : TileRuns.lookup u a.val.2.val k = some (.inr (side,⟨c,j⟩))) :
    ∃ e : Incident out v, e.val = .inr c ∧
      (readAt k).map Fin.val = some (wireStart out edge port v e+j.val) := by
  obtain ⟨ht,yes⟩ := live G hV count N h hg oldEdge oldPort edge port v a i k (.inr (side,⟨c,j⟩)) hs
  cases side
  · let e : Incident out v := ⟨.inr c,Or.inl ((h.bundle.atEnd c false j).symm.trans ht)⟩
    refine ⟨e,rfl,?_⟩
    rw [yes,Option.map_some]
    exact congrArg some (wireOrdinal out edge port v e j)
  · let e : Incident out v := ⟨.inr c,Or.inr ((h.bundle.atEnd c true j).symm.trans ht)⟩
    refine ⟨e,rfl,?_⟩
    rw [yes,Option.map_some]
    exact congrArg some (wireOrdinal out edge port v e j)

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
