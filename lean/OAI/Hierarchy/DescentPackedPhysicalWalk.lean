import OAI.Hierarchy.DescentPackedActorHeads
import OAI.Hierarchy.DescentPackedMatchRoster

namespace OAI
/-! # The physical two-hop route for each positive original cable -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentOldOccurrenceRAM PackedLocalMatch
open scoped Classical BigOperators
noncomputable section
private theorem physicalSelf {Z : Type} {r D : ℕ} (next : Z→Fin D→Option Z) (root : Z)
    (own : Fin r→Address) (peer : Fin D→Fin r→Address) (x : Fin r)
    (key : DescentHostDirectory.Key Z) (found : located next root (own x) key) :
    walked next root (look own peer (0,x.val)) key := by
  simpa [walked,walkSite,look,location,located,x.isLt] using found

private theorem physicalPeer {Z : Type} {r D : ℕ} (next : Z→Fin D→Option Z) (root toSite : Z)
    (own : Z→Fin r→Address) (v : Fin D) (x : Fin r) (key : DescentHostDirectory.Key Z)
    (found : located next toSite (own toSite x) key) (link : next root v=some toSite) :
    walked next root (look (own root) (fun i b=>(next root i).elim (0,0,0) (fun z=>own z b)) (v.val+1,x.val)) key := by
  simpa [walked,walkSite,look,location,located,x.isLt,v.isLt,link] using found

namespace Stage
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
local notation "names" => cableNames k rank
local notation "next" => rotor A rank
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 +
        (scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ) (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e) = scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "P" => coloredPack N W.core home color A.cap
local notation "pick" => colorPick N W.core home color A.cap
local notation "venue" => newSite N pick lay P
local notation "key" => nativeKey N W.core home color A.cap addr same lay
local notation "here" => fun h x=>resolved A.cap profile (panel h) lay x
local notation "peer" => fun h v x=>Option.elim (next h v) (0,0,0) (fun other=>here other x)

/-- The queried grain is present even on a positive unmarked tether. -/
def originPort (e : DescentSharedCableNames.Stage.Positive A) :
    A.CellPorts (A.pos ((N).src e.val)).1 (A.pos ((N).src e.val)).2 (A.block ((N).src e.val)) :=
  .inl ⟨⟨e.val,rfl,rfl⟩,⟨0,e.property⟩⟩

def sourceHandle (e : DescentSharedCableNames.Stage.Positive A) :=
  DescentSharedCableNames.Stage.live A native S ready names (DescentSharedCableNames.Stage.home A ((N).src e.val)) (originPort A e)

theorem origin_stored (e : DescentSharedCableNames.Stage.Positive A) :
    let h:=DescentSharedCableNames.Stage.home A ((N).src e.val)
    DescentSharedCableNames.Stage.signedPanel A native S ready names h
      (DescentSharedCableNames.Stage.signed A native S ready h.1 h.2 (originPort A e))=some (sourceHandle A native S ready rank e) :=
  DescentSharedCableNames.Stage.signed_read A native S ready names _ _

theorem origin_routes (e : DescentSharedCableNames.Stage.Positive A) :
    next (A.pos ((N).src e.val)) (sourceHandle A native S ready rank e).neighbor=some (A.pos ((N).dst e.val)) := by
  let h:=A.pos ((N).src e.val);let x:=A.block ((N).src e.val);let z:=A.pos ((N).dst e.val)
  have wz : z∈neighbors A h := (A.peers e.val).1
  let B:=DescentSharedCableNames.Stage.source A native
  let j:=DescentSharedCableNames.Stage.ofPort A native (h,x) (originPort A e)
  let grain : DescentSharedCableNames.Stage.Grain A := ⟨e.val, ⟨0,e.property⟩⟩
  have wire : j.val = DescentSharedCableNames.Stage.stream A native grain := rfl
  have original : ((DescentSharedCableNames.Stage.stream A native).symm j.val).1 = e.val := by
    rw [wire, Equiv.symm_apply_apply]
  have src : B.src j.val = (h,x) := by
    change DescentSharedCableNames.Stage.home A (W.graph.src ((DescentSharedCableNames.Stage.stream A native).symm j.val).1) = _
    rw [original]
    rfl
  have dst : B.dst j.val = (z,x) := by
    change DescentSharedCableNames.Stage.home A (W.graph.dst ((DescentSharedCableNames.Stage.stream A native).symm j.val).1) = _
    rw [original]
    exact Prod.ext rfl (A.same e.val).symm
  have node : B.peer (h,x) j.val=(z,x) := (ite_eq_left src).trans dst
  have digit : (sourceHandle A native S ready rank e).neighbor=ordinal A rank h ⟨z,wz⟩ := by
    change DescentSharedCableNames.Ends.neighborOrder (DescentSharedCableNames.Stage.near A) names _ (h,x) ⟨B.peer (h,x) j.val,_⟩=_
    convert paired A rank h x ⟨z,wz⟩ using 2
    exact Subtype.ext node
  rw [digit]
  exact rotor_at A rank h ⟨z,wz⟩

include coord named fit winner df edgeOrder in
theorem physical_walk (e : DescentSharedCableNames.Stage.Positive A) (atTarget : Bool) :
    let h:=A.pos ((N).src e.val)
    let x:=A.block ((N).src e.val)
    let v:=(sourceHandle A native S ready rank e).neighbor
    let receive:=if atTarget then (N).dst e.val else (N).src e.val
    walked next h (look (here h) (peer h) (if atTarget then v.val+1 else 0,x.val)) (key (venue (.inl receive))) := by
  let h:=A.pos ((N).src e.val);let x:=A.block ((N).src e.val);let v:=(sourceHandle A native S ready rank e).neighbor
  have issued (u : (N).Site):=old_location A native S ready names win next he rank coord named fit winner (rotor_sorted A rank)
    (rotor_routes A native S ready rank) df edgeOrder profile same lay u
  cases atTarget with
  | false=>
    exact physicalSelf next h (here h) (peer h) x _ (issued ((N).src e.val))
  | true=>
    have link:=origin_routes A native S ready rank e
    have blk : x=A.block ((N).dst e.val):=A.same e.val
    exact physicalPeer next h (A.pos ((N).dst e.val)) here v x _
      (by rw [blk]; exact issued ((N).dst e.val)) link
end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
