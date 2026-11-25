import OAI.Hierarchy.DescentPhysicalResetDateOperands
import OAI.Hierarchy.DescentReachedContactFrame

namespace OAI
/-! # Authentic private pages through the peer, trunk, contact and joint publication -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip DescentResetLocalRoster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "V₀" => a.successor
local notation "b₀" => a.rebased floor
local notation "F₀" => (V₀).front
local notation "start₀" => (V₀).actorEnd b₀
local notation "S₀" => (V₀).issuedScene b₀ u.earlier
local notation "C₀" => (F₀).contactLayout start₀
local notation "first₀" => (V₀).trunkEnd b₀
local notation "mass₀" => (V₀).massEnd b₀
local notation "joint₀" => (V₀).jointEnd b₀
local notation "D₀" => (V₀).privateShape
local notation "don₀" => (F₀).donorStart start₀
local notation "trunk₀" => (F₀).trunkScene start₀ S₀ u.sceneFits
local notation "pre₀" m => (F₀).prePeers start₀ S₀ u.sceneFits m
local notation "held₀" m => (F₀).preScalar start₀ S₀ u.sceneFits m

def privateStart (m : Memory w) : Memory w :=
  ((V₀).jointPhase b₀ u.earlier w).image
    ((V₀).contactShape.issuedImage don₀ first₀ (S₀).donor ((trunk₀).image m))

theorem privateStart_frame (ok : u.Ready) (m : Memory w) (z : ℕ) (before : z<(F₀).peers start₀) :
    u.privateStart m z=(held₀ m) z :=by
  let scene:=(trunk₀).image m
  let pub:=(V₀).contactShape.issuedImage don₀ first₀ (S₀).donor scene
  have fit:=(F₀).marker_trunk_frame start₀ S₀ u.sceneFits m ok.trunk z before
  have peers:=(F₀).peer_boundaries start₀ S₀ u.sceneFits
  have toTrunk : (F₀).peers start₀≤first₀:=by
    have body:=(F₀).front_order start₀
    have step : (F₀).peer.endAddress ((F₀).peers start₀)≤(F₀).parentStart start₀:=Nat.le_add_right ..
    have mixed : (F₀).mixed start₀≤first₀ := by
      unfold ResetOutput.trunkEnd CandidateFront.trunkEnd CandidateFront.gathered DescentResetTrunkIssue.endAddress
        DescentResetTrunkCompactGather.endAddress DescentResetTrunkCompactGather.geometry
        DescentResetTrunkCompactRows.endAddress DescentResetTrunkCompactRows.rowBase
      omega
    exact peers.2.2.2.trans (step.trans (body.1.trans (body.2.1.trans mixed)))
  have q : z<first₀:=before.trans_le toTrunk
  have j:=((V₀).joint_any b₀ u.earlier pub ok.joints ok.packed).2 z
    (.inl (q.trans_le ok.ordered.2.2.2.1))
  have c:=((V₀).contactShape.actual don₀ first₀ (S₀).donor u.sceneFits.donor ok.donors ok.mass
    ok.projectionLanes ok.projectionBlocks scene).2.2 z (.inl q)
  have atPeer:=((F₀).peer.any (S₀).peers ((F₀).peers start₀) (pre₀ m) u.sceneFits.peers).2.1 z (.inl before)
  exact j.trans (c.trans (fit.trans atPeer.symm))

theorem privateStart_source (ok : u.Ready) (m : Memory w) {H G b M : ℕ} (e : Expr)
    (values : Fin H→Fin G→Cell b) (earlier : e.Fits w ((F₀).peers start₀))
    (stored : Source e values M (held₀ m)) : Source e values M (u.privateStart m) :=by
  intro p
  exact (eval_below e _ (held₀ m) _ earlier (u.privateStart_frame ok m)).trans (stored p)

/-- The pitch lookups only touch the original physical prefix under markerBase.
The post-contact prePeers image is exactly the original native marker scan. -/
theorem privateStart_pitch (ok : u.Ready) (m : Memory w) (z : ℕ) (early : z<(C₀).markerBase) :
    u.privateStart m z=(pre₀ m) z:=by
  have before : z<(F₀).peers start₀:=early.trans_le ((C₀).ordered.2.2.2.1.trans (C₀).ordered.2.2.2.2)
  have atPeer:=((F₀).peer.any (S₀).peers ((F₀).peers start₀) (pre₀ m) u.sceneFits.peers).2.1 z (.inl before)
  exact (u.privateStart_frame ok m z before).trans atPeer

def privateResult (m : Memory w) := (D₀).final joint₀ C₀ u.earlier.pages (u.privateStart m)

/-- The reached predecessor's packed five-field pages suffice to determine every
private candidate operand in the same actual dated RAM used by the rank scanner. -/
theorem captured_private_pages (ok : u.Ready) (m : Memory w)
    (words : Bool→Root (D₀).residual (D₀).ports→Fin (C₀).hosts→Fin (C₀).groups→Cell (D₀).panels)
    (earlier : ∀s t,(u.earlier.pages s t).Fits w ((F₀).peers start₀))
    (initial : ∀s t,Source (.lookup (u.earlier.pages s t) .row) (words s t) (D₀).oldBatch (held₀ m))
    (oldPos : 0<(D₀).oldBatch) (batchEq : (D₀).oldBatch=(C₀).batch)
    (hostEq : (D₀).oldHosts*(D₀).shapes=(C₀).hosts*(C₀).shapes)
    (laneEq : (D₀).groups*(D₀).blocks=(C₀).groups)
    (key : Fin (D₀).keys) (j : Fin 3) (x : Fin (D₀).blocks) :
    Source ((D₀).operand joint₀ key j x) (fun v g=>
      (D₀).measured C₀ words key j (v.cast hostEq) ((finProdFinEquiv (g,x)).cast laneEq))
      (D₀).batch (u.privateResult m) :=by
  have bound:=(F₀).peer_boundaries start₀ S₀ u.sceneFits
  have mark : (C₀).markerBase≤((F₀).peers start₀):=(C₀).ordered.2.2.2.1.trans (C₀).ordered.2.2.2.2
  have prev:=mark.trans (bound.2.2.2.trans (((V₀).peer_prefix b₀).trans ((V₀).receipt_order b₀).1))
  have old s t:=u.privateStart_source ok m (.lookup (u.earlier.pages s t) .row) (words s t)
    ⟨earlier s t,trivial⟩ (initial s t)
  exact (D₀).projected_original joint₀ C₀ u.earlier.pages (S₀).rotor (S₀).boardReads ((F₀).sensor start₀ S₀)
    u.sceneFits.contact ((F₀).preContacts start₀ S₀ u.sceneFits m) (u.privateStart m) (u.privateStart_pitch ok m)
    prev batchEq hostEq laneEq ok.pages oldPos ok.projectionLanes ok.projectionBlocks ok.privates words old key j x


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
