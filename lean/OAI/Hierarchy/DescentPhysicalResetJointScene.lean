import OAI.Hierarchy.DescentPhysicalResetSceneInputs
import OAI.Hierarchy.DescentResetPeerJointPackedPrice
import OAI.Hierarchy.DescentResetPeerJointAuxRun
import OAI.Hierarchy.DescentResetPeerJointAuxPrice
import OAI.Hierarchy.DescentResetCompactedCandidates

namespace OAI
/-! # Compact receiver rank operands from the physical current and previous rosters -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput) (base : ℕ) (old : v.OriginalOperands base)
local notation "p₀" => v.front.peer
local notation "s₀" => v.sheets
local notation "a₀" => v.actorEnd base
local notation "lo₀" => v.massEnd base
local notation "hi₀" => v.jointEnd base
local notation "R₀" => v.issuedScene base old

/-- The current roster is the four sorted RAW names written by SelfPortsRAM.
The physical reader uses the compact inverse only to find the receiver. -/
def jointRegisters : DescentResetPeerJointRAM.Sources where
  count := (R₀).count
  inverse := (R₀).inverse
  current := ((p₀).ports (v.front.peers a₀)).roster
  prior := old.oldRoster

def initialPeers : Bank :=
  ⟨(p₀).rawPeers (v.front.peers a₀),Nat.clog 2 ((p₀).hosts*4)⟩

def jointPhase (w : ℕ) : NativePhase w :=
  DescentResetPeerJointPacked.Aux.complete w lo₀ (s₀).hosts (p₀).hosts (p₀).oldHosts
    (p₀).shapes (p₀).oldDegree (s₀).groups (s₀).lanes (s₀).metaBits (v.jointRegisters base old) (v.initialPeers base)

def peerJoint (j : Fin 4) : Expr :=
  DescentResetPeerJointPacked.expr lo₀ (s₀).hosts (p₀).hosts (s₀).groups (s₀).lanes (s₀).metaBits j

def peerAux (j : Fin 4) : Expr :=
  DescentResetPeerJointPacked.Aux.expr lo₀ (s₀).hosts (p₀).hosts (s₀).groups (s₀).lanes (s₀).metaBits j

structure JointRoom (w : ℕ) : Prop where
  measured : DescentResetPeerJointRAM.Room (v.jointRegisters base old) lo₀
    (s₀).hosts (p₀).hosts (p₀).oldHosts (p₀).oldDegree w
  original : (v.initialPeers base).Fits w lo₀

set_option quotPrecheck false in
theorem peer_prefix :
    (p₀).endAddress (v.front.peers a₀)≤lo₀ := by
  have order:=v.front.front_order a₀
  have parent : (p₀).endAddress (v.front.peers a₀)≤v.front.parentStart a₀:=Nat.le_add_right ..
  have trunk : v.front.mixed a₀≤v.trunkEnd base:=by
    unfold trunkEnd CandidateFront.trunkEnd CandidateFront.gathered DescentResetTrunkIssue.endAddress
      DescentResetTrunkCompactGather.endAddress DescentResetTrunkCompactGather.geometry
      DescentResetTrunkCompactRows.endAddress DescentResetTrunkCompactRows.rowBase
    omega
  have mass : v.trunkEnd base≤lo₀ := by
    change v.trunkEnd base≤v.contactShape.endAddress (v.trunkEnd base)
    rw [v.contactShape.translate]
    exact Nat.le_add_right ..
  exact parent.trans (order.1.trans (order.2.1.trans (trunk.trans mass)))

/-- All pointer room comes from the earlier physical peer installer and the final
calendar bound. The two count bounds also cover the case of an empty old roster. -/
theorem joint_room {w : ℕ} (safe : v.front.SceneRoom a₀ R₀ w)
    (oldFit : (p₀).oldHosts<2^w) (newFit : (s₀).hosts<2^w) (high : hi₀<2^w) :
    v.JointRoom base old w := by
  let addr:=v.front.peers a₀
  have early := v.peer_prefix base
  have walk:=(p₀).ordered addr
  have portBound : (p₀).self addr≤(p₀).endAddress addr:=walk.2.2.1.trans walk.2.2.2
  have port:=DescentResetSelfPortsRAM.roster_fits ((p₀).three addr) (p₀).hosts (p₀).groups (p₀).lanes (portBound.trans_lt safe.peers.total)
  have self : (p₀).self addr≤lo₀:=portBound.trans early
  have init : addr≤lo₀:=walk.1.trans (walk.2.1.trans self)
  have up {q : Bank} {z : ℕ} (r : q.Fits w z) (h : z≤lo₀) : q.Fits w lo₀:=
    ⟨r.1,r.2.1,r.2.2.trans h⟩
  have room : DescentResetPeerJointRAM.endAddress lo₀ (s₀).hosts (p₀).hosts≤hi₀:=by
    change _≤DescentResetPeerJointRAM.endAddress _ _ _+_+_+_+_
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans
      ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))
  have priorRaw : (v.initialPeers base).base≤(p₀).three addr:=Nat.le_add_right ..
  have selfRoom : (p₀).three addr+DescentResetSelfPortsRAM.pad (p₀).hosts≤(p₀).self addr:=by
    unfold PeerAperture.self DescentResetSelfPortsRAM.endAddress DescentResetSelfPortsRAM.rankBase
      DescentResetSelfPortsRAM.rawBase DescentScalarHaloPortROM.stop DescentResetSelfPortsRAM.portBase
    omega
  have rawSize : (v.initialPeers base).base+(v.initialPeers base).size≤lo₀:=
    (Nat.add_le_add_right priorRaw _).trans (selfRoom.trans self)
  have startRoom : lo₀≤DescentResetPeerJointRAM.endAddress lo₀ (s₀).hosts (p₀).hosts :=
    (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have sizeFits := (Nat.le_add_left (v.initialPeers base).size _).trans_lt
    (rawSize.trans_lt ((startRoom.trans room).trans_lt high))
  refine ⟨?_,⟨Nat.two_pow_pos _,sizeFits,rawSize⟩⟩
  exact ⟨up safe.count early,up safe.inverse early,up port.1 self,up safe.peers.old.oldFits init,
    port.2,safe.peers.old.oldSize,oldFit,newFit,room.trans_lt high⟩

theorem joint_any {w : ℕ} (m : Memory w) (room : v.JointRoom base old w) (high : hi₀<2^w) :
    (v.jointPhase base old w).Runs m ∧ ∀z,z<lo₀ ∨ hi₀≤z → (v.jointPhase base old w).image m z=m z :=
  DescentResetPeerJointPacked.Aux.any _ _ _ _ _ room.measured room.original high

theorem peerJoint_fits {w : ℕ} (room : v.JointRoom base old w) (high : hi₀<2^w) (j : Fin 4) :
    (v.peerJoint base j).Fits w hi₀ :=by
  have end₁ : DescentResetPeerJointPacked.endAddress lo₀ (s₀).hosts (p₀).hosts (s₀).groups (s₀).lanes (s₀).metaBits≤hi₀:=
    (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact ProtocolRAMGeneratedWrite.fits_mono _ end₁ (DescentResetPeerJointPacked.fits _ room.measured (end₁.trans_lt high) j)

/-- The concrete endpoints of the charged successor-calendar operation. -/
theorem joint_calendar : DescentResetPeerJointPacked.completeEnd lo₀ (s₀).hosts (p₀).hosts
    (s₀).groups (s₀).lanes (s₀).metaBits=hi₀ :=rfl

/-- Native reads of the compact count and inverse, the actual sparse self-port
page and the full old rotor imply all four packed rank inputs on the final image. -/
theorem joint_sources_before_aux {w N : ℕ} (name : Fin N→Fin (p₀).hosts)
    (now : Fin (p₀).hosts→Fin 4→Option (Fin (p₀).hosts))
    (prior : Fin (p₀).oldHosts→Fin (p₀).oldDegree→Option (Fin (p₀).oldHosts)) (m : Memory w)
    (active : N≤(s₀).hosts) (room : v.JointRoom base old w)
    (reads : DescentResetPeerJointRAM.Reads (v.jointRegisters base old) N name now prior m)
    (distinct : ∀a i j z,prior a i=some z→prior a j=some z→i=j)
    (pos : 0<(p₀).shapes) (bitsFit : (p₀).shapes*DescentResetPeerJointRAM.radix (p₀).oldDegree≤2^(s₀).metaBits)
    (high : hi₀<2^w) (j : Fin 4) :
    Source (v.peerJoint base j) (fun (h : Fin (s₀).hosts) (_ : Fin (s₀).groups) =>
      (⟨DescentResetPeerJointRAM.value (p₀).oldHosts (p₀).shapes (p₀).oldDegree prior N name now h j,
        DescentResetPeerJointRAM.value_lt prior name now h j distinct pos bitsFit⟩ : Cell (s₀).metaBits))
      (s₀).lanes ((DescentResetPeerJointPacked.phase w lo₀ (s₀).hosts (p₀).hosts (p₀).oldHosts
      (p₀).shapes (p₀).oldDegree (s₀).groups (s₀).lanes (s₀).metaBits (v.jointRegisters base old)).image m) :=
  (DescentResetPeerJointPacked.run _ _ _ _ name now prior _ active room.measured reads distinct pos bitsFit
    (((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans_lt high)).2.1 j

theorem aux_fits {w : ℕ} (high : hi₀<2^w) (j : Fin 4) : (v.peerAux base j).Fits w hi₀ :=
  DescentResetPeerJointPacked.Aux.expr_fits _ _ _ _ _ _ j high

theorem joint_sources {w N : ℕ} (name : Fin N→Fin (p₀).hosts)
    (now : Fin (p₀).hosts→Fin 4→Option (Fin (p₀).hosts))
    (prior : Fin (p₀).oldHosts→Fin (p₀).oldDegree→Option (Fin (p₀).oldHosts))
    (near : Fin (p₀).hosts→Fin 3→Option (Fin (p₀).hosts)) (m : Memory w)
    (active : N≤(s₀).hosts) (room : v.JointRoom base old w)
    (reads : DescentResetPeerJointRAM.Reads (v.jointRegisters base old) N name now prior m)
    (original : ∀h i,m ((v.initialPeers base).base+(i:Fin 3).val*(p₀).hosts+(h:Fin (p₀).hosts).val)=
      (((near h i).elim (p₀).hosts Fin.val : ℕ) : Word w))
    (distinct : ∀a i j z,prior a i=some z→prior a j=some z→i=j)
    (pos : 0<(p₀).shapes) (bitsFit : (p₀).shapes*DescentResetPeerJointRAM.radix (p₀).oldDegree≤2^(s₀).metaBits)
    (signFit : 2*((p₀).oldDegree+1)≤2^(s₀).metaBits) (high : hi₀<2^w) :
    let image:=(v.jointPhase base old w).image m
    (∀j,Source (v.peerJoint base j) (fun (h : Fin (s₀).hosts) (_ : Fin (s₀).groups) =>
      (⟨DescentResetPeerJointRAM.value (p₀).oldHosts (p₀).shapes (p₀).oldDegree prior N name now h j,
        DescentResetPeerJointRAM.value_lt prior name now h j distinct pos bitsFit⟩ : Cell (s₀).metaBits)) (s₀).lanes image) ∧
    ∀j,Source (v.peerAux base j) (fun (h : Fin (s₀).hosts) (_ : Fin (s₀).groups)=>
      (⟨DescentResetPeerJointPacked.Aux.value (p₀).shapes name prior near h j,
        DescentResetPeerJointPacked.Aux.value_lt (p₀).shapes name prior near h j distinct pos bitsFit signFit⟩ :
        Cell (s₀).metaBits)) (s₀).lanes image := by
  have span : 3*(p₀).hosts≤(v.initialPeers base).size:=
    (by nlinarith : 3*(p₀).hosts≤(p₀).hosts*4).trans (Nat.le_pow_clog (by decide) _)
  have run:=DescentResetPeerJointPacked.Aux.run lo₀ (p₀).shapes (v.jointRegisters base old) (v.initialPeers base)
    name now prior near m active room.measured room.original span reads original distinct pos bitsFit signFit high
  exact ⟨run.2.1,run.2.2.1⟩

theorem peerJoint_price (w : ℕ) :
    let q:=v.jointPhase base old w
    q.ticks+DescentStaticWordColumn.names q.program≤18000*((s₀).hosts+1)*((p₀).oldDegree+1)+150*((p₀).hosts+1)+
      25*DescentResetPeerJointBroadcast.count (s₀).hosts (s₀).groups (s₀).lanes (s₀).metaBits+38 :=
  DescentResetPeerJointPacked.Aux.priced ..

theorem peerJoint_price_before_aux (w : ℕ) :
    let q:=DescentResetPeerJointPacked.phase w lo₀ (s₀).hosts (p₀).hosts (p₀).oldHosts
      (p₀).shapes (p₀).oldDegree (s₀).groups (s₀).lanes (s₀).metaBits (v.jointRegisters base old)
    q.ticks+DescentStaticWordColumn.names q.program≤
      9000*((s₀).hosts+1)*((p₀).oldDegree+1)+150*((p₀).hosts+1)+
        25*DescentResetPeerJointBroadcast.count (s₀).hosts (s₀).groups (s₀).lanes (s₀).metaBits+19 :=
  DescentResetPeerJointPacked.priced ..

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
