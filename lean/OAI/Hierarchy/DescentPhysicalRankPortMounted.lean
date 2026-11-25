import OAI.Hierarchy.DescentRankPortMounted
import OAI.Hierarchy.DescentPhysicalBeforeRankPorts
import OAI.Hierarchy.DescentPhysicalResetActorOutput

namespace OAI
/-! # Read the reset rank ports from the same memory as the whole physical date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty DescentSixParty.Chronology DescentSortedRoster DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w) (ok : u.Ready)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "F₀" => (v).front
local notation "E" => (v).actorEnd b
local notation "S₀" => (v).issuedScene b u.earlier
local notation "T₀" => (v).trunkEnd b
local notation "M₀" => (v).massEnd b
local notation "don" => (F₀).donorStart E
local notation "B₀" => (v).rankPortRegs b
local notation "s₀" => (v).sheets
local notation "P₀" => (v).front.peer.hosts

theorem before_ports_actor (m : Memory w) (j : ℕ) (below : j<E) :
    u.before_ports ok m j=m j:=by
  have earlier:=ok.ordered.2.2.1
  have order:=ok.ordered.2.2.2.1
  have scene:=(F₀).trunkScene_any E S₀ u.sceneFits m ok.trunk
  have contact:=(v).contactShape.actual don T₀ (S₀).donor u.sceneFits.donor ok.donors ok.mass
    ok.projectionLanes ok.projectionBlocks (((F₀).trunkScene E S₀ u.sceneFits).image m)
  exact (u.before_ports_frame ok m j (below.trans_le (earlier.trans order))).trans
    ((contact.2.2 j (.inl (below.trans_le earlier))).trans (scene.2 j (.inl below)))

/-- The four rank registers come from the actual contact readout and the one
forward rank deposited by the preceding actor directory. -/
theorem reached_rank_ports {N O D : ℕ} (m : Memory w) (names : Fin N↪Fin P₀) (bound : N≤(s₀).hosts)
    (peers : Fin P₀→Fin 4→Option (Fin P₀)) (old : Fin O→Fin D→Option (Fin O))
    (inc : StrictMono names) (closed : ∀u y,y∈present peers (names u)→∃rowId,names rowId=y)
    (snap : DescentResetPeerJointRAM.Reads ((v).jointRegisters b u.earlier) N names (indexed peers) old
      (u.contactResult m)) (forward : ∀rowId:Fin N,m ((B₀).forward.base+(names rowId).val)=(rowId.val:Word w)) :
    Mounted ((v).rankPorts b) (indexed (Compact.pull names bound peers))
      (((v).rankPortPhase b w).image (u.before_ports ok m)) (s₀).groups (s₀).lanes:=by
  apply (v).rankPort_compact_of_reads b names bound peers inc closed (u.before_ports ok m) ok.rankPorts
    (u.contactResult m) ((v).jointRegisters b u.earlier) old snap rfl rfl rfl M₀ (u.before_ports_frame ok m)
    ok.joints.measured.count ok.joints.measured.inverse ok.joints.measured.current
  intro z
  have fit:=u.actor_rank_space ok
  have size:=(names z).isLt.trans_le ok.rankPorts.roster.forwardSize
  exact (u.before_ports_actor ok m _ ((Nat.add_lt_add_left size _).trans_le fit.2.2)).trans (forward z)

/-- The raw chart may be expressed in the measured reset family's equal
aperture, while the compact peer array itself is independent of that cast. -/
theorem reached_rank_ports_cast {N O D P : ℕ} (rawRoom : P₀=P) (m : Memory w)
    (names : Fin N↪Fin P) (bound : N≤(s₀).hosts) (peers : Fin P→Fin 4→Option (Fin P))
    (old : Fin O→Fin D→Option (Fin O)) (inc : StrictMono names)
    (closed : ∀u y,y∈present peers (names u)→∃rowId,names rowId=y)
    (snap : DescentResetPeerJointRAM.Reads ((v).jointRegisters b u.earlier) N names (indexed peers) old
      (u.contactResult m)) (forward : ∀z:Fin N,m ((B₀).forward.base+(names z).val)=(z.val:Word w)) :
    Mounted ((v).rankPorts b) (indexed (Compact.pull names bound peers))
      (((v).rankPortPhase b w).image (u.before_ports ok m)) (s₀).groups (s₀).lanes:=by
  subst P
  exact u.reached_rank_ports ok m names bound peers old inc closed snap forward

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
