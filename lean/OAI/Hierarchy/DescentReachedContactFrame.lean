import OAI.Hierarchy.DescentCanonicalPeerProgram
import OAI.Hierarchy.DescentPhysicalResetTrunkScene
import OAI.Hierarchy.DescentPhysicalPeerProbe

namespace OAI
/-! # Reached donor and marker words survive the physical reset trunk -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty.Chronology ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

theorem marker_trunk_frame (v : CandidateFront) (base : ℕ) (s : v.Scene) {w : ℕ}
    (safe : v.SceneRoom base s w) (m : Memory w) (room : v.trunkEnd base<2^w)
    (a : ℕ) (before : a<v.peers base) :
    (v.trunkScene base s safe).image m a = v.prePeers base s safe m a := by
  have peers:=(v.peer_boundaries base s safe).2.2.2
  have parent : v.peer.endAddress (v.peers base) ≤ v.parentStart base := Nat.le_add_right ..
  have aperture : v.parentStart base≤v.parentEnd base := by
    unfold parentEnd
    rw [DescentResetParentAperture.extent]
    omega
  have proj : v.parentEnd base≤v.projected base := by
    unfold projected
    rw [DescentResetStemProject.extent]
    omega
  have mixed' : v.projected base≤v.mixed base := by
    unfold mixed
    rw [DescentResetStemPackedIssue.Mixed.affine]
    omega
  exact (v.trunkScene_before base s safe m room a (before.trans_le
    (peers.trans (parent.trans (aperture.trans (proj.trans mixed')))))).trans
      ((v.retained_cuts base s safe m).2.2.1 a before)

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentSIMDLookup
open DescentContactDonorFront DescentResetLocalRoster ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (oldM nextM field metaBits : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR calendar
local notation "H" => S.hostSize i
local notation "Ht" => GroupStage.depthBound D n f g
local notation "cap" => (calendar.take i).prod*256
local notation "r" => B.reset.k-B.terminals.commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster B.reset.graph r Ht).card
local notation "bits" => (A).peer.bits
local notation "donor" => peerDonorShape B H oldM field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
variable (paid : input.placement.cap=(calendar.take i).prod*256) (floor : ℕ) (old : EarlierBanks D k ((calendar.take i).prod*256) n)
local notation "eqShape" => canonical_donor B oldM nextM field metaBits calendar paid
local notation "U" => (Shape.move eqShape old.donor)
local notation "next" => (A).oldKeys floor
local notation "L" => peerLayout B next H oldM (A).privateBits ((A).stemField+2) bits
local notation "lo" => (L).endAddress
local notation "e" => calendarOriginals S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR
  calendar floor old
variable (flags count inverse : Bank) {w : ℕ}
local notation "scene" => (A).fromOriginals floor e flags count inverse



local notation "markers₀" => (donor).markers lo shelf bits
local notation "markerRoom" dr:arg en:arg pk:arg => (donor).markerSpace lo shelf bits U dr en pk
local notation "early" => RawTables.image B.reset.graph r Ht L (peerTemplate B)
local notation "actual" dr:arg en:arg pk:arg => (donor).result lo shelf bits U B.reset.graph dr en pk

/-- The calculation on the canonical graph starts in exactly the memory reached
after the reset's earlier raw evidence tables. -/
theorem reached_donor_entry (room : (A).SceneRoom floor scene w) (m : Memory w) :
    (A).preDonors floor scene room m = early ((A).probeStart floor scene m) := by
  let keyMem := (A).probeStart floor scene m
  have shape := canonical_peer_layout B oldM nextM field metaBits calendar floor
  have preRoom : ((A).rawTables floor).endAddress<2^w :=
    ((A).tables_end floor room.sameLanes).trans_lt room.evidenceFit
  have tableRoom : (L).endAddress<2^w := shape ▸ preRoom
  apply ProtocolRAM.exec_unique (RawTables.program B.reset.graph r Ht L (peerTemplate B) w) keyMem
    _ _ (n := ((A).rawTables floor).ticks) (k := (L).ticks)
  · rw [←canonical_raw_program B oldM nextM field metaBits calendar floor old w]
    exact (RawTables.any (e).evidence.board (e).evidence.rootBits (e).evidence.depth
      ((A).rawTables floor) (e).evidence.template keyMem preRoom).1
  · exact (RawTables.any B.reset.graph r Ht L (peerTemplate B) keyMem tableRoom).1

/-- The concrete calendar slice supplies the low frame used by every late
contact operand, including addresses of previously issued sender columns. -/
theorem reached_contact_trunk_frame (room : (A).SceneRoom floor scene w)
    (donorRoom : (donor).Space lo U w)
    (end_ : (markers₀).endAddress<2^w)
    (packed : oldM*max (field*8) bits≤w/2) (m : Memory w) (trunkRoom : (A).trunkEnd floor<2^w)
    (a : ℕ) (prior : a<(markers₀).endAddress) :
    ((A).trunkScene floor scene room).image m a =
      (actual donorRoom end_ packed) (early ((A).probeStart floor scene m)) a := by
  have cutoff : (A).peers floor=(markers₀).endAddress :=
    congrArg DescentContactPreROM.Layout.endAddress (canonical_contact_layout B oldM nextM field metaBits calendar paid floor)
  have before : a<(A).peers floor:=by rwa [cutoff]
  rw [(A).marker_trunk_frame floor scene room m trunkRoom a before]
  let rawMem:=(A).preDonors floor scene room m
  have issued : (((A).donorPhase floor scene room).program.seq
      ((A).contactPhase floor scene room).program).Exec rawMem ((A).prePeers floor scene room m) _ :=
    Procedure.Exec.then (((A).donor.any ((A).donorStart floor) (scene).donor room.donor rawMem).1)
      ((((A).contactLayout floor).any (scene).rotor (scene).boardReads
        ((A).sensor floor scene) room.contact ((A).preContacts floor scene room m)).1)
  rw [canonical_donor_program B oldM nextM field metaBits calendar paid floor old flags count inverse room,
      canonical_contact_program B oldM nextM field metaBits calendar paid floor old flags count inverse room (markerRoom donorRoom end_ packed)] at issued
  have equal := ProtocolRAM.exec_unique _ rawMem _ _ issued
    ((donor).period_any lo shelf bits U B.reset.graph donorRoom end_ packed rawMem).1
  change (A).prePeers floor scene room m a=_
  rw [equal]
  exact congrArg (fun t => (actual donorRoom end_ packed) t a) (reached_donor_entry B oldM nextM field metaBits calendar
    floor old flags count inverse room m)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
