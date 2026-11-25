import OAI.Hierarchy.DescentCanonicalDonorProgram
import OAI.Hierarchy.DescentPhysicalPeerProbe

namespace OAI
/-! # Equality of the complete calendar peer scan and the reached four-family catalogue -/
namespace Hierarchy.DescentResetPeerUnionRAM.PeerCatalog
open DescentSIMDLookup ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
def inspect (L : RawTables.Layout) (C : DescentContactPreROM.Layout) (b : Banks C) (old : Bank) (w : ℕ) :=
  Program.program w C.endAddress C.hosts C.shapes C.degree C.outputBits C.batch C.groups old marked
    (terms L C b).all

def move {C A : DescentContactPreROM.Layout} (equal : C=A) (b : Banks C) : Banks A := equal ▸ b

private theorem restore_banks {C : DescentContactPreROM.Layout} (b : Banks C) :
    (⟨b.keys, b.pages, b.actorStarts, b.actorData⟩ : Banks C) = b := rfl

theorem inspect_congr {L R : RawTables.Layout} {C A : DescentContactPreROM.Layout}
    (slots : L=R) (area : C=A) (b : Banks C) (old : Bank) (w : ℕ) :
    inspect L C b old w=inspect R A (move area b) old w := by
  subst A;subst R;rfl
end
end Hierarchy.DescentResetPeerUnionRAM.PeerCatalog

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentSIMDLookup
open DescentContactDonorFront DescentResetLocalRoster ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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
variable (paid : input.placement.cap=cap) (floor : ℕ)
local notation "eqShape" => canonical_donor B oldM nextM field metaBits calendar paid
local notation "next" => (A).oldKeys floor
local notation "L" => peerLayout B next H oldM (A).privateBits ((A).stemField+2) bits
local notation "lo" => (L).endAddress
local notation "start" => (donor).endAddress lo
local notation "CA" => contactLayout B start H oldM field bits
local notation "rowCnt" => 2^B.terminals.commonDepth

include paid in
theorem canonical_contact_layout : (A).contactLayout floor=CA := by
  have end_ : (A).donorEnd floor=start :=
    congrArg₂ Shape.endAddress eqShape (canonical_raw_end B oldM nextM field metaBits calendar floor)
  exact (canonical_contact B oldM nextM field metaBits calendar paid floor).trans
    (congrArg (fun t=>contactLayout B t H oldM field bits) end_)

variable (old : EarlierBanks D k cap n)
local notation "books" => (A).originalPages floor old.roots old.actorStarts old.actorData
local notation "newBook" => PeerCatalog.move (canonical_contact_layout B oldM nextM field metaBits calendar paid floor) books
local notation "e" => calendarOriginals S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR
  calendar floor old
def canonical_peer_inputs : PeerInputs B :=
  ⟨(newBook).keys,(newBook).pages,(newBook).actorStarts,(newBook).actorData,old.oldRoster⟩
local notation "incoming" => canonical_peer_inputs B oldM nextM field metaBits calendar paid floor old
local notation "U" => Shape.move eqShape old.donor
local notation "terms" => peerTerms B next H oldM (A).privateBits ((A).stemField+2) bits field start incoming
variable (flags count inverse : Bank) {w : ℕ}
local notation "scene" => (A).fromOriginals floor e flags count inverse
variable (safe : (A).SceneRoom floor scene w)
local notation "prior" => (scene).peers

theorem canonical_query_program :
    Program.program w ((A).peers floor) (A).peer.oldHosts (A).peer.shapes (A).peer.oldDegree bits
        (A).peer.evidenceLanes (A).peer.evidenceGroups (prior).old (prior).test (prior).src=
      Program.program w (CA).endAddress H shelf input.placement.degree bits oldM rowCnt
        (incoming).oldPorts marked (terms).all := by
  erw [peerTerms_public]
  let transfer := PeerCatalog.inspect_congr (canonical_peer_layout B oldM nextM field metaBits calendar floor)
    (canonical_contact_layout B oldM nextM field metaBits calendar paid floor) books old.oldRoster w
  refine Eq.trans ?_ (transfer.trans ?_)
  · unfold PeerCatalog.inspect
    dsimp only [CandidateFront.fromOriginals, CandidateFront.compiledPeers, calendarOriginals]
    rfl
  · unfold PeerCatalog.inspect canonical_peer_inputs
    dsimp only
    simp only [PeerCatalog.restore_banks, contactLayout]
    rfl

theorem canonical_peer_program
    (space : ((donor).markers lo shelf bits).Space ((donor).oldBoard U) ((donor).priorSensor lo) w) :
    (A).probeProgram floor scene safe=
      directoryCode B next H oldM (A).privateBits ((A).stemField+2) bits field
        (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) incoming ((donor).oldBoard U) U space := by
  exact congrArg₂ Procedure.seq
    (congrArg₂ Procedure.seq
      (congrArg₂ Procedure.seq (canonical_raw_program B oldM nextM field metaBits calendar floor old w)
        (canonical_donor_program B oldM nextM field metaBits calendar paid floor old flags count inverse safe))
      (canonical_contact_program B oldM nextM field metaBits calendar paid floor old flags count inverse safe space))
    (canonical_query_program B oldM nextM field metaBits calendar paid floor old flags count inverse)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
