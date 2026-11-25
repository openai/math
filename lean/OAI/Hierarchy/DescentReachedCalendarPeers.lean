import OAI.Hierarchy.DescentCanonicalPeerProgram

namespace OAI
/-! # The three genuine observed raw peers survive on the compact trunk scalar input -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentSIMDLookup
open DescentGroupPeerOrder DescentPackedZip DescentContactDonorFront DescentResetLocalRoster ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
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


local notation "pitch" => H*shelf
local notation "D₀" => input.placement.degree
local notation "srcBase" => (CA).endAddress
local notation "scratch_" => Program.scratchAt srcBase H shelf D₀ (peerEvidenceRows B) bits oldM
local notation "rawAddress" => outBase scratch_ pitch (Candidates.count shelf D₀)

include paid in
theorem canonical_three_address :
    (A).peer.rawPeers ((A).peers floor)=rawAddress := by
  let P:=(A).peer
  have shape : P.shapes=shelf:=B.public_hub_slots.symm
  have deg : P.oldDegree=D₀:=input.branch.symm
  have num : P.evidence=peerEvidenceRows B:=(canonical_probes B oldM nextM field metaBits calendar paid).1
  have rawSize:=canonical_raw_hosts B oldM nextM field metaBits calendar
  have begin_ : (A).peers floor=srcBase:=congrArg DescentContactPreROM.Layout.endAddress
    (canonical_contact_layout B oldM nextM field metaBits calendar paid floor)
  change outBase (Program.scratchAt ((A).peers floor) H P.shapes P.oldDegree P.evidence bits oldM)
    P.hosts (Candidates.count P.shapes P.oldDegree)=_
  rw [begin_,shape,deg,num,rawSize]

variable (old : EarlierBanks D k cap n)
local notation "sensors" => Shape.move eqShape old.donor
local notation "incoming" => canonical_peer_inputs B oldM nextM field metaBits calendar paid floor old
local notation "early" => calendarOriginals S ctl.board k tail i D f g oldM nextM field metaBits C ctl.bitsR
  calendar floor old
variable (flags countBank inverse : Bank) {w : ℕ}
local notation "scene" => (A).fromOriginals floor early flags countBank inverse
variable (safe : (A).SceneRoom floor scene w) (initial : Memory w)
local notation "keyMem" => (A).probeStart floor scene initial
local notation "firstOut" => RawTables.image B.reset.graph r Ht L (peerTemplate B) keyMem
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "pad" => input.valid.host
local notation "padded" => (B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad)
local notation "named" => (Z).rawHostRank T padded
local notation "unitBits" => (A).privateBits
local notation "keyBits" => ((A).stemField+2)
variable (donorRoom : (donor).Space lo sensors w) (ends : srcBase<2^w)
    (packedMarker : oldM*max (field*8) bits≤w/2)
local notation "mr" => (donor).markerSpace lo shelf bits sensors donorRoom ends packedMarker
variable {pCount : ℕ} (prior : PriorPeerWords B H unitBits keyBits) (unit : 0 < (Z).unit)
    (panel : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel Ht pCount)
    (peers : Fin H→Fin D₀→Option (Fin H))
    (xs : Fin H→Fin rowCnt→Fin (DescentOldContactSender.count D₀ (donor).lows
      (donor).cap (donor).n (donor).residual)→Cell field)
    (raw : Fin (donor).lows→Fin (2*(donor).cap)→Fin H→Fin rowCnt→Cell field)
    (setup : (senderDesk B field).Inputs)
local notation "hosts" => input.vertex.trans (Fin.castLEEmb pad)
local notation "gr" => Function.Embedding.refl (Fin (S.groupCount i))
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k (DescentStageEdgeReceipt.groupRank
  ((gr).trans Fin.valEmbedding) ((hosts).trans Fin.valEmbedding))
local notation "native" => input.order.trans Fin.valEmbedding
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "words" => S.resetInputDigits ctl.base ctl.radix i

include donorRoom ends packedMarker in
theorem reached_peer_registers
    (measured : ∀v l,DescentOldContactSender.decode (xs (hosts v) l)=(senderDesk B field).sample setup v l)
    (signed : ∀v l lowDigit j,raw lowDigit j (hosts v) l=DescentResetOppositePayload.widened D₀ input.placement.cap field
      (DescentSharedCableNames.Stage.signedPanel input.placement native S input.valid names
        (DescentIssuedFallbackPanel.donor words B.frame.basis small v l lowDigit) j))
    (coded : DescentSignedCableCodec.width D₀ input.placement.cap≤field) (wordPositive : 0<field)
    (positions : OldPeerReads B next H oldM unitBits keyBits incoming prior keyMem)
    (origins : PeerOrigins B pad prior unit panel)
    (rosterRead : ∀(v : input.V) j,peers ((input.vertex v).castLE pad) j=
      (hostRoster input.placement (input.vertex.trans Fin.valEmbedding) v j).map (fun a=>(input.vertex a).castLE pad))
    (portFit : (incoming).oldPorts.Fits w next) (portSize : H*D₀ ≤ (incoming).oldPorts.size)
    (portRead : ∀(h : Fin H) (j : Fin D₀),keyMem ((incoming).oldPorts.base+(h.val*D₀+j.val))=(target (peers h j):Word w))
    (donorPacked : ((donor).sender lo).Packed w)
    (donorPrior : ((donor).sender lo).Before sensors xs peers raw firstOut)
    (boardWidth : oldM*max (field*(CA).oldFields) (CA).viewBits ≤ w/2)
    (shapeWidth : shelf ≤ 2^field) (markerWidth : (D₀+1)*shelf < 2^bits) (room : (Program.endAddress srcBase H shelf D₀ (peerEvidenceRows B) bits oldM) < 2^w) :
    ∃found : Fin pitch→Fin 3→Option (Fin pitch),
      (∀(v : Fin pitch) (j : Fin 3),(A).preScalar floor scene safe initial
        ((A).peer.rawPeers ((A).peers floor)+j.val*pitch+v.val)=(target (found v j):Word w)) ∧
      (∀v : B.next.V,DescentSortedRoster.present (selfPeers found) (named v)=(insert v ((Z).emittedNear T v)).map named) ∧
      (∀v : B.next.V,(∀j,found (named v) j≠some (named v)) ↔ v∉(Z).emittedNear T v) := by
  have observed:=issued_peer_directory_reached B next H oldM unitBits keyBits bits field
    (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) incoming sensors donorRoom ends packedMarker keyMem pad prior unit
    panel peers xs raw setup measured signed coded wordPositive positions origins rosterRead portFit portSize
    portRead donorPacked donorPrior boardWidth shapeWidth markerWidth room
  obtain ⟨exec,_,⟨found,read,real,loops⟩,_⟩:=observed
  have printed:=canonical_peer_program B oldM nextM field metaBits calendar paid floor old
    flags countBank inverse safe mr
  obtain ⟨ticks,physical⟩:=(A).probe_exec floor scene safe initial
  rw [printed] at physical
  have same:=ProtocolRAM.exec_unique _ _ _ _ exec physical
  have dim:=canonical_raw_hosts B oldM nextM field metaBits calendar
  have addr:=canonical_three_address B oldM nextM field metaBits calendar paid floor
  refine ⟨found,?_,real,loops⟩
  intro v j
  let key:=Fin.cast dim.symm v
  have keep:=(A).peer.three_word (scene).peers ((A).peers floor) ((A).prePeers floor scene safe initial) safe.peers j key
  change (A).preScalar floor scene safe initial _=(A).probeMemory floor scene safe initial _ at keep
  simp only [key,Fin.val_cast,dim] at keep
  rw [keep,←same,addr]
  exact read v j

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
