import OAI.Hierarchy.DescentCalendarPrivateField

namespace OAI
/-! # Normalizing the numeric dimensions of the current and predecessor rosters -/
namespace Hierarchy.DescentResetPeerJointRAM
open DescentSortedRoster DescentResetPeerUnionRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {O D P O' D' P' w H N : ℕ}
  (o : O=O') (d : D=D') (p : P=P') (old : Fin O'→Fin D'→Option (Fin O'))
  (names : Fin N→Fin P') (near : Fin P'→Fin 3→Option (Fin P'))
local notation "past" => (fun (v : Fin O) (j : Fin D)=>(old (v.cast o) (j.cast d)).map (Fin.cast o.symm))
local notation "rawNames" => (fun (v : Fin N)=>(names v).cast p.symm)
local notation "peers" => (fun (v : Fin P) (j : Fin 3)=>(near (v.cast p) j).map (Fin.cast p.symm))

theorem reads_cast (a : Sources) (m : Memory w)
    (s : Reads a N rawNames (indexed (selfPeers peers)) past m) :
    Reads a N names (indexed (selfPeers near)) old m:=by
  subst O'; subst D'; subst P'; simpa using s

theorem value_cast (k : ℕ) (h : Fin H) (j : Fin 4) :
    value O k D past N rawNames (indexed (selfPeers peers)) h j=
      value O' k D' old N names (indexed (selfPeers near)) h j:=by
  subst O'; subst D'; subst P'; simp

theorem aux_cast (k : ℕ) (h : Fin H) (j : Fin 4) :
    DescentResetPeerJointPacked.Aux.value k rawNames past peers h j=
      DescentResetPeerJointPacked.Aux.value k names old near h j:=by
  subst O'; subst D'; subst P'; simp

end
end Hierarchy.DescentResetPeerJointRAM

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

local notation "R₀" => measured_menu B oldBatch batch calendar I cal pad prior xs raw near
local notation "host₁" => DescentSharedCableNames.Stage.Host (Fin gs) B.next.V k
local notation "named₀" => (Z).rawHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))
local notation "s₀" => (v₀).sheets


local notation "regs₀" => (v₀).jointRegisters base₀ I.earlier
local notation "real₀" => compactActorName B pad
local notation "rows₀" => DescentResetPeerUnionRAM.selfPeers near
variable (m : Computability.VPVNP.BurstRAM.Memory bw) (seen : PhysicalReset.DateInputs.CaptureRoom (R₀) m)

include seen in
/-- The genuine current word belongs to the reached receiver and its own preceding port order. -/
theorem measured_rank_registers :
    DescentResetPeerJointRAM.Reads regs₀ used real₀ (indexed rows₀) adj_ (I.contactResult m) :=
  DescentResetPeerJointRAM.reads_cast cal.oldCount cal.oldDegree cal.peerSlots adj_ real₀ near
    regs₀ (I.contactResult m) seen.roster

include cal in
theorem measured_rank_limits (ok : I.Ready) :
    DescentResetPeerJointRAM.Room regs₀ ((v₀).massEnd base₀) I.masked.hosts rawSize H (A).degree bw :=by
  have bounds:=ok.joints.measured
  rw [cal.peerSlots,cal.oldCount,cal.oldDegree] at bounds
  exact bounds

include seen in
/-- Both word families on the compact output are indexed in the genuine sorted host order. -/
theorem measured_rank_values (hostId : Fin I.masked.hosts) (groupId : Fin I.masked.groups) (j : Fin 4) :
    ((R₀).capturedChannels.peer j hostId groupId).val=DescentResetPeerJointRAM.value H shelf (A).degree
      adj_ used real₀ (indexed rows₀) hostId j ∧
    ((R₀).capturedChannels.aux j hostId groupId).val=DescentResetPeerJointPacked.Aux.value shelf real₀ adj_ near hostId j:=by
  obtain ⟨peer,aux⟩:=(R₀).scalar_at m seen hostId groupId j
  have hp:=DescentResetPeerJointRAM.value_cast cal.oldCount cal.oldDegree cal.peerSlots adj_ real₀ near (peer₀).shapes hostId j
  have ha:=DescentResetPeerJointRAM.aux_cast cal.oldCount cal.oldDegree cal.peerSlots adj_ real₀ near (peer₀).shapes hostId j
  exact ⟨by simpa only [cal.peerShapes] using peer.trans hp,by simpa only [cal.peerShapes] using aux.trans ha⟩


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
