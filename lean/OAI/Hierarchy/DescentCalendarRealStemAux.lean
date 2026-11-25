import OAI.Hierarchy.DescentCalendarRankValues
import OAI.Hierarchy.DescentResetPeerOldSelfWord
import OAI.Hierarchy.DescentNamedStemSector

namespace OAI
/-! # The old self-loop correction at the input to the stem ticket emitter -/
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
set_option hygiene false
set_option quotPrecheck false
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
local notation "host₁" => Stage.Host (Fin gs) B.next.V k
local notation "named₀" => (Z).rawHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))
local notation "s₀" => (v₀).sheets


local notation "regs₀" => (v₀).jointRegisters base₀ I.earlier
local notation "real₀" => compactActorName B pad
local notation "rows₀" => DescentResetPeerUnionRAM.selfPeers near
variable (m : Computability.VPVNP.BurstRAM.Memory bw) (seen : PhysicalReset.DateInputs.CaptureRoom (R₀) m)


open DescentPackedZip
local notation "cut_" => (v₀).jointEnd base₀
local notation "aux₃" => (v₀).peerAux base₀ 3
local notation "reported" h:arg => DescentResetPeerJointPacked.Aux.value (peer₀).shapes
    (R₀).names (R₀).prior (R₀).near h 3

/-- The signed predecessor self word at every address of the compact receiver, including padding. -/
def CapturedSelf (R : I.MeasuredChannels used) : Prop :=
  ∀{N : ℕ},used≤N→∀h : Fin N,DescentResetPeerJointPacked.Aux.value (peer₀).shapes
    R.names R.prior R.near h 3=stemSelfDigit B (originalTrunkRack B) h

set_option maxHeartbeats 640000 in
theorem measured_original_self : CapturedSelf B I (R₀) := by
  intro N occupied h
  have eqn:=DescentResetPeerJointRAM.aux_cast cal.oldCount cal.oldDegree cal.peerSlots
    adj_ real₀ near (peer₀).shapes h 3
  refine eqn.trans ?_
  rw [cal.peerShapes]
  exact original_stem_self B pad occupied h

include seen in
theorem real_stem_aux (ok : I.Ready) (occupied : used≤I.masked.hosts) :
    ∃self : Fin I.masked.hosts→Cell I.masked.field,
      Source aux₃ (fun h (_ : Fin I.masked.groups)=>self h) I.masked.lanes (I.masked.image (I.privateResult m)) ∧
      ∀h v,(originalTrunkRack B h=some v)→(self h).val=stemSelfDigit B (originalTrunkRack B) h:=by
  let self (h : Fin I.masked.hosts) : Cell I.masked.field:=
    ⟨reported h % 2^I.masked.field,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  refine ⟨self,?_,?_⟩
  · have early:=(PhysicalReset.DateInputs.actual_channels (R₀) ok m seen).aux (3:Fin 4)
    have fit:=(v₀).aux_fits base₀ ok.packed (3:Fin 4)
    have cut:=(v₀).receipt_order base₀
    have stable:=(I.masked.any (I.privateResult m) (I.genuine_mask_previous ok.joints ok.masked) ok.masked).2.2
    intro p
    exact (eval_below aux₃ _ _ _ fit (fun a low=>stable a (.inl (low.trans_le cut.2)))).trans (early p)
  · intro h _ _
    change reported h % 2^I.masked.field=_
    rw [Nat.mod_eq_of_lt (DescentResetPeerJointPacked.Aux.value_lt (peer₀).shapes
      (R₀).names (R₀).prior (R₀).near h 3 seen.distinct seen.shapes seen.keys seen.previousSelf)]
    exact measured_original_self B oldBatch batch calendar I cal pad prior xs raw near occupied h

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
