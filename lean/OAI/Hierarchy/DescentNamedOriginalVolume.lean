import OAI.Hierarchy.DescentNamedOriginalNumberBill
import OAI.Hierarchy.DescentOriginalNumberVolume
import OAI.Hierarchy.DescentResetPrimitiveReceivedVolume
import OAI.Hierarchy.DescentResetDigits

namespace OAI
/-! The fully installed original parent numberer at the previous host and group volume. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀


local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor (namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
    (scene : ((((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet   oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
  previousMeta previousArguments initial prepared scene
local notation "ss" => (v).sheets
local notation "r" => ((v).remap base₀).endAddress
local notation "deck" => (ss).inputDonorsEnd r
local notation "N₀" => 2^k*(2*cap)


open DescentStaticWordColumn

local notation "U₀" => (256+28*((v).front.signedQueries/2))
local notation "V₀" => (v).contactShape.originalWork


open DescentResetMixedWordRAM DescentDenseHostOrder CandidateFront
local notation "H" => S.hostSize age
local notation "G₀" => S.groupCount age
local notation "area" => ResetOutput.receiptArea payload H (chunks G₀ M)
local notation "shapeCount" => (DescentDenseHostOrder.roster board k Ht).card
local notation "growth" => 2^S.hostGain*S.radix
local notation "factor" => (3*shapeCount+2*growth+1)

private theorem original_room_invoice (layout : ResetOutput) (inputs : layout.sheets.OriginalInputs)
    (baseAddr leftCost donorCost h envelope : ℕ)
    (positive : 1≤envelope) (rows : layout.sheets.rows≤envelope)
    (table : (h+1)^3*2^(h/2)≤envelope) (lanes : 0<layout.sheets.lanes)
    (blocks : 0<layout.sheets.blocks) (birth : 0<layout.birth.rootBits)
    (key : layout.sheets.coordinate.dim*layout.sheets.coordinate.dim+
      Nat.clog 2 (chunks layout.sheets.groups layout.sheets.lanes)≤h/2)
    (occ : stemEnvelope h layout.sheets.sparseHosts layout.sheets.hosts layout.sheets.groups
      layout.sheets.blocks layout.sheets.lanes layout.sheets.lanes≤envelope)
    (paid : ∀ t, t∈layout.receiverUnits → t*layout.sheets.lanes≤h/2) :
    inputs.invoice baseAddr leftCost donorCost 64 ≤ inputs.numberFactor leftCost donorCost 64*envelope := by
  have unitRoom := paid (layout.birth.rootBits*layout.sheets.blocks) (by simp [ResetOutput.receiverUnits])
  have small := ((Nat.le_mul_of_pos_left layout.sheets.lanes (Nat.mul_pos birth blocks)).trans unitRoom).trans (Nat.div_le_self ..)
  apply inputs.volume baseAddr leftCost donorCost 64 h envelope positive rows table lanes small blocks key
  · exact paid _ (by simp [ResetOutput.receiverUnits])
  · exact paid _ (by simp [ResetOutput.receiverUnits])
  · exact paid _ (by simp [ResetOutput.receiverUnits])
  · change max ((layout.sheets.selectorBits+layout.sheets.shortBits)*layout.sheets.lanes)
        ((layout.sheets.shortBits+layout.sheets.shortBits)*layout.sheets.lanes) ≤ _
    exact max_le (paid _ (by simp [ResetOutput.receiverUnits])) (paid _ (by simp [ResetOutput.receiverUnits]))
  · exact paid (Book.unit layout.sheets.metaBits layout.sheets.zeroBits layout.sheets.shortBits layout.sheets.shortBits)
      (by simp [ResetOutput.receiverUnits])
  · have slot:=paid (DescentOperandPairBook.unit 6 layout.sheets.stemBits) (by simp [ResetOutput.receiverUnits])
    simpa only [DescentOperandPairBook.unit, show layout.sheets.stemBits*6+layout.sheets.stemBits=7*layout.sheets.stemBits by omega] using slot
  · exact paid (Book.unit layout.sheets.metaBits layout.sheets.zeroBits layout.sheets.haloBits layout.sheets.argBits)
      (by simp [ResetOutput.receiverUnits])
  · exact occ

private theorem number_geometry (Mpos : 0<M) (reached : age<S.length)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (key : (cc+k+1)^2≤payload/2) :
    let s₀:=CandidateSheets.fromBoard S board k tail age venue.degree f g cap M
    let roomBound:=factor*area
    1≤roomBound ∧ s₀.rows≤roomBound ∧ (payload+1)^3*2^(payload/2)≤roomBound ∧
      s₀.coordinate.dim*s₀.coordinate.dim+Nat.clog 2 (chunks s₀.groups M)≤payload/2 ∧
      stemEnvelope payload s₀.sparseHosts s₀.hosts s₀.groups s₀.blocks M M≤roomBound :=by
  dsimp only
  let roomBound:=factor*area
  let s₀:=CandidateSheets.fromBoard S board k tail age venue.degree f g cap M
  have split:S.groupCount (age+1)*2^k=G₀:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits reached radix)).symm
  have groups : S.groupCount (age+1)≤G₀ :=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq split
  have fewer : chunks (S.groupCount (age+1)) M ≤ chunks G₀ M :=Nat.div_le_div_right
    (Nat.sub_le_sub_right (Nat.add_le_add_right groups _) _)
  have next:S.hostSize (age+1)=H*growth:=by simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have root : H≤area:=by unfold ResetOutput.receiptArea;omega
  have current : H*chunks G₀ M≤area:=by unfold ResetOutput.receiptArea;omega
  have table : (payload+1)^3*2^(payload/2)≤area:=by unfold ResetOutput.receiptArea;omega
  have oldArea : area≤roomBound :=Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have one : 1≤roomBound:=lt_of_lt_of_le (show 0<(payload+1)^3*2^(payload/2) by positivity) (table.trans oldArea)
  have newRows : s₀.rows≤growth*area:=by
    change S.hostSize (age+1)*chunks (S.groupCount (age+1)) M≤_
    rw [next]
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      Nat.mul_le_mul_left growth ((Nat.mul_le_mul_left H fewer).trans current)
  have rawRows : s₀.sparseHosts*chunks (s₀.groups*s₀.blocks) M≤ shapeCount*area:=by
    change (H*shapeCount)*chunks (S.groupCount (age+1)*2^k) M≤_
    rw [split]
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left shapeCount current
  have fewerRaw : s₀.sparseHosts*chunks s₀.groups M≤ shapeCount*area:=by
    change (H*shapeCount)*chunks (S.groupCount (age+1)) M ≤ _
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      Nat.mul_le_mul_left shapeCount ((Nat.mul_le_mul_left H fewer).trans current)
  have newHost : s₀.hosts≤growth*area:=by
    change S.hostSize (age+1)≤_
    rw [next,Nat.mul_comm H];exact Nat.mul_le_mul_left _ root
  have source : s₀.sparseHosts≤ shapeCount*area:=by
    change H*shapeCount≤_;rw [Nat.mul_comm H];exact Nat.mul_le_mul_left _ root
  have occupancy : stemEnvelope payload s₀.sparseHosts s₀.hosts s₀.groups s₀.blocks M M≤roomBound :=by
    unfold stemEnvelope
    change _+_+_+s₀.rows+_+_≤_
    dsimp only [roomBound]; nlinarith only [newRows,rawRows,fewerRaw,newHost,source,table]
  have rows : s₀.rows≤roomBound:=newRows.trans (Nat.mul_le_mul_right _ (by omega))
  have ch : chunks s₀.groups M ≤ 2^cc :=by
    rw [S.group_power baseGroups radix age]
    apply le_trans _ groups
    exact (ceilDiv_le_iff_le_mul Mpos).2 (Nat.le_mul_of_pos_left s₀.groups Mpos)
  have exp : s₀.coordinate.dim*s₀.coordinate.dim+Nat.clog 2 (chunks s₀.groups s₀.lanes)≤payload/2 :=by
    have low:=Nat.clog_le_of_le_pow ch
    change (cc+k)*(cc+k)+Nat.clog 2 (chunks s₀.groups M)≤_
    nlinarith only [key,low,Nat.zero_le cc,Nat.zero_le k]
  exact ⟨one,rows,table.trans oldArea,exp,occupancy⟩

set_option maxHeartbeats 450000 in
theorem original_volume (pitch : M=2^e) (reached : age<S.length)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (key : (cc+k+1)^2≤payload/2) (ceiling : (a).fullEnd floor<2^w)
    (markers : ((v).front.donor.markers ((v).front.donorStart early)
      (v).contactShape.shapes (v).contactShape.markerBits).endAddress≤(v).trunkEnd base₀)
    (keys : ∀t,t∈(v).receiverUnits→t*(v).receiver.lanes≤payload/2) :
    (u).numbered.time r+7*names ((u).numbered.code r w) ≤
      ((u).numbered.numberFactor U₀ V₀ 64*factor)*area := by
  have lane : 0<M := pitch▸Nat.two_pow_pos _
  have output := named_successor G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io.wire io.roster floor
  have sheet : (v).sheets=CandidateSheets.fromBoard S board k tail age venue.degree f g cap M := by rw [output]; rfl
  have mounted : (v).receiver.lanes=M := by rw [output];rfl
  have sheetLane : (ss).lanes=M := by rw [sheet];rfl
  obtain ⟨one,rows,table,coord,occupied⟩ :=
    number_geometry G S board k tail age f g payload M venue lane reached baseGroups radix key
  have issued := named_original_invoice G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared scene lane ceiling markers
  apply issued.trans
  rw [Nat.mul_assoc]
  apply original_room_invoice (v) (u).numbered r U₀ V₀ payload (factor*area) one _ table
  · rw [sheetLane]; exact lane
  · rw [sheet]; exact Nat.two_pow_pos _
  · rw [output]; change 0<n*2^n+n+3;omega
  · rw [sheet]; exact coord
  · rw [sheet]; exact occupied
  · intro t member;rw [sheetLane,←mounted];exact keys t member
  · rw [sheet]; exact rows

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
