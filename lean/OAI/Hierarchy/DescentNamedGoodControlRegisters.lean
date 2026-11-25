import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentDatedPublicValues
import OAI.Hierarchy.DescentExteriorStaticHops
import OAI.Hierarchy.DescentNamedRotorAddressRoom
import OAI.Hierarchy.DescentMeasuredBankBadge
import OAI.Hierarchy.DescentCapCalendarPositive

namespace OAI
/-! # The four issued public control registers of a realized good rotor -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
  (sceneRoom : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "HH" => S.hostSize age

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "U" => (v).actor

open DescentSortedRoster

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL
open DescentSharedCableNames
open DescentResetTrunks
local notation "C₀" => (v).setup
local notation "H₁" => S.hostSize (age+1)

local notation "ctrl" => (v).controlRegisters
local notation "controlStart" => (v).controlFloor base₀
local notation "liveAt" x:arg => (ctrl).live controlStart (x:Fin (v).receiver.blocks).val
local notation "regsAt" x:arg => (ctrl).ports controlStart ((a).c/2) (x:Fin (v).receiver.blocks).val
  ((U).directory actorBase).inverse ((U).depths actorBase) ((U).levels actorBase)
local notation "deck" x:arg => OperandMenu.publicPorts («a»:=a) sh start count io.hubs g (2^n) (liveAt x) (regsAt x)

local notation "cfg" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation "operandValues" x:arg menu:arg => (u).menu.publicData sh start count io.hubs g (2^n)
  (liveAt x) (regsAt x) menu rfl ((x):Fin (v).receiver.blocks).val

open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "qbits" => (v).setup.rotorBits
local notation "occ" x:arg => fun h g=>actualBit B B.next.valid.host h g x
local notation "scaled" => (⟨quantityDims B 1 HH H₁ (2^e) M,qbits⟩ : DescentResetControlRegisters.Chart)


local notation "rootHost" => B.next.vertex.trans (Fin.castLEEmb B.next.valid.host)
local notation "oldRank" => (B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb input.valid.host)
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "shapeWord" v₁:arg => ((Z).hostFields T oldRank v₁).2.val
local notation "levelAt" v₁:arg => (Z).placement.b (position (Z).graph (v₁).val)
local notation "receiver" => (C₀).placement
local notation "activeBit" row:arg => (cfg).oldConfig.header ((cfg).basic row) 0

set_option maxHeartbeats 1000000
include accepted

/-- All four values are read at the same enabled compact receiver.  Its public gate
register uses the affirmative good-root flag even on a base with no old signed grains. -/
theorem DateInputs.named_good_registers (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (calibrated : z=S.grainAt G.b p (age+1)) (growth : G.b≤2^S.capGain)
    (x : Fin (v).receiver.blocks) (menu : (deck x).Values (receiver).newHosts (receiver).groups)
    (measureLive : ∀h gr,(menu.active h gr).val=((scaled).enabled (occ x) (fun _=>1) h gr).val)
    (measure : ∀j h gr,(menu.register j h gr).val=((scaled).enabled (occ x)
      (controlScalar B input.valid.host B.next.valid.host j) h gr).val)
    (s : Bool) (root : (Z).placement.Good) (v₁ : B.next.V) (gr : Fin (receiver).groups)
    (holder : position (Z).graph v₁.val=root.val.1)
    (occupied : actualBit B B.next.valid.host (rootHost v₁) gr x≠0) :
    let row:=(operandValues x menu) (rootHost v₁) gr
    let reg:=(cfg).reg row
    (activeBit row).val≠0 ∧ (reg 0).val=input.placement.cap ∧
      (reg 1).val=((Z).goodLabel T root).val.1+1 ∧ (reg 2).val=0 ∧
      (reg 3).val=(localRank (Z).graph res (GroupStage.depthBound D n f g) ((Z).localShape T v₁)).val ∧
      DescentRecordedRotorLayers.layers (Z).n (Z).width f (reg 0).val=((Z).circuit s root).layers ∧
      ((Z).circuit s root).layers*((Z).unit/p)≤S.retainedNodes := by
  intro row reg
  have capPos : 0<cap:=Nat.mul_pos
    (DescentSixParty.Chronology.DonorDate.prefix_cap_pos G.b S.rounds g S.height age G.base_pos) (by decide)
  let pool:=DescentPackedPrivateMenu.fieldBound board k Ht (2^k*(2*cap))
    (DescentRecordedRotorLayers.width f cap) C packet
  have countLe : 2^k*(2*cap)≤pool:=Nat.le_max_left ..
  have palette : (roster board k Ht).card≤pool:=
    ((Nat.le_max_left ..).trans (Nat.le_max_right ..)).trans (Nat.le_max_right ..)
  have rate : ProtocolRAMPurchaseSampler.bits pool≤qbits:=
    ((Nat.le_max_right ..).trans (Nat.le_max_right ..)).trans (Nat.le_max_right ..)
  have space:= (ProtocolRAMPurchaseSampler.lt_span pool).trans_le (Nat.pow_le_pow_right (by decide) rate)
  have depthRoom : k+1≤pool:= (show k+1≤2^k from Nat.lt_two_pow_self).trans (by
    have twice:=Nat.mul_le_mul_left (2^k) (by omega : 1≤2*cap)
    exact (by simpa only [Nat.mul_one] using twice : 2^k≤2^k*(2*cap)).trans countLe)
  have shapeEq : (roster (Z).graph res (GroupStage.depthBound D n f g)).card=(roster board k Ht).card:=by
    rw [degreeAt]
    exact (DescentExteriorReplay.HopTables.reset_public B).1
  have shapeFits : shapeWord v₁ < 2^qbits:=
    (((Z).hostFields T oldRank v₁).2.isLt.trans_le (shapeEq.symm ▸ palette)).trans space
  have depthFits : levelAt v₁-(T).commonDepth+1<2^qbits:=by
    have dep : levelAt v₁≤cc+k:=((Z).placement.depth _).trans_eq B.frame.extent
    rw [B.commonDepth]
    exact ((show levelAt v₁-cc+1≤k+1 by omega).trans depthRoom).trans_lt space
  have capFit : input.placement.cap<2^qbits := by
    rw [capAt]
    calc
      cap ≤ 1*(2*cap) := by omega
      _ ≤ 2^k*(2*cap) := Nat.mul_le_mul_right _ (Nat.two_pow_pos _)
      _ ≤ pool := countLe
      _ < 2^qbits := space
  have word (j : Fin 4) : (reg j).val=((scaled).enabled (occ x)
      (controlScalar B input.valid.host B.next.valid.host j) (rootHost v₁) gr).val:=
    ((u).menu.public_control_registers sh start count io.hubs g (2^n) (liveAt x) (regsAt x)
      menu rfl x.val (rootHost v₁) gr j).trans (measure ..)
  have found : ∃t,rootHost t=rootHost v₁:=⟨v₁,rfl⟩
  have selected : controlReceiver B B.next.valid.host (rootHost v₁)=some v₁:=by
    unfold controlReceiver
    rw [dite_eq_left found]
    exact congrArg some ((rootHost).injective found.choose_spec)
  have numeral (j : Fin 4) : (reg j).val=
      ((![input.placement.cap,levelAt v₁-(T).commonDepth+1,0,shapeWord v₁] j : ℕ) : Cell qbits).val:=by
    rw [word]
    simp only [DescentResetControlRegisters.Chart.enabled,ite_eq_right occupied]
    let value (z : B.next.V) : ℕ := ![input.placement.cap,levelAt z-(T).commonDepth+1,0,shapeWord z] j
    exact congrArg (fun vtx : Option B.next.V => ((vtx.elim 0 value : ℕ) : Cell qbits).val) selected
  have capSeen : (reg 0).val=input.placement.cap:=(numeral 0).trans (Fin.val_cast_of_lt capFit)
  have guard:= (u).menu.public_header_register sh start count io.hubs g (2^n) (liveAt x) (regsAt x)
    menu rfl x.val (rootHost v₁) gr 0
  refine ⟨?_,capSeen,?_,?_,(word 3).trans (shape_register_at B input.valid.host B.next.valid.host v₁ gr x occupied shapeFits),
    (DescentRecordedRotorLayers.from_prior_cap B accepted s root _ capSeen).1.symm,
    B.named_rotor_address_room accepted (age+1) calibrated growth s root⟩
  · rw [guard]
    change (menu.active (rootHost v₁) gr).val≠0
    apply (measureLive (rootHost v₁) gr).trans_ne
    have one : 1<2^qbits:=by omega
    change (if actualBit B B.next.valid.host (rootHost v₁) gr x=0 then (0 : Cell qbits) else ((1 : ℕ) : Cell qbits)).val≠0
    rw [ite_eq_right occupied,Fin.val_cast_of_lt one]
    decide
  · have read : (reg 1).val=levelAt v₁-(T).commonDepth+1:=
      (numeral 1).trans (Fin.val_cast_of_lt depthFits)
    rw [read,holder]
    rfl
  · exact (numeral 2).trans (Fin.val_cast_of_lt (Nat.two_pow_pos _))


local notation "born" s:arg root:arg cell:arg => (⟨(s,.inl root),DescentCommonPalette.rotorSiteEquiv (Z).graph d
  (DescentChosenRouter.selectedRotorLayers (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit s root)
  C (Z).width (Z).unit cell⟩ : (Z).bank.Site)
local notation "siteAt" s:arg root:arg cell:arg => B.reblock.destination (((Z).resetNames T).symm (.inr (born s root cell)))
local notation "hostAt" s:arg root:arg cell:arg => (B.next.placement.pos (siteAt s root cell)).2
local notation "groupAt" s:arg root:arg cell:arg => (B.next.placement.pos (siteAt s root cell)).1
local notation "blockAt" s:arg root:arg cell:arg => B.next.placement.block (siteAt s root cell)

/-- Reading the genuinely installed good-bank site fixes all three coordinates and
discharges both the compact active-bit test and the identification of the old holder. -/
theorem DateInputs.named_bank_good_registers (degreeAt : venue.degree=D) (capAt : input.placement.cap=cap)
    (calibrated : z=S.grainAt G.b p (age+1)) (growth : G.b≤2^S.capGain)
    (s : Bool) (root : (Z).placement.Good) (cell : (DescentCommonPalette.rotor (Z).graph).Site)
    (menu : (deck (blockAt s root cell)).Values (receiver).newHosts (receiver).groups)
    (measureLive : ∀h gr,(menu.active h gr).val=((scaled).enabled (occ (blockAt s root cell))
      (fun _=>1) h gr).val)
    (measure : ∀j h gr,(menu.register j h gr).val=((scaled).enabled (occ (blockAt s root cell))
      (controlScalar B input.valid.host B.next.valid.host j) h gr).val) :
    let v₁:=hostAt s root cell
    let row:=(operandValues (blockAt s root cell) menu) (rootHost v₁) (groupAt s root cell)
    let reg:=(cfg).reg row
    (activeBit row).val≠0 ∧ (reg 0).val=input.placement.cap ∧
      (reg 1).val=((Z).goodLabel T root).val.1+1 ∧ (reg 2).val=0 ∧
      (reg 3).val=(localRank (Z).graph res (GroupStage.depthBound D n f g) ((Z).localShape T v₁)).val ∧
      DescentRecordedRotorLayers.layers (Z).n (Z).width f (reg 0).val=((Z).circuit s root).layers ∧
      ((Z).circuit s root).layers*((Z).unit/p)≤S.retainedNodes := by
  have oldSite:= (DescentPrimitivePalette.original_bank_actor B (born s root cell)).2.1
  apply DateInputs.named_good_registers (B:=B) accepted drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom degreeAt capAt calibrated growth _ menu measureLive measure
    s root (hostAt s root cell) (groupAt s root cell) oldSite
  have occupied : actualBit B B.next.valid.host (rootHost (hostAt s root cell)) (groupAt s root cell)
      (blockAt s root cell)=1 :=ite_eq_left ⟨siteAt s root cell,rfl,rfl,rfl⟩
  rw [occupied]
  decide

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
