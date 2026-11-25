import OAI.Hierarchy.DescentNamedVenueActorDirectory
import OAI.Hierarchy.DescentNamedOperandActorGeometry
import OAI.Hierarchy.DescentCalendarControlSources
import OAI.Hierarchy.DescentPhysicalResetActorOutput

namespace OAI
/-! # The published reset operand registers on the named trajectory -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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
local notation "succ₀" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
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
local notation "actorBase" => (succ₀).middle.stop base₀
local notation "early" => (succ₀).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (succ₀).front.SceneRoom early ((succ₀).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster succ₀
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (succ₀).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (succ₀).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster succ₀
local notation "geom₀" => (a).chart start
local notation "fresh" => (geom₀).remixEnd (a).payload (a).gain (a).positive
local notation "phys₀" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geom₀).routedHosts (a).high (a).low (a).bits
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader digits input.vertex).site

local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (DescentDenseHostOrder.roster (Z).graph res (GroupStage.depthBound D n f g)).card
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "U" => (succ₀).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)


open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "height₁" => S.hostSize (age+1)
local notation "group₁" => S.groupCount (age+1)
local notation "qbits" => (succ₀).setup.rotorBits
local notation "control" => (succ₀).controlRegisters
local notation "first_" => (succ₀).controlFloor base₀
local notation "last_" => (succ₀).operandFloor base₀
local notation "prior_" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "occ" x => fun h g=>actualBit B B.next.valid.host h g x
local notation "scaled" => (⟨quantityDims B 1 HH height₁ (2^e) M,qbits⟩ : DescentResetControlRegisters.Chart)
local notation "levelAt_" vertex:arg => (Z).placement.b (DescentDenseHostOrder.position (Z).graph (vertex).val)

include accepted in
theorem DateInputs.fromNamed_control_sources (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (succ₀).funded.oldLanes (succ₀).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (succ₀).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(succ₀).funded.oldLanes) (oldWidth : (succ₀).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    (blocksAt : venue.k=k) (hostsAt : venue.hosts=HH) (nextLanes : 0 < M) :
    ∃dst,(u).throughOperandDate.Runs ((entry₀).image mem) dst ∧ (u).throughOperandDate.cheap ∧
      ∀x : DescentColonies.Block k,(((control).live first_ x.val).Fits w last_ ∧
        Source ((control).live first_ x.val) ((scaled).enabled (occ x) (fun _=>1)) M dst) ∧
      ∀j : Fin 4,((control).ports first_ input.placement.cap x.val (u).bank.inverse
          ((U).depths actorBase) ((U).levels actorBase) j).Fits w last_ ∧
        Source ((control).ports first_ input.placement.cap x.val (u).bank.inverse ((U).depths actorBase) ((U).levels actorBase) j)
          ((scaled).enabled (occ x) (controlScalar B input.valid.host B.next.valid.host j)) M dst := by
  obtain ⟨measured,posted,scan,issued,_,_,_,_,_,_,mid,result,planes,_,depths,levels,_,_⟩:=
    DateInputs.fromNamed_venue_directory accepted drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
      sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits low
      score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom
  obtain ⟨reassociated,cheap⟩:=DateInputs.classified_prefix («u»:=u) ready scan issued
  have actorDim : (U).hosts=HH ∧ (U).shapes=rows ∧ (U).chunksPerHost=chunks (2^(T).commonDepth) (2^e) := by
    rw [named_successor]
    obtain ⟨_,_,_,hostsEq,shapesEq,chunksEq,_⟩:=ClosedReset.Window.named_operand_geometry B p drift degree payload e previous M nextM packet prior_ base₀
      degreeAt blocksAt hostsAt capAt nextLanes
    exact ⟨hostsEq,shapesEq,chunksEq⟩
  obtain ⟨hH,hQ,hGroups⟩:=actorDim
  have grid : (U).directory actorBase=⟨(U).endAddress actorBase,HH,rows,chunks (2^(T).commonDepth) (2^e)⟩:=by
    change DescentResetNewActorDirectory.Layout.mk _ (U).hosts (U).shapes (U).chunksPerHost=_
    rw [hH,hQ,hGroups]
  have chart : control=scaled := by
    apply ClosedReset.Window.control_chart_of_venue (A:=a) B
    rw [named_successor]
    exact ClosedReset.Window.named_venue B p drift degree payload e previous M nextM packet prior_ base₀
      degreeAt blocksAt hostsAt capAt
  have oldDepth (t : B.next.V) : levelAt_ t ≤ cc+k := ((Z).placement.depth _).trans_eq B.frame.extent
  let pool:=DescentPackedPrivateMenu.fieldBound board k Ht (2^k*(2*cap)) (DescentRecordedRotorLayers.width f cap) C packet
  have countLe : 2^k*(2*cap) ≤ pool := Nat.le_max_left ..
  have palette : (DescentDenseHostOrder.roster board k Ht).card ≤ pool :=
    ((Nat.le_max_left ..).trans (Nat.le_max_right ..)).trans (Nat.le_max_right ..)
  have rate : ProtocolRAMPurchaseSampler.bits pool ≤ qbits :=
    ((Nat.le_max_right ..).trans (Nat.le_max_right ..)).trans (Nat.le_max_right ..)
  have space := (ProtocolRAMPurchaseSampler.lt_span pool).trans_le (Nat.pow_le_pow_right (by decide) rate)
  have capPos : 0 < cap := by
    rw [←capAt]
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at live
  have oldRoom : cap ≤ pool := by
    have q : 1≤2^k:=Nat.two_pow_pos _
    exact (show cap≤1*(2*cap) by omega).trans ((Nat.mul_le_mul_right _ q).trans countLe)
  have depthRoom : k+1 ≤ pool := (show k+1≤2^k from Nat.lt_two_pow_self).trans (by
    have r:=Nat.mul_le_mul_left (2^k) (by omega : 1≤2*cap)
    exact (by simpa only [Nat.mul_one] using r : 2^k≤2^k*(2*cap)).trans countLe)
  have shapeEq : rows=(DescentDenseHostOrder.roster board k Ht).card:= by
    rw [degreeAt];exact (DescentExteriorReplay.HopTables.reset_public B).1
  have short (v₁ : B.next.V) (t : ℕ)
      (member : t∈[1,input.placement.cap,levelAt_ v₁-(T).commonDepth+1,((Z).hostFields T rank v₁).2.val]) : t < 2^qbits := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact ((show 1 ≤ cap from capPos).trans oldRoom).trans_lt space
    · rw [capAt]; exact oldRoom.trans_lt space
    · have dep:=oldDepth v₁
      rw [B.commonDepth]
      exact ((show levelAt_ v₁-cc+1 ≤ k+1 by omega).trans depthRoom).trans_lt space
    · exact (((Z).hostFields T rank v₁).2.isLt.trans_le (shapeEq.le.trans palette)).trans space
  rw [grid] at result
  rw [result] at reassociated
  exact ⟨_,ClosedReset.Window.calendar_control_all_rows B input.valid.host B.next.valid.host u ready grid chart
    ((entry₀).image mem) mid reassociated cheap (Nat.two_pow_pos _) nextLanes laneRoom
    planes depths levels oldDepth short⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
