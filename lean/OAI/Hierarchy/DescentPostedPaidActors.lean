import OAI.Hierarchy.DescentRecordedResetPaidSource
import OAI.Hierarchy.DescentNamedCapturedActorBounds
import OAI.Hierarchy.DescentRecordedFundedReturn
import OAI.Hierarchy.DescentNamedMeasuredActorMemory
import OAI.Hierarchy.DescentNamedOperandActorGeometry
import OAI.Hierarchy.DescentNamedRecordedVenue
import OAI.Hierarchy.DescentDatedVenueBelow
import OAI.Hierarchy.DescentPhysicalDateHistory

namespace OAI
/-! # Joint census and four actor-directory words at the selected original reset -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM DescentDatedAddressBook DescentSixParty.ClosedReset.Window DescentFundedCensus DescentPaidResidentCount.Reset
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentFallbackPeriod.Projected
open DescentSixParty.ClosedReset DescentGL DescentIssuedFallbackPanel
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
  (venue : StageVenueTail.Date) (io : Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "successor₀" => (a).successor
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
local notation "actorBase" => (successor₀).middle.stop base₀
local notation "early" => (successor₀).actorEnd base₀

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
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster successor₀
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (successor₀).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (successor₀).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster successor₀
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
local notation "U" => (successor₀).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

local notation "inputs" => FinalInputs.predecessor u
local notation "actorRows" => HH*chunks (2^(T).commonDepth) (2^e)


variable (run : @FinalInputs (named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) w ((DateInputs.fromNamed G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count) previousMeta previousArguments initial prepared sceneRoom))
local notation "st_" => (a).throughStencil (u).shape start (u).count (u).hub (u).g (u).Y
  (u).src (u).sourceRows (u).oldDegree w
local notation "time_" => (a).throughStencilTicks (u).shape start (u).count (u).hub (u).g (u).Y
  (u).sourceRows (u).oldDegree w
local notation "fund_" => (successor₀).funded
local notation "bill_" => (successor₀).venue.census
local notation "precision" => (bill_).bits
local notation "key_" => (⟨(P).saved,0⟩:Bank)
local notation "feeStart" => (successor₀).fundedEnd base₀
local notation "feeBanks" => fundedPorts (funded_residual B) B.dimension run.ports
local notation "paidRAM" dst:arg => DescentFundedCensus.memory run.jobs feeStart
  ((fund_).memory ((successor₀).finalEnd base₀) run.earlier key_ dst)
local notation "enter" src:arg => (entry₀).image src
local notation "atOps" src:arg => (u).throughOperandDate.nextMemory (enter src)
local notation "oldRaw" => input.vertex.trans (Fin.castLEEmb input.valid.host)

private theorem shift_venue {h₁ h₂ l₁ l₂ p₁ p₂ : ℕ} (hosts : h₁=h₂) (lanes : l₁=l₂) (bits : p₁=p₂)
    (o₁ : Fintype.card input.V≤h₁) (o₂ : Fintype.card input.V≤h₂) (m : Memory w)
    (seen : stageVenue input o₁ io l₁ p₁ floor (input.venueRoster o₁) m) :
    stageVenue input o₂ io l₂ p₂ floor (input.venueRoster o₂) m:=by
  subst h₂;subst l₂;subst p₂;exact seen

private theorem shift_actors {h₁ h₂ : ℕ} (hosts : h₁=h₂) (o₁ : Fintype.card input.V≤h₁)
    (o₂ : Fintype.card input.V≤h₂) (out : Memory w) (bank : ℕ)
    (got : ∀(j : Fin rows) (s : Row h₁ (2^(T).commonDepth) (2^e)),
      out (bank+j.val*(h₁*chunks (2^(T).commonDepth) (2^e))+(row _ _ _ s).val)=
      ((data (ClosedReset.Recorded.realActor (reset:=B) (shapes B) (rack B o₁) j) s).val:Word w)) :
    ∀(j : Fin rows) (s : Row h₂ (2^(T).commonDepth) (2^e)),
      out (bank+j.val*(h₂*chunks (2^(T).commonDepth) (2^e))+(row _ _ _ s).val)=
      ((data (ClosedReset.Recorded.realActor (reset:=B) (shapes B) (rack B o₂) j) s).val:Word w):=by
  subst h₂;exact got

private theorem shift_paid {h₁ h₂ : ℕ} (hosts : h₁=h₂) (o₁ : Fintype.card input.V≤h₁)
    (o₂ : Fintype.card input.V≤h₂) (mem : Memory w) (bank bits : ℕ)
    (got : ∀(j : Fin rows) (s : Row h₁ (2^(T).commonDepth) (2^e)),mem (bank+j.val*(h₁*chunks (2^(T).commonDepth) (2^e))+
      (row _ _ _ s).val)=((data (fun v hi=>payable («precision»:=bits) B accepted o₁ (finProdFinEquiv (v,j)) hi) s).val:Word w)) :
    ∀(j : Fin rows) (s : Row h₂ (2^(T).commonDepth) (2^e)),mem (bank+j.val*(h₂*chunks (2^(T).commonDepth) (2^e))+
      (row _ _ _ s).val)=((data (fun v hi=>payable («precision»:=bits) B accepted o₂ (finProdFinEquiv (v,j)) hi) s).val:Word w):=by
  subst h₂;exact got

theorem DateInputs.measured_funded_actors (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (successor₀).funded.oldLanes (successor₀).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (successor₀).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(successor₀).funded.oldLanes) (oldWidth : (successor₀).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    (hosts : HH=venue.hosts) (groups : venue.groups=S.groupCount age)
    (blocks : venue.k=k) (capacity : venue.cap=input.placement.cap) (pitch : venue.lanes=2^previous)
    (pos : 0<M) (readLanes : (fund_).oldLanes=venue.lanes) (readBits : (fund_).precision=precision)
    (original : run.io=io) (safe : run.Room) (banks : IssuedBanks io venue.hosts (S.groupCount age) venue.lanes)
    (oldHub : io.hubs.Fits w floor) (oldAtom : ∀x:Fin (2^(a).ingress.k),(io.atoms x.val).Fits w floor)
    (oldWire : ∀j:(a).ingress.signed.Slot,(io.wire j.1.val j.2.val).Fits w floor)
    (measured : Memory w) (scan : (st_).Exec (enter mem) measured time_)
    (μ : DescentGL.Layout ((cc-e)+(e+k))) (chosen : HEq μ B.frame.basis)
    (saved_ : measured (P).saved=((DescentExterior.matrixCode μ).val:Word w))
    (snap : PaddedSnapshot B (input.valid.host.trans_eq hosts) (u).roots.field)
    (rootPages : ∀s t,Source ((feeBanks).bank s t) (savedInput B (input.valid.host.trans_eq hosts) snap) (2^e)
      ((rc).preparedImage (u).book (u).bookFits measured))
    (fBits : ℕ)
    (printed : PackedFlow.Padded.Published (h:=cc-e) (l:=e+k) (2^e) (P).S.t (P).output
      (input.vertex.trans (Fin.castLEEmb (input.valid.host.trans_eq hosts)))
      (ClosedReset.Recorded.realPanel (reset:=B) (by omega : cc-e+(e+k)=cc+k) μ fBits (P).S.t) measured)
    (up : cc+k-(T).commonDepth<2^fBits) (one : 1<2^fBits) (enough : 2^(cc+k-(T).commonDepth)*amp<2^fBits)
    (legal : 2*DescentFallbackShapeTable.rows (cc+k-(T).commonDepth) (2^(Z).n)≤2^(P).S.t)
    (positiveQuota : 0<quota S.rounds) (countFits : amp<2^precision) (arrivalFits : 2*input.placement.cap<2^precision) :
    (∀j (s : Row HH (2^(T).commonDepth) (2^e)),(paidRAM (atOps mem)) (((successor₀).venue.original feeStart).base+
      j.val*actorRows+(row _ _ _ s).val)=((data (fun v hi=>payable («precision»:=precision)
      B accepted input.valid.host (finProdFinEquiv (v,j)) hi) s).val:Word w)) ∧
    (∀j (s : Row HH (2^(T).commonDepth) (2^e)),(atOps mem) ((inputs).actor.base+j.val*actorRows+
      (row _ _ _ s).val)=((data (ClosedReset.Recorded.realActor (reset:=B) (shapes B)
      (rack B input.valid.host) j) s).val:Word w)) ∧
    (atOps mem) (inputs).ranks.count.base=(Fintype.card B.next.V:Word w) ∧
    (∀v:B.next.V,(atOps mem) ((inputs).ranks.inverse.base+(B.next.vertex v).val)=((rawId v).val:Word w)) ∧
    (∀v:B.next.V,(atOps mem) ((inputs).ranks.forward.base+(rawId v).val)=((B.next.vertex v).val:Word w)):=by
  let oldRoom :=input.valid.host.trans_eq hosts
  obtain ⟨out,ran,_,_⟩:=(u).run_to_operands ready (enter mem)
  have completed:(u).throughOperandDate.Runs (enter mem) (atOps mem):=
    ((u).throughOperandDate.nextMemory_eq ran).symm ▸ ran
  have actors:=DateInputs.fromNamed_operand_actors accepted drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth entryFits
    low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom completed
  let config:=ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
  have geometry:=named_operand_geometry B p drift degree payload e previous M nextM packet config
    ((a).rebased start) degreeAt blocks hosts.symm capAt pos
  have shape : (bill_).jobs=(successor₀).actor.shapes:=geometry.1
  have arow : (successor₀).actor.hosts*(successor₀).actor.chunksPerHost=venue.hosts*chunks (2^(T).commonDepth) (2^e):=by
    exact congrArg₂ Nat.mul (geometry.2.2.2.1.trans hosts) geometry.2.2.2.2.2.1
  have activeActors:=shift_actors (B:=B) (e:=e) (w:=w) hosts input.valid.host oldRoom (atOps mem)
    (inputs).actor.base actors.1
  obtain ⟨_,frame⟩:=(a).ingress.any floor io.hubs (fun x=>io.atoms x.val)
    (fun j=>io.wire j.1.val j.2.val) mem oldHub oldAtom oldWire entryFits
  have under (h : ℕ) (h₀:h<floor) : (enter mem) h=mem h:=frame h (.inl h₀)
  have held:=shift_venue (input:=input) io floor w hosts readLanes readBits input.valid.host oldRoom mem seen
  have fits (x:DescentColonies.Block k) (j:Fin (2*input.placement.cap)) : (io.wire x.val j.val).Fits w floor ∧
      venue.hosts*chunks (S.groupCount age) venue.lanes≤(io.wire x.val j.val).size:=by
    simpa only [hosts,readLanes] using wireRoom x j
  have entered:=stageVenue_below input oldRoom io venue.lanes precision floor (input.venueRoster oldRoom) mem (enter mem) held
    (fun x j=>(Nat.add_le_add_left (fits x j).2 _).trans (fits x j).1.2.2) under
  have cuts:=(a).ingress.order floor
  have floorLE : floor≤ start:=cuts.1.trans (cuts.2.1.trans cuts.2.2)
  have degPositive : 0<32*Nat.clog 2 (2*input.placement.degree):=by
    simpa only [degreeAt,input.branch] using degreePos
  have issued:=FinalInputs.reached_funded_words B accepted drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor run fitsSigned fitsCut rfl rfl gr degreeAt capacity hosts blocks groups pitch oldRoom ready safe
    original (input.venueRoster oldRoom) floor floorLE (enter mem) measured (atOps mem) entered banks fits scan completed
    μ chosen saved_ shape arow activeActors snap rootPages fBits printed up one enough legal live positiveQuota
    degPositive countFits arrivalFits
  exact ⟨shift_paid accepted (e:=e) (w:=w) hosts.symm oldRoom input.valid.host _ _ _ issued,actors⟩

include accepted in
/-- The original reset census can be read at the primitive checkpoint without changing its packing width. -/
theorem DateInputs.fromNamed_paid_venue (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (successor₀).funded.oldLanes (successor₀).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (successor₀).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(successor₀).funded.oldLanes) (oldWidth : (successor₀).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
    (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w)
    (hosts : HH=venue.hosts) (groups : venue.groups=S.groupCount age)
    (blocks : venue.k=k) (capacity : venue.cap=input.placement.cap) (pitch : venue.lanes=2^previous)
    (pos : 0<M) (readLanes : (fund_).oldLanes=venue.lanes) (readBits : (fund_).precision=precision)
    (original : run.io=io) (safe : run.Room) (banks : IssuedBanks io venue.hosts (S.groupCount age) venue.lanes)
    (oldHub : io.hubs.Fits w floor) (oldAtom : ∀x:Fin (2^(a).ingress.k),(io.atoms x.val).Fits w floor)
    (oldWire : ∀j:(a).ingress.signed.Slot,(io.wire j.1.val j.2.val).Fits w floor)
    (measured : Memory w) (scan : (st_).Exec (enter mem) measured time_)
    (μ : DescentGL.Layout ((cc-e)+(e+k))) (chosen : HEq μ B.frame.basis)
    (saved_ : measured (P).saved=((DescentExterior.matrixCode μ).val:Word w))
    (snap : PaddedSnapshot B (input.valid.host.trans_eq hosts) (u).roots.field)
    (rootPages : ∀s t,Source ((feeBanks).bank s t) (savedInput B (input.valid.host.trans_eq hosts) snap) (2^e)
      ((rc).preparedImage (u).book (u).bookFits measured))
    (fBits : ℕ)
    (printed : PackedFlow.Padded.Published (h:=cc-e) (l:=e+k) (2^e) (P).S.t (P).output
      (input.vertex.trans (Fin.castLEEmb (input.valid.host.trans_eq hosts)))
      (ClosedReset.Recorded.realPanel (reset:=B) (by omega : cc-e+(e+k)=cc+k) μ fBits (P).S.t) measured)
    (up : cc+k-(T).commonDepth<2^fBits) (one : 1<2^fBits) (enough : 2^(cc+k-(T).commonDepth)*amp<2^fBits)
    (legal : 2*DescentFallbackShapeTable.rows (cc+k-(T).commonDepth) (2^(Z).n)≤2^(P).S.t)
    (positiveQuota : 0<quota S.rounds) (countFits : amp<2^precision) (arrivalFits : 2*input.placement.cap<2^precision)
    (newHost:0<S.hostSize (age+1))(newChunks:0<chunks (S.groupCount (age+1)) M):
    ∀x:DescentColonies.Block k,Source (.lookup (((successor₀).venue.sources inputs feeStart).paid x.val) .row)
      (fun h g=>Census.count B.next.placement (Equiv.refl _) (B.next.vertex.trans (Fin.castLEEmb B.next.valid.host))
        venue.paidBits h g x) M (run.venueImage (atOps mem)):=by
  obtain ⟨calibrated,_,used,word,_,rankEarly,inverseEarly,_,_,_,_,paidEnd,_,_⟩:=
    DateInputs.fromNamed_held_bounds B p drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
      venue io floor w (u) ready degreeAt blocks hosts.symm capAt pos
  obtain ⟨fund,_,counted,inv,_⟩:=DateInputs.measured_funded_actors accepted drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom run degreeAt ready mem gr fee capAt history branch seen popFit popRead wireRoom oldPos
    oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit laneRoom hosts groups
    blocks capacity pitch pos readLanes readBits original safe banks oldHub oldAtom oldWire measured scan μ chosen
    saved_ snap rootPages fBits printed up one enough legal positiveQuota countFits arrivalFits
  exact ClosedReset.Window.recorded_paid_at_venue B accepted input.valid.host B.next.valid.host run calibrated safe
    used word (atOps mem) (Nat.two_pow_pos _) pos newHost newChunks rankEarly inverseEarly fund counted inv paidEnd

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
