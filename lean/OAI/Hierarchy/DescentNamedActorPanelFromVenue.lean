import OAI.Hierarchy.DescentResetActorDirectoryOperands
import OAI.Hierarchy.DescentNamedActorDirectory
import OAI.Hierarchy.DescentNamedActorModel
import OAI.Hierarchy.DescentPhysicalRootSpectra
import OAI.Hierarchy.DescentStencilNativeRoom

namespace OAI
/-! The counted native venue reaches the named date's original measured actor header. -/
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
local notation "v" => (a).successor
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
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
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
local notation "priorCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal io.wire io.roster v
local notation "sourceRows" => DescentResetCanvasIngress.datedLayout input HH (v).funded.oldLanes
  (priorCPU).lanes (priorCPU).short (v).funded.precision (priorCPU).bits
local notation "oldCPU" => fromCalendar S k tail age G.b p f D payload e nBits tBits cal
  ((sourceRows).tokenAt floor) io.roster v
local notation "geom₀" => (a).chart start
local notation "fresh" => (geom₀).remixEnd (a).payload (a).gain (a).positive
local notation "phys₀" => DescentGLPacked.BankImage.Dated.chart (E).endAddress (geom₀).routedHosts (a).high (a).low (a).bits
local notation "saved" => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation "chip" => ((phys₀).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length
local notation "digits" => S.resetInputDigits ctl.base ctl.radix age
local notation "peer₀" => PackedFlow.portAt input.placement (input.placement.numberedHeader digits input.vertex).site

private def VenuePanel (L : DescentResetCanvasIngress.Layout) (cpu : PhysicalReset) (shape : cpu.StencilShape)
    (pop : Bank) (stride radius : ℕ) (mem : Memory w) : Prop :=
  let origin:=L.endAddress floor
  let ingress:=L.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
  let E₀:=cpu.estimator origin
  let stage:=cpu.stencilPhase shape origin pop io.hubs g radius
  ∃(μ : DescentGL.Layout E₀.dim) (dst : Memory w) (dim : E₀.dim=B.reset.k) (ports : D≤ stride),
    HEq μ B.frame.basis ∧ (ingress.program.seq (cpu.throughStencil shape origin pop io.hubs g radius (L.source floor)
      (S.groupCount age) stride w)).Exec mem dst
      (ingress.ticks+cpu.throughStencilTicks shape origin pop io.hubs g radius (S.groupCount age) stride w) ∧
    dst stage.saved=((DescentExterior.matrixCode μ).val:Word w) ∧ (∀x<floor,dst x=mem x) ∧
    ClosedReset.Recorded.StencilReservationWords (reset:=B) E₀ dim stride ports dst ∧
    stage.S.OldOrder stage.X stage.base stage.bank g (T).commonDepth μ dst ∧
    PackedFlow.Padded.Published (h:=cc) (l:=k) (2^e) tBits stage.output idx
      (ClosedReset.Recorded.realPanel (reset:=B) rfl B.frame.basis nBits tBits) dst ∧
    (∀site j,dst (io.roster.base+((idx site).val*input.placement.degree+j.val))=
      (DescentFallbackRankRAM.hostDigit idx (peer₀ site j):Word w)) ∧
    (∀site,dst (io.hubs.base+(idx site).val)=((input.placement.hub site).toNat:Word w)) ∧
    dst pop.base=(Fintype.card input.V:Word w) ∧
    ∀site,dst (E₀.depthRows.base+(idx site).val*(cc+k+1))=(B.reset.placement.b (B.frame.host site):Word w)

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

/-- All four bank bounds for the measured panel come from the actual named preparation
and issued stencil. -/
theorem DateInputs.fromNamed_venue_bank_room (ready : (u).Ready) :
    (chip).Fits w fresh ∧ ((1+venue.degree)+(E).dim)*HH*2^(E).high≤(chip).size ∧
    (ClosedReset.Recorded.firstContactBank E).Fits w (saved+1) ∧ (E).depthRows.Fits w (saved+1) :=by
  have stage : (P).Room w:=ready.stencil
  have area := stage.area
  change Size (P).chart (((1+(P).S.maxPorts)+((a).high+(a).low))*(P).S.hosts)
    (a).high (a).low (P).S.b w at area
  erw [(sh).ports,(sh).hosts,(sh).bits] at area
  have chosen:=(a).stencil_chosen_chip sh start count io.hubs g (2^n) w stage.saveRoom area
  have retained:=(a).root_spectra_before sh start count io.hubs g (2^n) ready.prime.fit (saved+1) le_rfl
  exact ⟨chosen.1,chosen.2,retained.2,retained.1⟩

include accepted in
theorem DateInputs.fromNamed_venue_reserved (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (v).funded.oldLanes (v).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (v).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(v).funded.oldLanes) (oldWidth : (v).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low) (fit : (E).Fits w) (room : 3*(E).dim+(E).precision+2≤w)
    (smooth : decayExponent venue.degree<2^w) (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (stored : (chip).Fits w fresh) (stores : ((1+venue.degree)+(E).dim)*HH*2^(E).high≤(chip).size)
    (spectrum : (ClosedReset.Recorded.firstContactBank E).Fits w (saved+1)) (depthFit : (E).depthRows.Fits w (saved+1))
    (live : 0<amp) (capBits : 2^((E).dim-(T).commonDepth)*amp<2^nBits)
    (levels : (E).dim-(T).commonDepth<2^nBits) (one : 1<2^nBits)
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p)≤w) (hostBits : HH<2^w)
    (codes : 2*DescentFallbackShapeTable.rows ((E).dim-(T).commonDepth) (2^n)≤2^tBits)
    (positiveD : 0<32*Nat.clog 2 (2*venue.degree)) :
    ∃(μ : DescentGL.Layout (E).dim) (measured : Memory w),HEq μ B.frame.basis ∧
      ((entry₀).program.seq ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
      (S.groupCount age) venue.degree w)).Exec mem measured
        ((entry₀).ticks+(a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      measured (P).saved=((DescentExterior.matrixCode μ).val:Word w) ∧
      (∀x<floor,measured x=mem x) ∧
      ClosedReset.Recorded.StencilReservationWords (reset:=B) E ((sh).dimension.symm.trans B.keyWidth.symm)
        venue.degree degreeAt.symm.le measured ∧
      (P).S.OldOrder (P).X (P).base (P).bank g (T).commonDepth μ measured ∧
      ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
        count (E).depthRows (rc).stencil book measured := by
  have rowsEq : sourceRows=(a).ingress := by
    subst D
    exact (calendar_ingress input tail p f payload e nBits tBits cal io.wire io.roster v
      ctl.base ctl.radix capAt gr fee history).symm
  have model : oldCPU=a:=named_actor_model G S board k tail age p f g drift degree payload e previous M nextM
    C packet oldLanes primitiveLanes printedBits venue io floor sourceRows rowsEq D degreeAt.symm
  let oldStart:=(sourceRows).endAddress floor
  have startEq : oldStart=start:=congrArg (fun L:DescentResetCanvasIngress.Layout=>L.endAddress floor) rowsEq
  have countOK : (oldCPU).PrimeRoom oldStart ((sourceRows).source floor) count (S.groupCount age) D w:=by
    let good (cpu : PhysicalReset) (L : DescentResetCanvasIngress.Layout) (d₀ : ℕ) :=
      cpu.PrimeRoom (L.endAddress floor) (L.source floor) count (S.groupCount age) d₀ w
    exact Eq.mpr ((congrArg (fun cpu => good cpu sourceRows D) model).trans
      ((congrArg (fun L => good a L D) rowsEq).trans (congrArg (good a (a).ingress) degreeAt.symm))) ready.prime
  have stageOK : ∀s:(oldCPU).StencilShape,((oldCPU).stencilPhase s oldStart count io.hubs g (2^(Z).n)).Room w:=by
    rw [model,startEq,B.dimension]
    intro s
    exact ready.stencil
  let oldE:=(oldCPU).estimator oldStart
  have estate : oldE=E:=(congrArg (fun cpu : PhysicalReset => cpu.estimator oldStart) model).trans (congrArg (a).estimator startEq)
  have atOld (pred : EstimatorArena → Prop) (ok : pred E) : pred oldE :=
    Eq.mpr (congrArg pred estate) ok
  have prepare : e≤oldE.low-k:=atOld (fun z => e≤z.low-k) fitsStencil
  let sourceShape:=calendar_shape S k tail age G.b p f D payload e nBits tBits cal ((sourceRows).tokenAt floor)
    io.roster v prepare
  let geomAt (cpu : PhysicalReset) (loc : ℕ) := cpu.chart loc
  let freshAt (cpu : PhysicalReset) (loc : ℕ) :=
    (geomAt cpu loc).remixEnd cpu.payload cpu.gain cpu.positive
  let chipAt (cpu : PhysicalReset) (loc : ℕ) :=
    let arena := cpu.estimator loc
    let image := DescentGLPacked.BankImage.Dated.chart arena.endAddress (geomAt cpu loc).routedHosts cpu.high cpu.low cpu.bits
    (image.chosen arena.dim).bank (DescentGLNielsen.schedule arena.dim).length
  let savedWord (cpu : PhysicalReset) (loc : ℕ) :=
    let arena := cpu.estimator loc
    freshAt cpu loc + (2^arena.dim)^arena.dim + (2^arena.dim)^arena.dim
  have transfer (pred : PhysicalReset → ℕ → ℕ → Prop) (ok : pred a start venue.degree) : pred oldCPU oldStart D :=
    Eq.mpr ((congrArg (fun cpu => pred cpu oldStart D) model).trans
      ((congrArg (fun loc => pred a loc D) startEq).trans (congrArg (pred a start) degreeAt.symm))) ok
  obtain ⟨μ,dst,chosen,run,savedAt,kept,reserved,orderAt,panel,hosts,hubs,pop,depth⟩:=
    accepted.actor_panel_from_venue_directory payload e nBits tBits cal io v floor count mem gr fee capAt branch
      seen popFit popRead wireRoom oldPos oldWidth (startEq.trans_lt entryFits)
      (atOld (fun z => k≤z.low) low) (atOld (fun z => z.Fits w) fit)
      (atOld (fun z => 3*z.dim+z.precision+2≤w) room) (Eq.mp (congrArg (fun d => decayExponent d<2^w) degreeAt) smooth)
      prepare (atOld (fun z => 3*z.dim+(z.precision+Nat.clog 2 z.hosts)+2≤w) score)
      countOK (stageOK sourceShape)
      (transfer (fun cpu loc _ => (chipAt cpu loc).Fits w (freshAt cpu loc)) stored)
      (transfer (fun cpu loc deg => ((1+deg)+(cpu.estimator loc).dim)*HH*2^(cpu.estimator loc).high≤(chipAt cpu loc).size) stores)
      (transfer (fun cpu loc _ => (ClosedReset.Recorded.firstContactBank (cpu.estimator loc)).Fits w (savedWord cpu loc+1)) spectrum)
      (transfer (fun cpu loc _ => (cpu.estimator loc).depthRows.Fits w (savedWord cpu loc+1)) depthFit)
      live (atOld (fun z => 2^(z.dim-(T).commonDepth)*amp<2^nBits) capBits)
      (atOld (fun z => z.dim-(T).commonDepth<2^nBits) levels) one
      (atOld (fun z => Nat.clog 2 (z.dim+2)+(z.dim+S.censusBits p)≤w) headerBits) hostBits
      (atOld (fun z => 2*DescentFallbackShapeTable.rows (z.dim-(T).commonDepth) (2^(Z).n)≤2^tBits)
        (Eq.mpr (congrArg (fun exp => 2*DescentFallbackShapeTable.rows ((E).dim-(T).commonDepth) (2^exp)≤2^tBits) B.dimension) codes)) (Eq.mp (congrArg (fun d => 0<32*Nat.clog 2 (2*d)) degreeAt) positiveD)
  have oldDim : oldE.dim=B.reset.k:=(congrArg EstimatorArena.dim estate).trans ((sh).dimension.symm.trans B.keyWidth.symm)
  have oldRun : ∀s:(oldCPU).StencilShape,VenuePanel (p:=p) (B:=B) e io floor w sourceRows oldCPU s count D (2^(Z).n) mem :=
    fun _=>⟨μ,dst,oldDim,le_rfl,chosen,run,savedAt,kept,reserved,orderAt,panel,hosts,hubs,pop,depth⟩
  have atDate : ∀s:(a).StencilShape,VenuePanel (p:=p) (B:=B) e io floor w (a).ingress a s count venue.degree (2^n) mem:=by
    let receipt (cpu : PhysicalReset) (L : DescentResetCanvasIngress.Layout) (stride exp : ℕ) :=
      ∀ shape : cpu.StencilShape, VenuePanel (p:=p) (B:=B) e io floor w L cpu shape count stride (2^exp) mem
    exact Eq.mp ((congrArg (fun cpu => receipt cpu sourceRows D (Z).n) model).trans
      ((congrArg (fun L => receipt a L D (Z).n) rowsEq).trans
      ((congrArg (fun stride => receipt a (a).ingress stride (Z).n) degreeAt.symm).trans
        (congrArg (receipt a (a).ingress venue.degree) B.dimension)))) oldRun
  obtain ⟨μ,dst,dimOK,ports,won,physical,savedAt,lowWords,census,rowOrder,pub,neighbors,marked,used,relative⟩:=atDate sh
  exact ⟨μ,dst,won,physical,savedAt,lowWords,census,rowOrder,⟨pub,neighbors,marked,used,relative⟩⟩

include accepted in
theorem DateInputs.fromNamed_venue_panel (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (v).funded.oldLanes (v).funded.precision floor
      (input.venueRoster input.valid.host) mem) (popFit : count.Fits w floor)
    (popRead : mem count.base=(Fintype.card input.V:Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (v).funded.oldLanes≤(io.wire x.val j.val).size)
    (oldPos : 0<(v).funded.oldLanes) (oldWidth : (v).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low) (fit : (E).Fits w) (room : 3*(E).dim+(E).precision+2≤w)
    (smooth : decayExponent venue.degree<2^w) (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (stored : (chip).Fits w fresh) (stores : ((1+venue.degree)+(E).dim)*HH*2^(E).high≤(chip).size)
    (spectrum : (ClosedReset.Recorded.firstContactBank E).Fits w (saved+1)) (depthFit : (E).depthRows.Fits w (saved+1))
    (live : 0<amp) (capBits : 2^((E).dim-(T).commonDepth)*amp<2^nBits)
    (levels : (E).dim-(T).commonDepth<2^nBits) (one : 1<2^nBits)
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p)≤w) (hostBits : HH<2^w)
    (codes : 2*DescentFallbackShapeTable.rows ((E).dim-(T).commonDepth) (2^n)≤2^tBits)
    (positiveD : 0<32*Nat.clog 2 (2*venue.degree)) :
    ∃measured,((entry₀).program.seq ((a).throughStencil sh start count io.hubs g (2^n) ((a).ingress.source floor)
      (S.groupCount age) venue.degree w)).Exec mem measured
        ((entry₀).ticks+(a).throughStencilTicks sh start count io.hubs g (2^n) (S.groupCount age) venue.degree w) ∧
      ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
        count (E).depthRows (rc).stencil book measured := by
  obtain ⟨_,dst,_,physical,_,_,_,_,panel⟩:=DateInputs.fromNamed_venue_reserved accepted drift degree payload e previous M
    nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom degreeAt ready mem gr fee capAt history branch seen popFit popRead
    wireRoom oldPos oldWidth entryFits low fit room smooth score stored stores spectrum depthFit live capBits levels one
    headerBits hostBits codes positiveD
  exact ⟨dst,physical,panel⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
