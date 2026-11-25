import OAI.Hierarchy.DescentNamedPrefixRangeRoom
import OAI.Hierarchy.DescentProfiledResetPaidRoles
import OAI.Hierarchy.DescentProfiledRootRegister
import OAI.Hierarchy.DescentProfiledInheritedRoles
import OAI.Hierarchy.DescentMatchedPrimitiveVenue

namespace OAI
/-! # Paid node counts and primitive instructions from the chronological reset -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline DescentExteriorReplay ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 600000
set_option maxRecDepth 8000
set_option cleanup.letToHave false
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
variable (drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "board" => reset.board
local notation "op" => RotorSpec.ofRates reset
local notation "frozen" => tail
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) a.ports a.floor

local notation "data" => fun i=>Geometry G S menu k w i (cursor i)
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial

variable (bus : payload≤w) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w)

variable (walk : (last).Choice) (m : Memory w)
variable {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
  {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}
  {n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
  (before : Path (trace walk).origin.source r) (B : ClosedReset r ctl)
  (after_ : Path B.next (trace walk).target) (joined : (before.reset B).append after_=(trace walk).path)
local notation "evt" => (Path.Event.reset before B after_ joined : (traces walk).path.Event i)
local notation "cur" => cursor i
local notation "history" => DateCode.history program m i
local notation "padEnd" => (cur).ports.priorStart k (cur).floor

local notation "inner₁" => (resetAt i cur).inner

local notation "prior₁" => ((cur).ports.afterPad k (cur).floor).archive
local notation "support₁" => PhysicalReset.ScheduledCodeRoom G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports.operandLanes (cur).ports.roleLanes
  (cur).ports.venue (cur).ports.io padEnd w prior₁
local notation "tag₁" => ((kindCalendar S.rounds S.height).drop i).head?
local notation "full₁" => (resetAt i cur).fullEnd
local notation "issued₁" cap₁:arg sp₁:arg => DatePorts.resetDate G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w cap₁ sp₁
local notation "ready₁" cap₁:arg sp₁:arg => PhysicalReset.ScheduledReady G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports.operandLanes (cur).ports.roleLanes (cur).ports.venue
  (cur).ports.io padEnd w prior₁ cap₁ sp₁

local notation "R₁" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "one₁" => le_max_left 1 (max reset.bitsR (C*reset.bitsR))
local notation "pinWidth" => (show p ∣ S.firstWidth G.b p from Nat.dvd_mul_right_of_dvd (grainAt_multiple S G.b 0) G.b)
local notation "divides" => fun _ : pins=>Nat.dvd_mul_right_of_dvd pinWidth 1
local notation "source" => (trace walk).origin
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private Origin.archiveOrder from OAI.Hierarchy.DescentNamedPrivateArchive
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
local notation "firstShape" => Origin.archiveShape source p R₁ positive one₁ pinWidth
local notation "rawCode" => Palette.encodedOrigin (p:=p) source op reset.menu
local notation "pinNumber" => fun y : pins=>y.1.val
open private chosenClaim from OAI.Hierarchy.DescentNamedArchivePrefix
local notation "claim" => chosenClaim X G S ordinary reset branch positive room shorten w walk
local notation "nextPath" => before.reset B
local notation "oldDesc" hw:arg => (before.archive p positive (source).archive (hw).1).bit
local notation "rank₀" hw:arg => trajectory p positive (source).archive (Origin.archiveOrder source) before (hw).1
local notation "shape₀" hw:arg hb:arg => archiveShape positive one₁ divides (source).archive firstShape before (hw).1 (hb).1
local notation "label₀" hw:arg hr:arg => (encodePath op reset.menu before positive (hw).1 (hr).1 (source).archive rawCode).atNode
local notation "capacity" => ((capCalendar G.b S.rounds g S.height).take i).prod*256
local notation "u₁" sp:arg => DatePorts.resetInputs G S board k frozen i p f g drift degree payload (menu).ordinary op
  s (S.grainAt G.b p 0) (cur).ports (cur).floor w sp
local notation "z₁" geo:arg sp:arg => DatePorts.resetFinalInputs G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w (geo).capacity sp
local notation "ports₁" sp:arg => DatePorts.resetPorts G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w sp
local notation "pad₁" => priorArchivePhase G S board k frozen i p f g drift degree payload
  (menu).ordinary op s (S.grainAt G.b p 0) (cur).ports (cur).floor w
local notation "ingress" => (inner₁).ingress
local notation "ingressPhase" => (ingress).phase padEnd w (cur).ports.io.hubs (fun x=>(cur).ports.io.atoms x.val)
  (fun j=>(cur).ports.io.wire j.1.val j.2.val)
local notation "atMem" => (ingressPhase).image ((pad₁).image history)
local notation "dst" => DateCode.history program m (i+1)

local notation "desc₁" hw:arg => ((nextPath).archive p positive (source).archive hw).bit
local notation "rank₁" hw:arg => trajectory p positive (source).archive (Origin.archiveOrder source) nextPath hw
local notation "shape₁" hw:arg hb:arg => archiveShape positive one₁ divides (source).archive firstShape nextPath hw hb
local notation "label₁" hw:arg hr:arg => (encodePath op reset.menu nextPath positive hw hr (source).archive rawCode).atNode

local notation "oldA" hw:arg => before.archive p positive (source).archive (hw).1

open DescentSIMDLookup DescentDatedNodeMetadata DescentResetGates DescentPacking.PackedMatch.Local.Stage
open DescentPackedResetRotorRoles DescentResetActorClass DescentRetainedRangeDigits
local notation "v" => (inner₁).successor
local notation "meta" => (v).metadata
local notation "l" => (v).birth.placement
local notation "lowBase" => (inner₁).rebased ((inner₁).stageStart padEnd)
local notation "location" => (v).actor.directory ((v).middle.stop lowBase)
local notation "oldArchive" hw:arg => before.archive p positive (source).archive (hw).1
local notation "oldCode" hw:arg hr:arg => encodePath op reset.menu before positive (hw).1 (hr).1 (source).archive rawCode
local notation "orig" hw:arg y:arg => resetOrigin B positive (hw).2 (oldArchive hw) y
local notation "prog" hw:arg => B.reset.laneRecipe (DescentOrderedReset.grains U B.count B.order) (B.reset.unit/p) p positive
  ((Nat.div_mul_cancel ((hw).2 : p∣B.reset.unit)).symm)
local notation "shape" hw:arg => B.reset.laneShape (DescentOrderedReset.grains U B.count B.order) (B.reset.unit/p) p positive
  ((Nat.div_mul_cancel ((hw).2 : p∣B.reset.unit)).symm)
local notation "node" geo:arg space:arg hw:arg => PhysicalReset.FinalInputs.nodeCell (z₁ geo space) B positive (hw).2 (oldArchive hw)
  (rank₀ hw) (by rfl) (by rfl) (by rfl)
local notation "gate" hw:arg hr:arg => reachedInput G s (S.grainAt G.b p 0) op reset.menu B positive (hw).2 (oldArchive hw) (oldCode hw hr)
local notation "actors" => B.next.vertex.trans (Fin.castLEEmb B.next.valid.host)
local notation "res" => B.reset.k-B.terminals.commonDepth
local notation "idxBits" => indexBits B.reset.n res
local notation "classEq" hn:arg => (show (v).birth.classBits=idxBits from by
  change indexBits n k=_
  exact congrArg₂ indexBits (B.dimension.trans hn).symm (ClosedReset.Window.calendar_residual B).symm)
local notation "kind" hn:arg h:arg => Fin.cast (congrArg (fun t : ℕ=>2^t) (classEq hn).symm)
  ((ClosedReset.Window.paidActorAt B h).elim 0 (fun actor=>indexed B.reset.graph res actor.val))

attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage chosenClaim
include bus seedDegree degreeRoom in
private theorem acquiredRolesFromRegisteredFields
    (seed₁ : data 0)
    (placed₁ : ∀j (ev : RunTrace.Events traces j), RegisterTimeline.fitsAt traces menu initial (w:=w) j ev)
    (incoming : (evt).incoming cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : claim before cur history)
    (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
    (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space)
    (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (boardAt : HEq ctl.board board) (opAt : RotorSpec.ofRates ctl=op)
    (degreeAt : (cur).ports.venue.degree=D) (capAt : r.placement.cap=capacity)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
    (places : DatePorts.RangeRoom (ports₁ space) B.next (desc₁ hw))
    (mid : Memory w) (first : (u₁ space).throughOperandDate.Runs atMem mid)
    (ran : (PhysicalReset.date (z₁ geo space)).Runs atMem dst)
    (actorMem : Memory w) (acted : (u₁ space).ThroughActors atMem actorMem)
    (origins : RegisterTimeline.MatchedPublicOriginsAt board op B p drift degree payload w (menu).ordinary
      cur space hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt actorMem)
    (choice : ∀ix,DatePorts.OrdinalRead (u₁ space) admitted.1 layout.small actorMem ix)
    (spans : DatePorts.SevenSpans (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
      (shape₁ hw hb) admitted.1 layout.small layout.axes actorMem choice)
    (empty : DatePorts.SevenVacant (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
      admitted.1 layout.small layout.axes actorMem choice)
    (limit:R₁≤drift) :
    paidPublication (gg:=G) (sched:=S) (age₀:=i) (drift:=drift) B.next (u₁ space) (z₁ geo space) layout places mid ∧
    DatePorts.PrimitiveRolesAt (u₁ space) B.next (desc₁ hw) (rank₁ hw) places op (label₁ hw hr) dst:=by
  have ms:=profiled_original_measures X G S ordinary reset branch positive room shorten w fit drift degree
    payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁ incoming words
  let rootWord := Classical.choice (profiled_root_register X G S ordinary reset branch positive room shorten w fit drift degree
    payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁ incoming words
    hw geo space admitted hn hh hf hg ht boardAt opAt degreeAt capAt actorMem mid origins first)
  have recorded : B.Recorded p := (profiled_reset_controls (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten walk before B after_ joined).1
  have venue:=RegisterTimeline.matched_primitive_venue (f:=f) (g:=g) (tail:=tail) board op B p drift degree payload w (menu).ordinary
    (menu).seats (menu).profile (menu).header cur geo.capacity space geo recorded hn hh hf hg ht boardAt opAt
    degreeAt admitted.1 admitted.2 history ms mid first
  have retained:=profiled_reset_inherited_roles (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten w fit
    drift degree payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁
    incoming words previous hw hb hr geo space admitted mid first ran
  let suffix := (Path.here.reset B).append after_
  have onPath : before.append suffix = (trace walk).path :=
    (Path.append_cut_assoc before (Path.here.reset B) after_).symm.trans joined
  have physical := Branch.prefix_tokenized X G S (trace walk) positive before suffix onPath hw.1
  exact profiled_reset_paid_roles (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten w fit drift degree payload lo
    header initial walk m before B after_ joined hw hb hr geo space admitted hn layout places mid first ran
    actorMem acted choice spans empty recorded physical rootWord venue retained limit

private abbrev AcquiredRolesFromRegisteredFieldsType : Prop := type_of% @acquiredRolesFromRegisteredFields

theorem profiled_reset_acquired_roles : AcquiredRolesFromRegisteredFieldsType :=
  @acquiredRolesFromRegisteredFields

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
