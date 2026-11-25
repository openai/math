import OAI.Hierarchy.DescentProfiledResetArgumentHeaders
import OAI.Hierarchy.DescentProfiledResetArchiveReturn
import OAI.Hierarchy.DescentProfiledResetRangeFields
import OAI.Hierarchy.DescentProfiledResetAcquiredRoles

namespace OAI
/-! # The actual seven fields of the successor archive after a registered reset -/
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
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option pp.maxSteps 1200
set_option cleanup.letToHave false
set_option Elab.async false
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
local notation "divides" => fun _ : pins => Nat.dvd_mul_right_of_dvd pinWidth 1
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

attribute [local irreducible] SeedNamed.issued Origin.source Origin.archivePackage chosenClaim
include bus seedDegree degreeRoom in
private theorem profiledSelfArchiveProof
    (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (incoming : (evt).incoming cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : claim before cur history) (limit : R₁≤drift) :
    claim nextPath (cursor (i+1)) dst :=by
  have evidence := profiled_reset_seven_origins (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten w fit drift degree payload
      lo header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁ incoming words previous
  refine Exists.elim evidence (fun hw hwTail => ?_)
  refine Exists.elim hwTail (fun hb hbTail => ?_)
  refine Exists.elim hbTail (fun hr hrTail => ?_)
  refine Exists.elim hrTail (fun bounds boundsTail => ?_)
  refine Exists.elim boundsTail (fun geo geoTail => ?_)
  refine Exists.elim geoTail (fun space spaceTail => ?_)
  refine Exists.elim spaceTail (fun admitted admittedTail => ?_)
  have portsAt := admittedTail.2.1
  refine Exists.elim admittedTail.2.2 (fun hn hnTail => ?_)
  refine Exists.elim hnTail (fun hh hhTail => ?_)
  refine Exists.elim hhTail (fun hf hfTail => ?_)
  refine Exists.elim hfTail (fun hg hgTail => ?_)
  refine Exists.elim hgTail (fun ht htTail => ?_)
  refine Exists.elim htTail (fun boardAt boardAtTail => ?_)
  refine Exists.elim boardAtTail (fun opAt opAtTail => ?_)
  refine Exists.elim opAtTail (fun degAt degAtTail => ?_)
  refine Exists.elim degAtTail (fun capAt capAtTail => ?_)
  have held : RegisterTimeline.MatchedRegisteredOperandPanels (input:=r) (ctl:=ctl) (f:=f) (g:=g) (tail:=tail) (description:=oldDesc hw) (R:=R₁) board op B p drift degree payload w (menu).ordinary (menu).seats (menu).profile (menu).header cur space (rank₀ hw) bounds (shape₀ hw hb) (label₀ hw hr) geo geo.room.archive hn hh hf hg ht boardAt opAt degAt admitted.1 history capAt := capAtTail.1
  have sized := capAtTail.2.2.1
  have rolePos := capAtTail.2.2.2.1
  refine Exists.elim capAtTail.2.2.2.2 (fun layout layoutTail => ?_)
  refine Exists.elim layoutTail (fun actorMem actorTail => ?_)
  have acted : (u₁ space).ThroughActors atMem actorMem := actorTail.1
  have orig : RegisterTimeline.MatchedPublicOriginsAt board op B p drift degree payload w (menu).ordinary cur space hn hh hf hg ht boardAt opAt degAt admitted.1 history capAt actorMem := actorTail.2.1
  have fresh : RegisterTimeline.MatchedFreshInputsAt board op B p drift degree payload w (menu).ordinary cur space hn hh hf hg ht boardAt opAt admitted.1 actorMem := actorTail.2.2.1
  refine Exists.elim actorTail.2.2.2.1 (fun choice _ => ?_)
  refine Exists.elim actorTail.2.2.2.2 (fun mid physicalRun => ?_)
  have first : (u₁ space).throughOperandDate.Runs atMem mid := physicalRun.1
  have ran : (PhysicalReset.date (z₁ geo space)).Runs atMem dst := physicalRun.2
  have places:=profiled_reset_next_room (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten w fit drift degree
    payload lo header initial walk before B after_ joined geo space layout hw
  have headers:=profiled_reset_headers (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten w fit drift degree
    payload lo header initial bus walk m before B after_ joined seed₁ placed₁ hw hb hr bounds geo space admitted hn
    hh hf hg ht boardAt opAt degAt capAt held previous sized rolePos layout places limit actorMem (@acted) orig fresh choice
  have occupancy := profiled_reset_spans (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten w fit drift degree
    payload lo header initial bus walk m before B after_ joined seed₁ placed₁ hw hb hr bounds geo space admitted hn
    hh hf hg ht boardAt opAt degAt capAt held previous sized rolePos layout places limit actorMem (@acted) orig choice
  have spans := occupancy.1
  have vacant := occupancy.2
  have acquired := profiled_reset_acquired_roles (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten w fit
    drift degree payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁
    incoming words previous hw hb hr geo space admitted hn hh hf hg ht boardAt opAt degAt capAt layout places mid
    (@first) (@ran) actorMem (@acted) orig choice spans vacant limit
  exact profiled_reset_acquired_return (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten w fit drift degree payload
    lo header initial walk m before B after_ joined hw hb hr geo space admitted portsAt layout places limit mid
    (@first) (@ran) actorMem (@acted) choice headers spans vacant acquired.1 acquired.2

private abbrev ProfiledSelfArchiveType : Prop := type_of% @profiledSelfArchiveProof

theorem profiled_self_archive : ProfiledSelfArchiveType := @profiledSelfArchiveProof

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
