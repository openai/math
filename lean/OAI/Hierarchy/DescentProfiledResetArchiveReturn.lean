import OAI.Hierarchy.DescentProfiledResetSevenSource
import OAI.Hierarchy.DescentRegisteredCutArchiveTags
import OAI.Hierarchy.DescentResetAcquiredArchive
import OAI.Hierarchy.DescentRegisteredSevenSpans

namespace OAI
/-! # Return the decoded reset archive to the original registered path -/
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
set_option maxHeartbeats 400000
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
private theorem firstWidthGrainDivides (schedule : AtomSchedule) (b divisor : ℕ) :
    divisor ∣ schedule.firstWidth b divisor :=
  Nat.dvd_trans (grainAt_multiple schedule b 0) ⟨b, rfl⟩
local notation "pinWidth" => firstWidthGrainDivides S G.b p
local notation "divides" => fun _ : pins=>by simpa only [Nat.mul_one] using (pinWidth : p∣s)
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

attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage Origin.archiveOrder Origin.archiveShape Palette.encodedOrigin

local notation "ar" pro:arg => before.archive p positive (source).archive pro
local notation "rankOld" pro:arg => trajectory p positive (source).archive (Origin.archiveOrder source) before pro
local notation "schemaOld" pro:arg align:arg => archiveShape positive one₁ divides (source).archive firstShape before pro align
local notation "codeOld" pro:arg only:arg => encodePath op reset.menu before positive pro only (source).archive rawCode
set_option maxHeartbeats 450000 in
private theorem establishSelectedClaimAt (pos : RegisterTimeline.Position) (mem : Memory w) (out : DatePorts)
    (portsAt : pos.ports = out) (whole : before.whole p) (aligned : before.aligned p R₁) (only : before.OnlyRotor op)
    (available : ∃ bounds : DatePorts.RangeRoom out r (ar whole).bit,
      DatePorts.ArchiveRead out r (ar whole).bit (rankOld whole) bounds (schemaOld whole aligned) op (codeOld whole only).atNode
        (Reached.argumentPointer r (ar whole).bit (rankOld whole) (schemaOld whole aligned) positive pinNumber out.argumentsPerNode)
        (archiveFlag r (ar whole).bit (rankOld whole) out bounds) mem) : claim before pos mem := by
  subst out
  intro _ _ _
  exact available

include after_ joined in
/-- The registered date and the returned physical ports have the same occupied node and
operand coordinates. The claim uses the original recorded encoding on the extended path. -/
private theorem concreteReturnedRead
    (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
    (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
    (places : DatePorts.RangeRoom (ports₁ space) B.next (desc₁ hw))
    (limit : R₁≤drift)
    (mid : Memory w) (first : (u₁ space).throughOperandDate.Runs atMem mid)
    (ran : (PhysicalReset.date (z₁ geo space)).Runs atMem dst)
    (receipt : DatePorts.ResetArchiveCertificate (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
      (shape₁ hw hb) positive pinNumber op (label₁ hw hr) admitted.1 layout.small layout.axes layout.chart
      (z₁ geo space) atMem mid dst) :
    DatePorts.ArchiveRead (ports₁ space) B.next (desc₁ hw) (rank₁ hw) places (shape₁ hw hb) op (label₁ hw hr)
      (Reached.argumentPointer B.next (desc₁ hw) (rank₁ hw) (shape₁ hw hb) positive pinNumber
        (ports₁ space).argumentsPerNode)
      (archiveFlag B.next (desc₁ hw) (rank₁ hw) (ports₁ space) places) dst := by
  have mass:=profiled_reset_paid_precision X G S ordinary reset branch positive room shorten w fit
    drift degree payload lo header initial walk before B after_ joined geo space layout
  exact DatePorts.ResetArchiveCertificate.result (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
    (shape₁ hw hb) positive pinNumber op (label₁ hw hr) admitted.1 layout.small layout.axes layout.chart
    (z₁ geo space) admitted.2 first ran layout.coeff layout.blocks
    (Nat.zero_lt_succ i)
    (profiled_reset_argument_room X G S ordinary reset branch positive room shorten w fit drift degree payload
      lo header initial walk before B space layout limit hw (shape₁ hw hb)) mass receipt

include after_ joined in
/-- The registered date and the returned physical ports have the same occupied node and
operand coordinates. The claim uses the original recorded encoding on the extended path. -/
theorem profiled_reset_archive_return
    (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
    (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space)
    (portsAt : (cursor (i+1)).ports=ports₁ space)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
    (places : DatePorts.RangeRoom (ports₁ space) B.next (desc₁ hw))
    (limit : R₁≤drift)
    (mid : Memory w) (first : (u₁ space).throughOperandDate.Runs atMem mid)
    (ran : (PhysicalReset.date (z₁ geo space)).Runs atMem dst)
    (receipt : DatePorts.ResetArchiveCertificate (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
      (shape₁ hw hb) positive pinNumber op (label₁ hw hr) admitted.1 layout.small layout.axes layout.chart
      (z₁ geo space) atMem mid dst) :
    claim nextPath (cursor (i+1)) dst := by
  apply establishSelectedClaimAt (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (w:=w)
    (walk:=walk) (before:=nextPath) (cursor (i+1)) dst (ports₁ space) portsAt hw hb hr
  refine ⟨places, ?_⟩
  exact concreteReturnedRead X G S ordinary reset branch positive room shorten w fit drift degree payload
    lo header initial walk m before B after_ joined hw hb hr geo space admitted layout places limit mid first ran receipt

open DescentColonies DescentPackedZip DescentSIMDLookup DescentDatedNodeMetadata
local notation "v" => (inner₁).successor
local notation "inputs" sp:arg => u₁ sp
local notation "meta" => (v).metadata

include after_ joined in
theorem profiled_reset_acquired_return
    (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
    (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space)
    (portsAt : (cursor (i+1)).ports=ports₁ space)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (inputs space))
    (places : DatePorts.RangeRoom (ports₁ space) B.next (desc₁ hw)) (limit : R₁≤drift)
    (mid : Memory w) (first : (inputs space).throughOperandDate.Runs atMem mid)
    (ran : (PhysicalReset.date (z₁ geo space)).Runs atMem dst)
    (actorMem : Memory w) (acted : (inputs space).ThroughActors atMem actorMem)
    (choice : ∀ix,DatePorts.OrdinalRead (inputs space) admitted.1 layout.small actorMem ix)
    (headers : DatePorts.SevenHeaders (inputs space) B.next (desc₁ hw) (rank₁ hw) places
      (shape₁ hw hb) positive pinNumber admitted.1 layout.small layout.axes actorMem choice)
    (spans : DatePorts.SevenSpans (inputs space) B.next (desc₁ hw) (rank₁ hw) places
      (shape₁ hw hb) admitted.1 layout.small layout.axes actorMem choice)
    (empty : DatePorts.SevenVacant (inputs space) B.next (desc₁ hw) (rank₁ hw) places
      admitted.1 layout.small layout.axes actorMem choice)
    (paid : ∀x,Source ((PhysicalReset.FinalInputs.paid (inputs space)) x) (fun laneHost laneGroup=>
      Census.count B.next.placement (Equiv.refl _) (B.next.vertex.trans (Fin.castLEEmb B.next.valid.host))
        (meta).paidBits ((laneHost.cast (congrArg Chart.hosts layout.chart).symm).cast layout.hosts)
        ((laneGroup.cast (congrArg Chart.groups layout.chart).symm).cast places.groups.symm)
        ((x.cast (congrArg Chart.blocks layout.chart).symm).cast (congrArg (2^·) places.radix.symm)))
        (meta).chart.lanes ((z₁ geo space).venueImage mid))
    (roles : DatePorts.PrimitiveRolesAt (inputs space) B.next (desc₁ hw) (rank₁ hw) places op (label₁ hw hr) dst) :
    claim nextPath (cursor (i+1)) dst :=by
  have signed:=(DatePorts.reset_operand_word_room G S board k frozen i p f g drift degree payload (menu).ordinary
    op s (S.grainAt G.b p 0) (cur).ports (cur).floor w space admitted.1).2.2
  have receipt:=DatePorts.reset_acquired_certificate (inputs space) B.next (desc₁ hw) (rank₁ hw) places
    (shape₁ hw hb) positive pinNumber op (label₁ hw hr) (z₁ geo space) admitted.1 admitted.2 first layout.small
    layout.axes layout.chart actorMem acted choice headers spans empty layout.positiveLanes signed layout.receiverHosts
    layout.receiverGroups layout.receiverLanes layout.spanBits layout.hosts paid roles
  exact profiled_reset_archive_return X G S ordinary reset branch positive room shorten w fit drift degree payload lo
    header initial walk m before B after_ joined hw hb hr geo space admitted portsAt layout places limit mid
    first ran receipt

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
