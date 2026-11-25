import OAI.Hierarchy.DescentProfiledPreviousArchive
import OAI.Hierarchy.DescentProfiledResetArgumentGeometry
import OAI.Hierarchy.DescentProfiledMathematicalReset
import OAI.Hierarchy.DescentScheduledSelectedReady
import OAI.Hierarchy.DescentMatchedSevenSpans

namespace OAI
/-! # The three original range fields on occupied and vacant reset slots -/
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
set_option maxHeartbeats 3500000
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
local notation "pinWidth" => dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
local notation "divides" => fun _ : pins=>by rw [Nat.mul_one]; exact (show p ∣ S.grainAt G.b p 0 * G.b from pinWidth)
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

attribute [local irreducible] SeedNamed.issued Origin.source Origin.archivePackage
include after_ joined bus in
theorem profiled_reset_spans
    (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
    (bounds : DatePorts.RangeRoom (cur).ports r (oldDesc hw))
    (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space)
    (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (boardAt : HEq ctl.board board) (opAt : RotorSpec.ofRates ctl=op)
    (degreeAt : (cur).ports.venue.degree=D) (capAt : r.placement.cap=capacity)
    (held : RegisterTimeline.MatchedRegisteredOperandPanels board op B p drift degree payload w
      (menu).ordinary (menu).seats (menu).profile (menu).header cur space (rank₀ hw) bounds (shape₀ hw hb)
      (label₀ hw hr) geo geo.room.archive hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt)
    (previous : claim before cur history) (sized : (cur).ports.RoleRows) (rolePos : 0<(cur).ports.roleLanes)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
    (places : DatePorts.RangeRoom (ports₁ space) B.next (desc₁ hw)) (limit : R₁≤drift)
    (actorMem : Memory w) (acted : (u₁ space).ThroughActors atMem actorMem)
    (orig : RegisterTimeline.MatchedPublicOriginsAt board op B p drift degree payload w (menu).ordinary cur space
      hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt actorMem)
    (choice : ∀ix,DatePorts.OrdinalRead (u₁ space) admitted.1 layout.small actorMem ix) :
    DatePorts.SevenSpans (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
      (shape₁ hw hb) admitted.1 layout.small layout.axes actorMem choice ∧
    DatePorts.SevenVacant (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
      admitted.1 layout.small layout.axes actorMem choice :=by
  let controls := profiled_reset_controls X G S ordinary reset branch positive room shorten walk before B after_ joined
  have recorded := controls.1
  have elapsed := controls.2.2.2.1
  have sorted := controls.2.2.2.2.1
  have grain := controls.2.2.2.2.2
  let sizes := profiled_reset_argument_geometry X G S ordinary reset branch positive room
    shorten w fit drift degree payload lo header initial walk before B after_ joined seed₁ placed₁ hw hb geo space
    layout elapsed limit
  have population := sizes.1
  have oldArity := sizes.2.1
  have newArity := sizes.2.2
  exact RegisterTimeline.matched_seven_spans board op B p drift degree payload w (menu).ordinary (menu).seats
      (menu).profile (menu).header cur space (oldA hw)
      (number:=rank₀ hw) (bounds:=bounds) (shape:=shape₀ hw hb) (label:=label₀ hw hr) (geo:=geo)
      («widths»:=geo.room.archive) (paid:=recorded) (hp:=positive) (one:=one₁) (unitPos:=hb.2.1)
      (whole:=hw.2) (wide:=hb.2.2.2) (pin:=pinNumber) (places:=places) (oldArity:=oldArity) (newArity:=newArity)
      (height:=ctl.height) (grain:=grain) (gain:=branch) (sized:=sized) (rolePos:=rolePos) (wBig:=bus)
      (population:=population) (flags:=RegisterTimeline.archiveFlag r (oldDesc hw) (rank₀ hw) (cur).ports bounds) hn hh hf hg ht boardAt opAt degreeAt admitted.1 history capAt elapsed sorted
      (RegisterTimeline.archive_read_at_bounds (fun (realRoom : DatePorts.RangeRoom (cur).ports r (oldDesc hw)) =>
        DatePorts.ArchiveRead (cur).ports r (oldDesc hw) (rank₀ hw) realRoom (shape₀ hw hb) op
          (label₀ hw hr) (Reached.argumentPointer r (oldDesc hw) (rank₀ hw) (shape₀ hw hb) positive
            pinNumber (cur).ports.argumentsPerNode)
          (RegisterTimeline.archiveFlag r (oldDesc hw) (rank₀ hw) (cur).ports realRoom) history)
        (previous hw.1 hb.1 hr.1) bounds) held actorMem
      acted orig (hb.2.2.2.trans limit) layout.small layout.axes choice

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
