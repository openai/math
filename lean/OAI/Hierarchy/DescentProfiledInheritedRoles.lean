import OAI.Hierarchy.DescentNamedArchivePrefix
import OAI.Hierarchy.DescentProfiledResetOperandPanels
import OAI.Hierarchy.DescentMatchedInheritedRoles
import OAI.Hierarchy.DescentProfiledOriginalMeasures

namespace OAI
/-! # The inherited primitive source at an actual registered reset event -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline DescentExteriorReplay ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 1200000
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
local notation "shapeNow" => (v).primitive.chart
local notation "newBits" hw:arg => (resetArchive B p positive (hw).2 (oldArchive hw)).bit
local notation "newOrder" hw:arg => DescentLocalArchiveOrder.reset B p positive (hw).2 (oldArchive hw) (rank₀ hw)
local notation "now" hw:arg x:arg j:arg h':arg g':arg => Reached.NodeCells.whereAt B.next (newBits hw) (newOrder hw)
  ((x).cast (by rfl)) j ((h').cast (by rfl)) ((g').cast (by rfl))
local notation "gate" hw:arg hr:arg => reachedInput G s (S.grainAt G.b p 0) op reset.menu B positive (hw).2 (oldArchive hw) (oldCode hw hr)
local notation "actors" => B.next.vertex.trans (Fin.castLEEmb B.next.valid.host)
local notation "res" => B.reset.k-B.terminals.commonDepth
local notation "idxBits" => indexBits B.reset.n res
local notation "classEq" hn:arg => (show (v).birth.classBits=idxBits from by
  change indexBits n k=_
  rw [B.dimension,hn,ClosedReset.Window.calendar_residual B])
local notation "kind" hn:arg h:arg => Fin.cast (congrArg (fun t : ℕ=>2^t) (classEq hn).symm)
  ((ClosedReset.Window.paidActorAt B h).elim 0 (fun actor=>indexed B.reset.graph res actor.val))

open DescentColonies DescentPackedZip
local notation "ar" pro:arg => before.archive p positive (source).archive pro
local notation "rankOld" pro:arg => trajectory p positive (source).archive (Origin.archiveOrder source) before pro
local notation "schemaOld" pro:arg align:arg => archiveShape positive one₁ divides (source).archive firstShape before pro align
local notation "codeOld" pro:arg only:arg => encodePath op reset.menu before positive pro only (source).archive rawCode
attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage Origin.archiveOrder Origin.archiveShape Palette.encodedOrigin
set_option maxHeartbeats 450000 in
private theorem readPreviousAtPoint (pos : RegisterTimeline.Position) (mem : Memory w)
    (previous : claim before pos mem) (whole : before.whole p) (aligned : before.aligned p R₁) (only : before.OnlyRotor op) :
    ∃ bounds : DatePorts.RangeRoom pos.ports r (ar whole).bit,
      DatePorts.ArchiveRead pos.ports r (ar whole).bit (rankOld whole) bounds (schemaOld whole aligned) op (codeOld whole only).atNode
        (Reached.argumentPointer r (ar whole).bit (rankOld whole) (schemaOld whole aligned) positive pinNumber pos.ports.argumentsPerNode)
        (archiveFlag r (ar whole).bit (rankOld whole) pos.ports bounds) mem := by
  exact previous whole aligned only

attribute [local irreducible] chosenClaim
include bus seedDegree degreeRoom in
/-- The incoming chronological archive and the actually selected calendar run supply
the retained operand of `profiled_reset_paid_roles` at each physical slot. -/
theorem profiled_reset_inherited_roles (seed₁ : data 0)
    (placed₁ : ∀j (ev : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j ev)
    (incoming : Path.Event.incoming (t:=traces walk) evt cur history) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (previous : claim before cur history) (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁)
    (hr : (nextPath).OnlyRotor op)
    (geoAt : data i) (spaceAt : support₁) (admitted : ready₁ geoAt.capacity spaceAt)
    (mid : Memory w) (first : (u₁ spaceAt).throughOperandDate.Runs atMem mid)
    (ran : (PhysicalReset.date (z₁ geoAt spaceAt)).Runs atMem dst) :
    ∀(x : Fin (shapeNow).blocks) (j : Fin (shapeNow).nodes),
      DescentPackedZip.Source ((z₁ geoAt spaceAt).roles.retained x j)
        (fun (h' : Fin (shapeNow).hosts) (g' : Fin (shapeNow).groups) =>
          DescentResetPrimitivePage.oldWord (b:=DescentPrimitivePalette.printedBits G s (S.grainAt G.b p 0) op)
            ((now hw x j h' g').elim .padding (gate hw hr)))
        (shapeNow).lanes ((z₁ geoAt spaceAt).roleInput mid):=by
  let earlier := readPreviousAtPoint X G S ordinary reset branch positive room shorten w walk before cur history previous hw.1 hb.1 hr.1
  let bounds := earlier.choose
  let old := earlier.choose_spec
  have recorded := (profiled_reset_controls (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten walk before B after_ joined).1
  let panels := profiled_reset_original_panels (F:=F) (cp:=cp) (nP:=nP) (k:=k) (cut:=cut) (tail:=tail) (n:=n) (h:=h)
      (C:=C) (f:=f) (g:=g) (p:=p) (r:=r) (ctl:=ctl) (description:=oldDesc hw) (R:=R₁)
      X G S ordinary reset branch positive room shorten w fit drift degree payload lo header initial bus seedDegree
      degreeRoom walk m before B after_ joined (rank₀ hw) bounds (shape₀ hw hb) (label₀ hw hr)
      seed₁ placed₁ incoming words old
  let shapeFacts := panels.choose_spec.choose_spec.choose_spec.2.2.2.2
  let shapeN := shapeFacts.choose
  let shapeNRest := shapeFacts.choose_spec
  let shapeH := shapeNRest.choose
  let shapeHRest := shapeNRest.choose_spec
  let shapeF := shapeHRest.choose
  let shapeFRest := shapeHRest.choose_spec
  let shapeG := shapeFRest.choose
  let shapeGRest := shapeFRest.choose_spec
  let sameTail := shapeGRest.choose
  let sameTailRest := shapeGRest.choose_spec
  let originalBoard := sameTailRest.choose
  let originalBoardRest := sameTailRest.choose_spec
  let operator := originalBoardRest.choose
  let operatorRest := originalBoardRest.choose_spec
  let atDegree := operatorRest.choose
  let atDegreeRest := operatorRest.choose_spec
  let capAtRest := atDegreeRest.choose_spec
  let sized := capAtRest.2.2.1
  let rolePos := capAtRest.2.2.2
  have ms := profiled_original_measures (r:=r) (ctl:=ctl) X G S ordinary reset branch positive room shorten w fit
    drift degree payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined seed₁ placed₁ incoming words
  exact RegisterTimeline.measured_inherited_roles board op B p drift degree payload w (menu).ordinary (menu).seats
    (menu).profile (menu).header cur geoAt.capacity spaceAt geoAt recorded (oldArchive hw) (rank₀ hw)
    reset.menu (oldCode hw hr) positive hw.2 shapeN shapeH shapeF shapeG sameTail originalBoard operator
    atDegree admitted.1 admitted.2 history mid dst incoming ms bounds (shape₀ hw hb)
    old sized rolePos first ran

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
