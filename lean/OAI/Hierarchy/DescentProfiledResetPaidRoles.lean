import OAI.Hierarchy.DescentScheduledSelectedReady
import OAI.Hierarchy.DescentPostedResetCheckpoints
import OAI.Hierarchy.DescentRegisteredProfileMenu
import OAI.Hierarchy.DescentNamedArchivePrefix
import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentSevenPrimitiveRoles
import OAI.Hierarchy.DescentNamedPrimitiveVenue
import OAI.Hierarchy.DescentFreshArgumentRoom
import OAI.Hierarchy.DescentScheduledInheritedTokens

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ → Dated.Ordinary) (op : RotorSpec)
    (s Z : ℕ) (ports : Chronology.DatePorts) (floor : ℕ)
private theorem scheduledAtPorts_birth_arguments :
    (scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z ports floor).inner.successor.birth.arguments =
      S.retainedArgumentsAt G drift := rfl
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

/-! # Native primitive and funded rows on the actual selected reset at the next chronological date -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline DescentExteriorReplay ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section

open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
open scoped Classical Fin.CommRing
private def reachedCensusWords {F₁ P₁ : Type} [Field F₁] {dd : ℕ} {widths₁ : P₁ → ℕ}
    {world₁ : MarkedWorld F₁ dd P₁ widths₁} {gg : PoweredGadget F₁} {pr fe : ℝ}
    {sched : AtomSchedule} {kw age₀ grain degree₀ wire hist : ℕ}
    (node : Reached world₁ gg pr fe sched kw age₀ grain degree₀ wire hist) (wordBits : ℕ) :
    Fin (sched.hostSize age₀) → Fin (sched.groupCount age₀) → Fin (2^kw) → Cell wordBits :=
  Census.count (H:=sched.hostSize age₀) (G:=sched.groupCount age₀) node.placement (Equiv.refl _)
    (node.vertex.trans (Fin.castLEEmb node.valid.host)) wordBits

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset
def paidPublication
    {F₁ P₁ : Type} [Field F₁] {dd : ℕ} {widths₁ : P₁ → ℕ}
    {world₁ : MarkedWorld F₁ dd P₁ widths₁} {gg : PoweredGadget F₁} {pr fe : ℝ}
    {sched : AtomSchedule} {kw age₀ grain degree₀ wire hist drift : ℕ}
    (node : Reached world₁ gg pr fe sched kw (age₀+1) grain degree₀ wire hist)
    {stage : PhysicalReset} {floor w : ℕ} (u : stage.DateInputs floor w)
    (final : u.FinalInputs) {prev out : DatePorts}
    (layout : DatePorts.ResetPublicationGeometry gg sched age₀ drift prev out u)
    {desc : DescentKernelHistory.BitDescription world₁} (places : DatePorts.RangeRoom out node desc) (mid : Memory w) : Prop :=
  ∀ x : Fin stage.successor.metadata.chart.blocks,
    DescentPackedZip.Source (FinalInputs.paid u x)
      (fun (h : Fin stage.successor.metadata.chart.hosts) (g : Fin stage.successor.metadata.chart.groups) =>
        reachedCensusWords node stage.successor.metadata.paidBits
          ((h.cast (congrArg DescentDatedNodeMetadata.Chart.hosts layout.chart).symm).cast layout.hosts)
          ((g.cast (congrArg DescentDatedNodeMetadata.Chart.groups layout.chart).symm).cast places.groups.symm)
          ((x.cast (congrArg DescentDatedNodeMetadata.Chart.blocks layout.chart).symm).cast
            (congrArg (2^·) places.radix.symm)))
      stage.successor.metadata.chart.lanes (final.venueImage mid)


variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 600000
set_option maxRecDepth 18000
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

local notation:max "desc₁" hw:arg => ((nextPath).archive p positive (source).archive hw).bit
local notation:max "rank₁" hw:arg => trajectory p positive (source).archive (Origin.archiveOrder source) nextPath hw
local notation:max "shape₁" hw:arg hb:arg => archiveShape positive one₁ divides (source).archive firstShape nextPath hw hb
local notation:max "label₁" hw:arg hr:arg => (encodePath op reset.menu nextPath positive hw hr (source).archive rawCode).atNode

open DescentSIMDLookup DescentDatedNodeMetadata DescentResetGates DescentPacking.PackedMatch.Local.Stage
open DescentPackedResetRotorRoles DescentResetActorClass DescentRetainedRangeDigits
local notation "v" => (inner₁).successor
local notation "meta" => (v).metadata
local notation "l" => (v).birth.placement
local notation "lowBase" => (inner₁).rebased ((inner₁).stageStart padEnd)
local notation "location" => (v).actor.directory ((v).middle.stop lowBase)
local notation:max "oldArchive" hw:arg => before.archive p positive (source).archive (hw).1
local notation:max "oldCode" hw:arg hr:arg => encodePath op reset.menu before positive (hw).1 (hr).1 (source).archive rawCode
local notation:max "orig" hw:arg y:arg => resetOrigin B positive (hw).2 (oldArchive hw) y
local notation:max "prog" hw:arg => B.reset.laneRecipe (DescentOrderedReset.grains U B.count B.order) (B.reset.unit/p) p positive
  ((Nat.div_mul_cancel ((hw).2 : p∣B.reset.unit)).symm)
local notation:max "shape" hw:arg => B.reset.laneShape (DescentOrderedReset.grains U B.count B.order) (B.reset.unit/p) p positive
  ((Nat.div_mul_cancel ((hw).2 : p∣B.reset.unit)).symm)
local notation:max "node" geo:arg space:arg hw:arg => PhysicalReset.FinalInputs.nodeCell (z₁ geo space) B positive (hw).2 (oldArchive hw)
  (rank₀ hw) (by rfl) (by rfl) (by rfl)
local notation:max "gate" hw:arg hr:arg => reachedInput G s (S.grainAt G.b p 0) op reset.menu B positive (hw).2 (oldArchive hw) (oldCode hw hr)
local notation "actors" => B.next.vertex.trans (Fin.castLEEmb B.next.valid.host)
local notation "res" => B.reset.k-B.terminals.commonDepth
local notation "idxBits" => indexBits B.reset.n res
local notation:max "classEq" hn:arg => (show (v).birth.classBits=idxBits from by
  change indexBits n k=_
  exact congrArg₂ DescentResetActorClass.indexBits (B.dimension.trans hn).symm (ClosedReset.Window.calendar_residual B).symm)
local notation:max "kind" hn:arg h:arg => Fin.cast (congrArg (fun t : ℕ=>2^t) (classEq hn).symm)
  ((ClosedReset.Window.paidActorAt B h).elim 0 (fun actor=>indexed B.reset.graph res actor.val))

attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage Origin.archiveOrder Origin.archiveShape Palette.encodedOrigin

private theorem checkedProfiledPaidRoles {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
    {k cut tail n h C f g p : ℕ}
    (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
    (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
    (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
    (drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
    (walk : (last).Choice) (m : Memory w)
    {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
  {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}
  {n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
  (before : Path (trace walk).origin.source r) (B : ClosedReset r ctl)
  (after_ : Path B.next (trace walk).target) (_joined : (before.reset B).append after_=(trace walk).path)
    (hw : (nextPath).whole p) (hb : (nextPath).aligned p R₁) (hr : (nextPath).OnlyRotor op)
    (geo : data i) (space : support₁) (admitted : ready₁ geo.capacity space) (hn : n₁=n)
    (layout : DatePorts.ResetPublicationGeometry G S i drift (cur).ports (ports₁ space) (u₁ space))
    (places : DatePorts.RangeRoom (ports₁ space) B.next (desc₁ hw))
    (mid : Memory w) (first : (u₁ space).throughOperandDate.Runs atMem mid)
    (ran : (PhysicalReset.date (z₁ geo space)).Runs atMem dst)
    (actorMem : Memory w) (acted : (u₁ space).ThroughActors atMem actorMem)
    (choice : ∀ix,DatePorts.OrdinalRead (u₁ space) admitted.1 layout.small actorMem ix)
    (spans : DatePorts.SevenSpans (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
      (shape₁ hw hb) admitted.1 layout.small layout.axes actorMem choice)
    (empty : DatePorts.SevenVacant (u₁ space) B.next (desc₁ hw) (rank₁ hw) places
      admitted.1 layout.small layout.axes actorMem choice)
    (recorded:B.Recorded p) (tokens:(oldArchive hw).bit.Tokenized r.placement.records)
    (roots : RootRegister B positive hw.2 (oldArchive hw) (rank₀ hw) (v).birth (z₁ geo space).guards
      ((z₁ geo space).classImage mid) rfl rfl rfl)
    (venue : 0<(v).birth.sourceLanes ∧
      (z₁ geo space).venueImage mid ((location).count.base)=(Fintype.card B.next.V:Computability.VPVNP.BurstRAM.Word w) ∧
      (∀j:Fin (Fintype.card B.next.V),(z₁ geo space).venueImage mid ((location).inverse.base+j.val)=
        ((ClosedReset.Window.originalCompactName B (S.hostSize i) r.valid.host j).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      Fintype.card B.next.V<2^w ∧ (l).newHosts≤2^w ∧ Fintype.card B.next.V≤(location).inverse.size ∧
      (∀v₀,(B.next.placement.records v₀).length<2^(v).birth.paidBits) ∧
      DescentPackedZip.Source (PhysicalReset.FinalInputs.classWord (u₁ space)) (fun (laneHost : Fin (l).newHosts) (_ : Fin (l).groups) => kind hn laneHost) (l).lanes ((z₁ geo space).classImage mid) ∧
      ∀x:DescentColonies.Block k,DescentPackedZip.Source (.lookup (((v).venue.sources (PhysicalReset.FinalInputs.predecessor (u₁ space))
        ((v).fundedEnd lowBase)).paid x.val) .row)
        (fun (laneHost : Fin (l).newHosts) (laneGroup : Fin (l).groups) =>
          reachedCensusWords B.next (v).birth.paidBits laneHost laneGroup x)
        (l).lanes ((z₁ geo space).venueImage mid))
    (inherited:∀blockSlot nodeSlot,DescentPackedZip.Source ((z₁ geo space).roles.retained blockSlot nodeSlot)
      (fun laneHost laneGroup=>DescentResetPrimitivePage.oldWord (((node geo space hw) blockSlot nodeSlot laneHost laneGroup).elim .padding (gate hw hr)))
      (v).primitive.chart.lanes ((z₁ geo space).roleInput mid))
    (limit:R₁≤drift) :
    paidPublication (gg:=G) (sched:=S) (age₀:=i) (drift:=drift) B.next (u₁ space) (z₁ geo space) layout places mid ∧
    DatePorts.PrimitiveRolesAt (u₁ space) B.next (desc₁ hw) (rank₁ hw) places op (label₁ hw hr) dst:=by
  let active := venue.1
  let pop := venue.2.1
  let inv := venue.2.2.1
  let narrow := venue.2.2.2.1
  let roomAt := venue.2.2.2.2.1
  let saved := venue.2.2.2.2.2.1
  let fitRows := venue.2.2.2.2.2.2.1
  let cls := venue.2.2.2.2.2.2.2.1
  let pay := venue.2.2.2.2.2.2.2.2
  have argumentWidth : S.retainedArgumentsAt G drift = (v).birth.arguments :=
    (PhysicalReset.scheduledAtPorts_birth_arguments G S board k frozen i p f g drift degree payload (menu).ordinary
      op s (S.grainAt G.b p 0) (cur).ports (cur).floor).symm
  have rootN : 2*(2^res*2^B.reset.n)=(v).birth.roots :=
    congrArg₂ (fun a b : ℕ => 2*(2^a*2^b)) (ClosedReset.Window.calendar_residual B) (B.dimension.trans hn)
  have roleWidth : roleBits B.reset.n≤(v).primitive.rawBits :=
    (congrArg DescentPackedResetRotorRoles.roleBits (B.dimension.trans hn)).le
  have sign:=(DatePorts.reset_operand_word_room G S board k frozen i p f g drift degree payload (menu).ordinary
    op s (S.grainAt G.b p 0) (cur).ports (cur).floor w space admitted.1).2.2
  have posted := PhysicalReset.FinalInputs.from_seven_paid_roles
    (a:=inner₁) (floor:=(inner₁).stageStart padEnd) (w:=w) (u:=u₁ space)
    (P:=pins) (d:=0) (bits:=widths) (W:=U) (q:=price) (ε:=fee) (S:=S) (k:=k) (i:=i) (grain:=z)
    (D:=D) (wire:=S.epochPower^S.priceExponent) (n:=n₁) (h:=h₁) (C:=C₁) (f:=f₁) (g:=g₁) (cut:=cut₁)
    (tail:=tail₁) (p:=p) (prev:=r) (ctl:=ctl) (R:=R₁) (before:=atMem) (mid:=mid) («dst»:=dst)
    (z₁ geo space) reset.menu B positive hw.2 hr.2 (oldArchive hw) (oldCode hw hr)
    (rank₀ hw) rfl rfl rfl recorded tokens (classEq hn) rootN rfl rfl rfl rfl places (shape₀ hw hb)
    one₁ hb.2.1 hb.2.2.2 ran first admitted.1 admitted.2 layout.blocks roots active pop inv narrow roomAt
    saved fitRows cls pay
  have atLayout := posted (driftBudget:=drift) (cur).ports layout layout.nodeCount rfl rfl rfl rfl rfl rfl
  have gateCount (site : B.reset.bank.Site) (atom : ((prog hw) site).Node) :
      (((shape hw) site).recipe positive).arity atom ≤ (v).birth.arguments :=
    (B.fresh_calendar_arguments positive hw.2 drift (hb.2.2.2.trans limit) site atom).trans_eq argumentWidth
  have sameBits : (v).primitive.chart.bits = printedBits G s (S.grainAt G.b p 0) op := rfl
  -- Build this last application from its ten verified local arguments. The kernel
  -- checks each argument against the already specialized physical layout.
  run_tac Lean.Elab.Tactic.withMainContext do
    let app ← Lean.Meta.getFVarFromUserName `atLayout
    let args ← ([`gateCount, `sign, `actorMem, `acted, `choice, `spans, `empty, `inherited, `sameBits, `roleWidth].mapM
      Lean.Meta.getFVarFromUserName : Lean.MetaM (List Lean.Expr))
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkAppN app args.toArray)
    Lean.Elab.Tactic.replaceMainGoal []

private abbrev ProfiledPaidRolesType : Prop := type_of% @checkedProfiledPaidRoles

/-- The original physical root, node ordering and paid actor census yield the two
last native archive assertions, on the same registered date and posted ordinal choice. -/
theorem profiled_reset_paid_roles : ProfiledPaidRolesType := @checkedProfiledPaidRoles

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
