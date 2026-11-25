import OAI.Hierarchy.DescentFinalPrintedArchiveAfterMount
import OAI.Hierarchy.DescentProfiledTaggedArchiveAcquire
import OAI.Hierarchy.DescentNamedFinalPointerArchive
import OAI.Hierarchy.DescentNamedSeedPositionTagged
import OAI.Hierarchy.DescentOriginalFundedStageHost
import OAI.Hierarchy.DescentOriginalFundedSeed
import OAI.Hierarchy.DescentOriginalFinalEventPlacement
import OAI.Hierarchy.DescentTerminalHostISARoom
import OAI.Hierarchy.DescentTerminalHostWords
import OAI.Hierarchy.DescentNamedSeedChronology

namespace OAI
/-! # The final archived fields at the selected ballot on the purchased stage -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentTerminalEmitter DescentTerminalEmitter.Branch DescentTerminalChipRuntime
open DescentTerminalVertexFields DescentTerminalHeaderScatter DescentTerminalSiteShelves
open DescentTerminalScalarTransposes DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalScalarPadded DescentTerminalCompiledPrefix DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators
open DescentTerminalHost DescentTerminalThreshold DescentTerminalLast DescentTerminalRAM
open DescentTerminalReadout DescentTerminalFixedISAHost CorrectionFrame DescentTerminalChipPins
open ThreeFlat Routing Diagonal TraceBanks
open Computability.VPVNP.RAMMemory TaggedShorterControlHistory Tagged Tagged.SortLift TaggedShorterHistoryOrder
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false

open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentExterior DescentExteriorShelf DescentTerminalChipRuntime DescentTerminalChipPins
open ThreeFlat Routing
open scoped Classical BigOperators
section PurchasedCourseRelay
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<W*piece) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "s" => S.firstWidth G.b p
local notation "last" => Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b (W*piece) < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local instance : Fintype (ch).Pin := (ch).finite
variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
local notation "E" => Fintype.card (Port P X.width)
local notation "Old" => (ch).Pin ⊕ Hidden E j rest s
local notation "originalPins" => Port ((S.copies*s)*P) (CorrectionFrame.copiesWidth (S.copies*s) X.width)
local notation "mix" => fun c => Branch.publicLayout X G S (trace c) positive base width
local notation "power" => NativeBranch.copy_power S (radix:=ordinary.radix) base width


private theorem chosenByRead {Seed Label Choice : Type} {bits : Label → Seed → Bool}
    {ok : (Seed → Bool) → Prop} {src : Choice → Label}
    (rack : DescentTerminalEpochChart.Chart bits ok src) (path : DescentTerminalEpochChart.Route rack)
    (votes : rack.Pin → Bool) (c : Choice) (hit : rack.read votes=some c) :
    c=path.follow votes :=
  ((congrArg path.follow ((rack.read_iff votes c).mp hit)).trans (path.stored c)).symm


open Chronology RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
variable {hostArity hostDegree : ℕ} (b : RegisterTimeline.Menu hostArity hostDegree)
  (initial : RegisterTimeline.Position) (gain : b.gain=g) (grain : b.p=W*piece) (arity : b.f=f)
local notation "traces₀" => traceAt X G S ordinary reset branch positive room shorten
local notation "cpu₀" => RegisterTimeline.instruction (w:=w) traces₀ b initial
local notation "cursor₀" => RegisterTimeline.calendar (w:=w) traces₀ b initial
local notation "dates₀" => RunTrace.machine traces₀ (fun i _ => cpu₀ i)
variable (pre : Geometry G S b k w 0 initial)
variable (places : ∀i (e : RunTrace.Events (traceAt X G S ordinary reset branch positive room shorten) i),
  fitsAt (traceAt X G S ordinary reset branch positive room shorten) b initial (w:=w) i e)

attribute [local irreducible] terminalArchive
include gain grain arity pre places in
private theorem archiveOfWideCourse (x : originalPins → Bool) (votes : Old → Bool) (c : (last).Choice) (m : Memory w)
    (ok : wideChoicePrior X G S ordinary reset branch positive room shorten w fit base width x votes=some c)
    (bootstrap : let walk := (show DescentTerminalEpochChart.Route ch from
      normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow (votes∘Sum.inl);
      (ch).read (votes∘Sum.inl)=some walk → initialTagged X G S ordinary reset branch positive room shorten w initial walk m)
    (course : let walk := (show DescentTerminalEpochChart.Route ch from
      normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow (votes∘Sum.inl);
      OriginalCourse traces₀ b initial walk m ((ch).rows (votes∘Sum.inl)).length ((ch).read (votes∘Sum.inl)=some walk))
    (steps : let walk := (show DescentTerminalEpochChart.Route ch from
      normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow (votes∘Sum.inl);
      datedArchiveSteps X G S ordinary reset branch positive room shorten w fit b initial (votes∘Sum.inl) walk m) :
    terminalArchive X G S ordinary reset branch positive room shorten w c (cursor₀ S.length)
      (DateCode.history dates₀ m S.length) := by
  let readVotes := votes ∘ Sum.inl
  let walk := (show DescentTerminalEpochChart.Route ch from
    normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow readVotes
  have chosen : (ch).read readVotes=some c :=
    ((DescentExteriorShelf.proposed_eq (ch).read mix (DescentExterior.publicRows X
      (Branch.copyInput X s power x)) votes c).mp ok).1
  have agrees : c=walk := chosenByRead ch (normalizedRoute X G S ordinary reset branch positive room shorten w fit)
    readVotes c chosen
  have live : (ch).read readVotes=some walk := chosen.trans (congrArg some agrees)
  let holds (u : (last).Choice) := terminalArchive X G S ordinary reset branch positive room shorten w u
    (cursor₀ S.length) (DateCode.history dates₀ m S.length)
  exact (congrArg holds agrees).mpr (terminal_archive_from_dates X G S ordinary reset branch positive room
    shorten w fit b initial gain grain arity pre places readVotes walk m (bootstrap live)
    (fun i e _ => course.advance i e) steps live)

end PurchasedCourseRelay

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F)
private abbrev archiveStage (rounds f g restart τ β sites payload : ℕ) :=
  let depth := Nat.log 2 payload / (2*β)
  stageNumbers G rounds depth f g restart sites (DescentCompiler.TerminalScale.tail τ depth)

private abbrev archiveGroupBits (rounds f g restart β payload : ℕ) :=
  groupBits rounds (Nat.log 2 payload / (2*β)) (hostRate rounds restart)
    (capRate G rounds g) (cutRate rounds f g)

section FundedCalendar

open DescentCompiler.TerminalScale DescentDatedAddressBook DescentDatedSeedStartup DescentSeedRoot
open DescentWideSeedFlags DescentTerminalLocalPortBook DescentTerminalFixedSlices Chronology RegisterTimeline

variable {n d:ℕ} (board:NonlinearExpanders.Graph n d)
  (op:RotorSpec) (t f g rate cut drift limit τ β h:ℕ) (x:ShellSource F h)
  (branch:G.b≤2^(capRate G t g)) (head dates W:ℕ)
local notation "J" => Nat.log 2 h/(2*β)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g rate x.sites tb
local notation "k" => groupBits t J (hostRate t rate) (capRate G t g) (cutRate t f g)
local notation "p" => headGrain G S k h
local notation "s" => (S).firstWidth G.b p
local notation "W₀" => NativeBranch.binLimit («k»:=k) S
local notation "q" => headArity G S
local notation "w" => W*h
variable (ordinary : OrdinaryRates G (archiveStage G t f g rate τ β x.sites h)
    (archiveGroupBits G t f g rate β h) cut)
  (reset : ResetRates G (archiveStage G t f g rate τ β x.sites h) (archiveGroupBits G t f g rate β h)
    (atRound t) n d op.C f g cut (TerminalScale.tail τ (Nat.log 2 h / (2*β))))
  (positive : 0 < headGrain G (archiveStage G t f g rate τ β x.sites h)
    (archiveGroupBits G t f g rate β h) h)
  (shorten : reentryRate d op.C*(1-(2-G.rate)/4)^t ≤ 1/2)
  (fit : let schedule := archiveStage G t f g rate τ β x.sites h
         schedule.firstWidth G.b (headGrain G schedule (archiveGroupBits G t f g rate β h) h) < 2^(W*h))
  (H degree wire hist:ℕ)
local notation "trace" => traceAt x.X G S ordinary reset branch positive x.opened shorten
local notation "chart" => normalizedPackedChart x.X G S ordinary reset branch positive x.opened shorten w fit
local notation "ss" => (chart).layout
local notation "bins" => terminalBinCount x.X G S p q W₀ n d op.C f g+1
local notation "raw" => terminalRawRows x.X G S p q n d op.C f g
local notation "V" => originalSeedHead G op drift x.X ss S k tb h H degree wire hist bins raw
local notation "origin" => (V).position G op t f g drift h
local notation "lo" => selectorBase x.X (S).copies s h (ss).length
local notation "header" => (V).base G h-1
local notation "menu" => fromProfiles G S board op k tb p f g drift degree h lo header ss

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem fundedCalendarOfSeed (budget : OriginalFundedSeed G board op t f g rate cut drift limit τ β h
    x branch head dates W ordinary reset positive shorten fit H degree wire hist) (coeff : degree ≤ limit)
    (i : ℕ) (e : RunTrace.Events trace i) :
    RegisterTimeline.fitsAt trace menu origin («w»:=w) i e :=
  (profiled_calendar_at_rate x.X G t rate τ β x.sites h ordinary reset branch positive x.opened shorten
    w fit board op drift degree limit lo header origin dates head budget.grant budget.old budget.returned
    budget.receiver budget.growth x.upper budget.input coeff budget.first budget.geometry budget.groups
    budget.headerFits budget.machine i e).1

end FundedCalendar

attribute [local irreducible] Origin.source Origin.archivePackage normalizedPackedChart SeedNamed.issued

variable {n h C f g : ℕ} (rounds restart τ β siteCount payloadBits : ℕ)
variable (opened:10*(X.size+1)≤ siteCount) (smaller:siteCount≤(2^payloadBits)^2)
  (low:2^payloadBits≤ siteCount) (dyadic:∃a,siteCount=2^a)
local notation "cut" => cutRate rounds f g
local notation "src_" => (⟨cp,P,siteCount,X,opened,smaller⟩:ShellSource F payloadBits)
local notation "depth_" => Nat.log 2 payloadBits/(2*β)
local notation "tail" => DescentCompiler.TerminalScale.tail τ depth_
local notation "S" => stageNumbers G rounds depth_ f g restart siteCount tail
local notation "k" => groupBits rounds depth_ (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g)
local notation "W" => NativeBranch.binLimit («k»:=k) S
local notation "j" => Nat.clog 2 (NativeBranch.localLimit G S)
local notation "q" => 2^j*(G.b^(rounds*depth_)*G.b)
local notation "piece" => payloadBits/(16*(q*W))
local notation "rest" => (S).groupWidth k tail 0+k-2*j
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G (archiveStage G rounds f g restart τ β siteCount payloadBits)
    (archiveGroupBits G rounds f g restart β payloadBits) (cutRate rounds f g))
  (reset : ResetRates G (archiveStage G rounds f g restart τ β siteCount payloadBits)
    (archiveGroupBits G rounds f g restart β payloadBits) (atRound rounds) n h C f g (cutRate rounds f g)
    (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits / (2*β))))
variable (branch : G.b ≤ 2^(capRate G rounds g))
  (positive : 0 < headGrain G (archiveStage G rounds f g restart τ β siteCount payloadBits)
    (archiveGroupBits G rounds f g restart β payloadBits) payloadBits)
  (room : 10*(X.size+1) ≤ siteCount)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
local notation "s" => (S).firstWidth G.b p
local notation "Z" => (S).grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => (S).epochPower^(S).localTokenExponent
local notation "venues" => (S).groupCount (S).length*2^k

variable (base : (archiveStage G rounds f g restart τ β siteCount payloadBits).baseGroups = 2^(DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits / (2*β))))
  (width : let sched := archiveStage G rounds f g restart τ β siteCount payloadBits
           let depthBits := archiveGroupBits G rounds f g restart β payloadBits
           sched.groupWidth depthBits (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits / (2*β))) 0 + depthBits =
             headChunk G sched + (headChunk G sched + headRest G sched depthBits (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits / (2*β)))))
variable (age : 0 < Nat.log 2 payloadBits / (2*β))

open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalExteriorPackets DescentTerminalPublicIdentity
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall DescentPackedProfileTape
open DescentSeedRoot DescentExteriorShelf DescentTerminalPrimitiveArena
local notation "E₀" => Fintype.card (Port P X.width)
local notation "H₀" => (S).hostSize (S).length
local notation "count₀" => E₀*2^(j+rest)
local notation "rawWords" => terminalRawRows X G S p q n h C f g
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact
open DescentTerminalLocalPortBook DescentTerminalSpanBook DescentTerminalBinPack
open DescentTerminalPreflightSpace ThreeFlat.RAM PhysicalProcedure

open DescentPackedEpochFold DescentExteriorMatrixUpdate DescentPackedSeed DescentSeedRoot
open ThreeFlat Routing Diagonal
variable (ratio₀:ℕ)
local notation "w" => ratio₀*payloadBits
variable (fit : let sched := archiveStage G rounds f g restart τ β siteCount payloadBits
                let depthBits := archiveGroupBits G rounds f g restart β payloadBits
                sched.firstWidth G.b (headGrain G sched depthBits payloadBits) < 2^(ratio₀*payloadBits))
local notation "K" => calibratedBins X G rounds depth_ f g restart siteCount τ payloadBits n h C
local notation "chart" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "steps" => (chart).layout
local notation "lo" => DescentWideSeedFlags.selectorBase X (S).copies s payloadBits (steps).length
local notation "packWidth" => DescentPackedEpochShelves.grain (payloadBits/2) G.C
local notation "matrixAt" => end_ (lo+extent packWidth steps) G.C packWidth
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentResetInvoice CorrectionBatch
open DescentSixParty.SeedNamed.Branch DescentExteriorReplay DescentTerminalFixedSlices
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup DescentPackedColony
open ThreeFlat.Routing CallPool DescentColonies DescentActorRaster DescentColonies.SplitRAM
open DescentTerminalRoleTables DescentTerminalPointerIssue
open Chronology DescentDatedSeedStartup.Input DescentTerminalEpochDecoder
variable (headRate_ datesRate_ codeRate_ lastRate_ slots_:ℕ)
local notation "dateDegree" => maximumDegree (rounds+1)
local notation "board" => reset.board
local notation "bootHosts" => siteCount
local notation "seedWire_" => (S).epochPower^(S).priceExponent
local notation "seedHist_" => s
local notation "vhead_" => originalSeedHead G rot R X steps S k tail payloadBits bootHosts dateDegree seedWire_ seedHist_
  (terminalBinCount X G S p q W n h C f g+1) rawWords
local notation "startup" => (vhead_).layout G rounds f g R payloadBits
local notation "startingHeader" => (vhead_).base G payloadBits-1
variable (funding : let ret := max 1 (max reset.bitsR (C*reset.bitsR))
                    OriginalWord G reset.board (RotorSpec.ofRates reset) rounds f g restart (cutRate rounds f g)
                      ret (maximumDegree (rounds+1)) branch headRate_ datesRate_ codeRate_ lastRate_
                      ratio₀ τ β payloadBits (ret+1) slots_)
local notation "heads_" => original_funded_seed G board rot rounds f g restart cut R dateDegree τ β payloadBits src_ branch
  headRate_ datesRate_ codeRate_ lastRate_ ratio₀ slots_ ordinary reset positive shorten fit siteCount
  dateDegree seedWire_ seedHist_ funding low dyadic le_rfl (Nat.le_pow_clog (by decide : 1<2) siteCount)
local notation "hostsEnough" => (heads_).hosts
local notation "primitiveLanes_" => DescentDatedSeedStartup.Primitive.paletteLanes G rot (startup).seedWidth Z payloadBits k
local notation "initialSource_" => DescentPackedSeed.Primitive.Source.jobs X (S).copies (startup).seedWidth payloadBits
local notation "seedEnd_" => (DescentDatedSeedStartup.Input.nodeChart startup k bootHosts ((S).groupCount 0)).seedEnd
  (DescentDatedSeedStartup.endAddress X startup bootHosts ((S).groupCount 0) k)
local notation "initialBound_" => DescentDatedSeedStartup.Primitive.initialEnd X (S).copies (startup).seedWidth payloadBits k
  bootHosts ((S).groupCount 0) primitiveLanes_ seedEnd_

local notation "entry_" => (⟨DatePorts.initial G rot X (S).copies startup k bootHosts ((S).groupCount 0) payloadBits Z,
    initialBound_⟩ : RegisterTimeline.Position)
local notation "traces_" => traceAt X G S ordinary reset branch positive room shorten
local notation "menu_" => RegisterTimeline.fromProfiles G S board rot k tail p f g R dateDegree payloadBits lo startingHeader steps
local notation "cursor_" => RegisterTimeline.calendar («w»:=w) traces_ menu_ entry_
local notation "datesAt" => RunTrace.machine traces_ (fun i _=>RegisterTimeline.instruction («w»:=w) traces_ menu_ entry_ i)
local notation "arity" => max 8 (2^(S).capGain)
local notation "groups" => cap
local notation "stride" => R
local notation "oldTags" => DescentPrimitivePalette.colors G s Z rot
local notation "tagCount" => DescentBundleTagKeys.capacity oldTags arity groups p stride
local notation "codes" => DescentTerminalScalarHeader.range q tagCount cap nodeCap cap p venues
local notation "seed" => (chart).seed
local notation "clockCap" => G.C
local notation "front" => end_ (lo+extent packWidth steps) clockCap packWidth+17*DescentExteriorShelf.span j rest s E₀
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rawWords count₀
local notation "Full" => DescentTerminalFullPins.Candidate ((chart).Pin⊕Hidden E₀ j rest s) K W q piece rawWords
local notation "power" => NativeBranch.copy_power S (radix:=ordinary.radix) base width
local notation "extPins" => Port (((S).copies*s)*P) (copiesWidth ((S).copies*s) X.width)
local notation "view" x₀:arg => Branch.copyInput X s power x₀
local notation "packedBallot" x₀:arg z₀:arg => Root.widePackedImage X (S).copies s payloadBits w seed lo G.C packWidth steps matrixAt
      (DescentExterior.publicRows X (view x₀)) (Sum.elim (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
      (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr))
local notation "bootFor" x₀:arg z₀:arg => Root.appended front extra (packedBallot x₀ z₀)
    (DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀)

local notation "histAt" z₀:arg => (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
local notation "checkedAt" x₀:arg z₀:arg => DescentWideSeedFlags.countedAt X (S).copies s payloadBits seed
  (histAt z₀) (bootFor x₀ z₀)
local notation "startedAt" x₀:arg z₀:arg => completeImage G rot X ((S).initialDigits ordinary.radix) hostsEnough startup
  startingHeader payloadBits Z (checkedAt x₀ z₀)
local notation "lastAt" x₀:arg z₀:arg => DateCode.history datesAt (startedAt x₀ z₀) (S).length
local notation "selectedAt" z₀:arg => (show DescentTerminalEpochChart.Route chart from normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow (histAt z₀)
local notation "honestAt" z₀:arg => issued X G S ordinary reset branch positive room shorten (selectedAt z₀)
local notation "candidatePrior" => wideChoicePrior X G S ordinary reset branch positive room shorten w fit base width

local notation "externalRows" x₀:arg => DescentExterior.publicRows X (view x₀)
local notation "ballot" z₀:arg => Sum.elim (histAt z₀) (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr)
local notation "appended" z₀:arg => DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀
local notation "bootTagged" x₀:arg z₀:arg => initialTagged X G S ordinary reset branch positive room shorten w
  entry_ (selectedAt z₀) (startedAt x₀ z₀)
local notation "acquired" x₀:arg z₀:arg => datedArchiveSteps X G S ordinary reset branch positive room shorten w fit
  menu_ entry_ (histAt z₀) (selectedAt z₀) (startedAt x₀ z₀)

/-- An unused suffix of a reserved memory range contains zeros. -/
private theorem zeroPaddedAppendix {bits : ℕ} (prefixSize paid reserved : ℕ) (fits : paid ≤ reserved)
    (image appendix : Memory bits) :
    Root.appended prefixSize reserved image (Computability.VPVNP.RAMMemory.initialMemory paid appendix) = Root.appended prefixSize paid image appendix := by
  funext address
  by_cases before : address < prefixSize
  · rw [Root.append_low _ _ _ _ before, Root.append_low _ _ _ _ before]
  by_cases used : address < prefixSize+paid
  · have inside : address < prefixSize+reserved := by omega
    have old : address-prefixSize < paid := by omega
    simp [Root.appended,Computability.VPVNP.RAMMemory.initialMemory,used,inside,before,old]
  · have unused : ¬address-prefixSize < paid := by omega
    by_cases inside : address < prefixSize+reserved <;> simp [Root.appended,Computability.VPVNP.RAMMemory.initialMemory,used,inside,before,unused]

private theorem decodeBitsFromChart {copies lanes bits : ℕ} {Labels : Type}
    {sourceLabel : Labels → (initialGroup X copies lanes).Choice}
    (rack : DescentTerminalEpochChart.Chart (selectBit X («R»:=copies) («s»:=lanes) bits)
      (valid X («R»:=copies) («s»:=lanes)) sourceLabel) (fits : lanes < 2^bits)
    (votes : rack.Pin → Bool) (choice : Labels) (hit : rack.read votes=some choice)
    (target : (initialGroup X copies lanes).Choice) (same : sourceLabel choice=target) :
    DescentSeedRoot.decode X (votes ∘ rack.seed) = some target := by
  apply (DescentSeedRoot.decode_iff X fits _ _).2
  exact (funext fun i => (congrFun ((rack.read_iff votes choice).mp hit) (rack.seed i)).trans
    (rack.original choice i)).trans (congrArg (selectBit X bits) same)

set_option maxHeartbeats 1200000 in
private theorem decodePurchasedBallot (votes : (chart).Pin → Bool) (choice : (last).Choice)
    (hit : (chart).read votes = some choice) :
    DescentSeedRoot.decode X (votes ∘ (chart).seed) =
      some (Chronology.epochsSource G (cert).choose choice) :=
  decodeBitsFromChart X chart fit votes choice hit _
    (seedTrunk G _ _ (cert).choose choice).symm

include funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- True public instruction bounds on each offered date of the purchased ballot. -/
theorem purchased_calendar_placed (i:ℕ) (e:RunTrace.Events traces_ i):
    RegisterTimeline.fitsAt traces_ menu_ entry_ («w»:=w) i e :=
  fundedCalendarOfSeed G board rot rounds f g restart cut R dateDegree τ β payloadBits src_ branch
    headRate_ datesRate_ ratio₀ ordinary reset positive shorten fit siteCount dateDegree seedWire_ seedHist_
    heads_ le_rfl i e

attribute [local semireducible] normalizedPackedChart

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem paidAppendixBound :
    extra ≤ (vhead_).appendix.words count₀ :=
  DescentTerminalPublicIdentity.total_mono_bins (Nat.le_succ K) W q piece codes rawWords count₀

local notation "paddedBack" z₀:arg => Computability.VPVNP.RAMMemory.initialMemory extra (appended z₀)
local notation "reservedBallot" x₀:arg z₀:arg => Root.appended front ((vhead_).appendix.words count₀)
  (packedBallot x₀ z₀) (paddedBack z₀)
local notation "initMemory" z₀:arg heap:arg => completeImage G rot X ((S).initialDigits ordinary.radix) hostsEnough
  startup startingHeader payloadBits Z (DescentWideSeedFlags.countedAt X (S).copies s payloadBits seed (histAt z₀) heap)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem archiveStartFromReserved (x₀:extPins→Bool) (z₀:Full→Bool)
    (readback : initialTagged X G S ordinary reset branch positive room shorten w entry_ (selectedAt z₀)
      (initMemory z₀ (reservedBallot x₀ z₀))) : bootTagged x₀ z₀ := by
  let holds (heap : Memory w) := initialTagged X G S ordinary reset branch positive room shorten w entry_
    (selectedAt z₀) (initMemory z₀ heap)
  have sameBallot : reservedBallot x₀ z₀ = bootFor x₀ z₀ :=
    zeroPaddedAppendix front extra ((vhead_).appendix.words count₀)
      (paidAppendixBound X G rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten ratio₀ fit)
      (packedBallot x₀ z₀) (appended z₀)
  exact (congrArg holds sameBallot).mp readback

include age funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in
/-- Read the actual tag, arity and seven operand fields on the counted seed of the accepted run. -/
theorem purchased_archive_start (x₀:extPins→Bool) (z₀:Full→Bool)
    (hit:(chart).read (histAt z₀)=some (selectedAt z₀)) : bootTagged x₀ z₀ :=by
  let b:=honestAt z₀
  have decoded : DescentSeedRoot.decode X ((ballot z₀ ∘ Sum.inl) ∘ seed) =
      some (Chronology.epochsSource G (cert).choose (selectedAt z₀)) :=
    decodePurchasedBallot X G rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten
      ratio₀ fit (histAt z₀) (selectedAt z₀) hit
  have supply:=funding.calendar.words.seed siteCount low smaller dyadic X ordinary reset positive opened shorten
    w fit siteCount dateDegree seedWire_ seedHist_ le_rfl (Nat.le_pow_clog (by decide:1<2) siteCount)
    funding.calendar.words.seedFits
  have operand:0<(startup).operandLanes:=(funding.seedOperandLanes siteCount dateDegree p (heads_).input le_rfl).2
  apply archiveStartFromReserved (X:=X) (G:=G) (ordinary:=ordinary) (reset:=reset) (fit:=fit)
    (opened:=opened) (smaller:=smaller) (low:=low) (dyadic:=dyadic)
    (funding:=funding) (base:=base) (width:=width) (x₀:=x₀) (z₀:=z₀)
  exact (vhead_).position_tagged G rot rounds f g R payloadBits ordinary.radix hostsEnough seed
    (externalRows x₀) (ballot z₀) (paddedBack z₀) b.origin positive (le_max_left ..) reset.menu b.target b.path
    board supply base age branch operand decoded

include funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
/-- The selected startup preserves every packed original ballot and separates the paid private header. -/
theorem purchased_archive_grains (words:HostWordRoom G S k tail p j ratio₀ payloadBits)
    (x₀:extPins→Bool) (z₀:Full→Bool) :
    lo+extent packWidth steps≤ startingHeader ∧ startingHeader<(entry_).floor ∧
      ∀ a ∈ shelves packWidth lo 0 steps, ∀ i : Fin (DescentPackedProfileTape.slots a.src.seats packWidth),
        (startedAt x₀ z₀) (a.base+i.val)=((packed a.src.pin (histAt z₀) packWidth i.val).val:Computability.VPVNP.BurstRAM.Word w) :=by
  have headPaid:=original_head_placement G board rot rounds f g restart cut R τ β payloadBits src_
    branch ratio₀ ordinary reset positive shorten fit siteCount dateDegree seedWire_ seedHist_ K (Nat.le_succ _)
  have starts:DescentWideSeedFlags.endInput X (S).copies s payloadBits+
      (DescentPackedSeed.rows X (S).copies s payloadBits+1)≤lo:= (Nat.add_assoc ..).symm.le.trans (Nat.le_add_right ..)
  exact
    complete_appended_profile_after G rot X ((S).initialDigits ordinary.radix) hostsEnough startup startingHeader
      payloadBits Z s seed lo G.C packWidth steps matrixAt extra (externalRows x₀) (ballot z₀) (appended z₀)
      words.seedWord (heads_).source (heads_).live (heads_).embed (heads_).signed (heads_).fields starts
      le_rfl headPaid.archiveEnd (heads_).low (heads_).boot

include age funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
set_option cleanup.letToHave false in
/-- The register at the final calendar date is on the same accepted input and memory as the host. -/
theorem purchased_archive_from_steps (words:HostWordRoom G S k tail p j ratio₀ payloadBits)
    (dates:StageDateResources G rot rounds f g restart R dateDegree n h τ β payloadBits siteCount w)
    (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
    (accepted:candidatePrior x₀ (erased z₀)=some c₀) (steps_:acquired x₀ z₀) :
    terminalArchive X G S ordinary reset branch positive room shorten w c₀ (cursor_ (S).length) (lastAt x₀ z₀) :=by
  let saved := purchased_archive_grains X G rounds restart τ β siteCount payloadBits
    opened smaller low dyadic ordinary reset branch positive room shorten base width ratio₀ fit
    headRate_ datesRate_ codeRate_ lastRate_ slots_ funding words x₀ z₀
  let paidClaim := profiled_original_course (driftR:=R+1) (ratio:=ratio₀) X G rounds restart τ β
    siteCount payloadBits ordinary reset branch positive room shorten w fit R dateDegree dateDegree lo startingHeader entry_
  let course := paidClaim datesRate_ headRate_ (heads_).grant (heads_).old (heads_).returned (heads_).receiver
    (heads_).growth smaller (heads_).input le_rfl (heads_).first (heads_).geometry (heads_).groups
    (heads_).headerFits (heads_).machine dates.matcher dates.signed dates.palette W (2^j) (Nat.two_pow_pos _) rfl
    saved.1 saved.2.1 (histAt z₀) (startedAt x₀ z₀) saved.2.2 (heads_).observations (heads_).degree dates.degree dates.snapshot
  have placed : ∀i (e : RunTrace.Events traces_ i),RegisterTimeline.fitsAt traces_ menu_ entry_ («w»:=w) i e :=
    fun i e => purchased_calendar_placed X G rounds restart τ β siteCount payloadBits opened smaller low dyadic
      ordinary reset branch positive room shorten ratio₀ fit headRate_ datesRate_ codeRate_ lastRate_ slots_ funding i e
  have startupRead : (chart).read (histAt z₀)=some (selectedAt z₀) → bootTagged x₀ z₀ :=
    fun hit => purchased_archive_start (X:=X) (G:=G) (branch:=branch) (positive:=positive) (ordinary:=ordinary) (reset:=reset) (base:=base)
      (width:=width) (age:=age) (room:=room) (shorten:=shorten) (funding:=funding)
      (opened:=opened) (low:=low) (dyadic:=dyadic) (smaller:=smaller) (fit:=fit) (x₀:=x₀) (z₀:=z₀) (hit:=hit)
  exact archiveOfWideCourse X G S ordinary reset branch positive room shorten w fit base width menu_ entry_ rfl rfl rfl
    (heads_).geometry placed x₀ (erased z₀) c₀ (startedAt x₀ z₀) accepted startupRead course steps_


run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env (["purchased_terminal_archive", "purchased_pointer_from_terminal", "purchased_final_pointer_archive", "purchased_printed_from_terminal", "purchased_final_printed_archive", "purchasedRoleFromTerminal", "purchased_final_role_archive"] ++ ·)

include age funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in
/-- Recover the full semantic archive on the literal final heap for each accepted ballot. -/
theorem purchased_terminal_archive (words:HostWordRoom G S k tail p j ratio₀ payloadBits)
    (dates:StageDateResources G rot rounds f g restart R dateDegree n h τ β payloadBits siteCount w)
    (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
    (accepted:candidatePrior x₀ (erased z₀)=some c₀) :
    terminalArchive X G S ordinary reset branch positive room shorten w c₀ (cursor_ (S).length) (lastAt x₀ z₀) :=by
  apply purchased_archive_from_steps (X:=X) (G:=G) (branch:=branch) (positive:=positive) (ordinary:=ordinary) (reset:=reset) (room:=room) (shorten:=shorten)
    (funding:=funding) (opened:=opened) (low:=low) (dyadic:=dyadic) (smaller:=smaller) (fit:=fit)
    (base:=base) (width:=width) (age:=age) (words:=words) (dates:=dates) (x₀:=x₀) (z₀:=z₀)
    (c₀:=c₀) (accepted:=accepted)
  have grains := purchased_archive_grains (X:=X) (G:=G) (branch:=branch) (positive:=positive)
    (ordinary:=ordinary) (reset:=reset) (room:=room) (shorten:=shorten) (funding:=funding)
    (opened:=opened) (low:=low) (dyadic:=dyadic) (smaller:=smaller) (fit:=fit)
    (base:=base) (width:=width) (words:=words) (x₀:=x₀) (z₀:=z₀)
  have supply:=funding.calendar.words.seed siteCount low smaller dyadic X ordinary reset positive opened shorten
    w fit siteCount dateDegree seedWire_ seedHist_ le_rfl (Nat.le_pow_clog (by decide:1<2) siteCount)
    funding.calendar.words.seedFits
  have roles:=(vhead_).position_role_rows G rot rounds f g R payloadBits board supply
  have originSize:Fintype.card (honestAt z₀).origin.source.V≤(entry_).ports.operandHosts:=
    (honestAt z₀).origin.source.valid.host.trans (heads_).geometry.room.population.venue_low
  intro i e state incoming prior tags required
  exact profiled_tagged_archive_acquire X G rounds restart τ β siteCount payloadBits ordinary reset branch positive
    room shorten w fit R dateDegree dateDegree lo startingHeader entry_ datesRate_ headRate_
    (heads_).grant (heads_).old (heads_).returned (heads_).receiver (heads_).growth smaller
    (heads_).input le_rfl (heads_).first (heads_).geometry (heads_).groups (heads_).headerFits (heads_).machine
    dates.matcher dates.signed dates.palette W (2^j) (Nat.two_pow_pos _) rfl grains.1 grains.2.1
    (histAt z₀) (startedAt x₀ z₀) grains.2.2 (heads_).observations (heads_).degree dates.degree dates.snapshot roles le_rfl originSize dates.walks i e state incoming prior tags required

attribute [local irreducible] normalizedPackedChart

local notation "lastPrior" => cursor_ ((S).length-1)
private abbrev archiveResetSpace (schedule : AtomSchedule) {vertices degree : ℕ}
    (book : RegisterTimeline.Menu vertices degree) (depth bits : ℕ) (previous : RegisterTimeline.Position) :=
  PhysicalReset.ScheduledCodeRoom G schedule book.board depth book.tail (schedule.length-1) book.p book.f
    book.gain book.drift book.degreeLimit book.payload book.ordinary book.op (schedule.firstWidth G.b book.p)
    (schedule.grainAt G.b book.p 0) previous.ports.operandLanes previous.ports.roleLanes previous.ports.venue
    previous.ports.io (previous.ports.priorStart depth previous.floor) bits (previous.ports.afterPad depth previous.floor).archive

private def archiveResetPorts (schedule : AtomSchedule) {vertices degree : ℕ}
    (book : RegisterTimeline.Menu vertices degree) (depth bits : ℕ) (previous : RegisterTimeline.Position)
    (space : archiveResetSpace G schedule book depth bits previous) : DatePorts :=
  DatePorts.resetPorts G schedule book.board depth book.tail (schedule.length-1) book.p book.f book.gain book.drift
    book.degreeLimit book.payload book.ordinary book.op (schedule.firstWidth G.b book.p)
    (schedule.grainAt G.b book.p 0) previous.ports previous.floor bits space

local notation "lastSpace" => archiveResetSpace G S menu_ k w lastPrior
local notation "lastPorts" sp:arg => archiveResetPorts G S menu_ k w lastPrior sp

attribute [local irreducible] FinalPrintedArchive FinalPointerArchive terminalArchive

include age funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3400000 in
set_option cleanup.letToHave false in
/-- Identify the archive with the registers returned by the last selected reset instruction. -/
theorem purchased_pointer_from_terminal (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
    (obtained:terminalArchive X G S ordinary reset branch positive room shorten w c₀ (cursor_ (S).length)
      (lastAt x₀ z₀)) :
    ∃sp:lastSpace,(cursor_ (S).length).ports=lastPorts sp ∧
      FinalPointerArchive X G S ordinary reset branch positive room shorten w c₀ (lastPorts sp) (lastAt x₀ z₀) :=
  final_pointer_register X G S ordinary reset branch positive room shorten w menu_ entry_ rfl rfl rfl
    (heads_).geometry (fun i e => purchased_calendar_placed X G rounds restart τ β siteCount payloadBits
      opened smaller low dyadic ordinary reset branch positive room shorten ratio₀ fit
      headRate_ datesRate_ codeRate_ lastRate_ slots_ funding i e)
    c₀ (startedAt x₀ z₀) age obtained

include age funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- Recover the submitted final pointer sources at the unique scheduled reset register. -/
theorem purchased_final_pointer_archive (words:HostWordRoom G S k tail p j ratio₀ payloadBits)
    (dates:StageDateResources G rot rounds f g restart R dateDegree n h τ β payloadBits siteCount w)
    (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
    (accepted:candidatePrior x₀ (erased z₀)=some c₀) :
    ∃sp:lastSpace,(cursor_ (S).length).ports=lastPorts sp ∧
      FinalPointerArchive X G S ordinary reset branch positive room shorten w c₀ (lastPorts sp) (lastAt x₀ z₀) :=by
  apply purchased_pointer_from_terminal (X:=X) (G:=G) (branch:=branch) (positive:=positive) (ordinary:=ordinary) (reset:=reset)
    (room:=room) (shorten:=shorten) (funding:=funding) (opened:=opened) (low:=low) (dyadic:=dyadic)
    (smaller:=smaller) (fit:=fit) (base:=base) (width:=width) (age:=age) (x₀:=x₀) (z₀:=z₀) (c₀:=c₀)
  exact purchased_terminal_archive (X:=X) (G:=G) (branch:=branch) (positive:=positive) (ordinary:=ordinary) (reset:=reset) (room:=room) (shorten:=shorten)
    (funding:=funding) (opened:=opened) (low:=low) (dyadic:=dyadic) (smaller:=smaller) (fit:=fit)
    (base:=base) (width:=width) (age:=age) (words:=words) (dates:=dates) (x₀:=x₀) (z₀:=z₀)
    (c₀:=c₀) (accepted:=accepted)

include age funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3400000 in
set_option cleanup.letToHave false in
/-- Identify the original labels on the registers returned by the last selected reset instruction. -/
theorem purchased_printed_from_terminal (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
    (obtained:terminalArchive X G S ordinary reset branch positive room shorten w c₀ (cursor_ (S).length)
      (lastAt x₀ z₀)) :
    ∃sp:lastSpace,(cursor_ (S).length).ports=lastPorts sp ∧
      FinalPrintedArchive X G S ordinary reset branch positive room shorten w c₀ (lastPorts sp) (lastAt x₀ z₀) :=
  final_printed_register X G S ordinary reset branch positive room shorten w menu_ entry_ rfl rfl rfl
    (heads_).geometry (fun i e => purchased_calendar_placed X G rounds restart τ β siteCount payloadBits
      opened smaller low dyadic ordinary reset branch positive room shorten ratio₀ fit
      headRate_ datesRate_ codeRate_ lastRate_ slots_ funding i e)
    c₀ (startedAt x₀ z₀) age obtained

include age funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- Recover the exact encoded primitive and its archived arity at the unique scheduled reset register. -/
theorem purchased_final_printed_archive (words:HostWordRoom G S k tail p j ratio₀ payloadBits)
    (dates:StageDateResources G rot rounds f g restart R dateDegree n h τ β payloadBits siteCount w)
    (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
    (accepted:candidatePrior x₀ (erased z₀)=some c₀) :
    ∃sp:lastSpace,(cursor_ (S).length).ports=lastPorts sp ∧
      FinalPrintedArchive X G S ordinary reset branch positive room shorten w c₀ (lastPorts sp) (lastAt x₀ z₀) :=by
  apply purchased_printed_from_terminal (X:=X) (G:=G) (branch:=branch) (positive:=positive) (ordinary:=ordinary) (reset:=reset)
    (room:=room) (shorten:=shorten) (funding:=funding) (opened:=opened) (low:=low) (dyadic:=dyadic)
    (smaller:=smaller) (fit:=fit) (base:=base) (width:=width) (age:=age) (x₀:=x₀) (z₀:=z₀) (c₀:=c₀)
  exact purchased_terminal_archive (X:=X) (G:=G) (branch:=branch) (positive:=positive) (ordinary:=ordinary) (reset:=reset) (room:=room) (shorten:=shorten)
    (funding:=funding) (opened:=opened) (low:=low) (dyadic:=dyadic) (smaller:=smaller) (fit:=fit)
    (base:=base) (width:=width) (age:=age) (words:=words) (dates:=dates) (x₀:=x₀) (z₀:=z₀)
    (c₀:=c₀) (accepted:=accepted)

local notation "roleBase" => max ((cursor_ (S).length).floor) (matrixAt+32*DescentExteriorShelf.span j rest s E₀)
local notation "replayBase" => roleBase+DescentTerminalRoleTables.count (originalRoleBits G rot S p R)
local notation "capture" => DescentWideSeedFlags.endInput X (S).copies s payloadBits+
  DescentPackedSeed.rows X (S).copies s payloadBits+1
local notation "captureDates" => countDates 0 (kindCalendar (S).rounds (S).height)
private def archiveSelectorRow (schedule : AtomSchedule) {vertices degree : ℕ}
    (book : RegisterTimeline.Menu vertices degree) (depth : ℕ) (positions : ℕ → RegisterTimeline.Position)
    (dates : List ℕ) (index : ℕ) : ℕ :=
  let date := dates[index]?.getD 0
  book.selectorAt G schedule depth date (positions date)

private def mountedArchiveMemory {bits low high : ℕ} (mounted : RoleMount bits low high)
    (first count : ℕ) (source : ℕ → ℕ) (heap : Memory bits) : Memory bits :=
  mounted.phase.image (DescentLowCountBook.output first source heap count)

private def mountedArchiveResult (schedule : AtomSchedule) {vertices degree : ℕ}
    (book : RegisterTimeline.Menu vertices degree) (depth bits : ℕ)
    (previous final : RegisterTimeline.Position) (want : DatePorts → Memory bits → Prop)
    {mountBase mountEnd : ℕ} (mount : RoleMount bits mountBase mountEnd) (first count : ℕ) (source : ℕ → ℕ)
    (heap : Memory bits) : Prop :=
  ∃ sp : archiveResetSpace G schedule book depth bits previous,
    final.ports = archiveResetPorts G schedule book depth bits previous sp ∧
      want (archiveResetPorts G schedule book depth bits previous sp)
        (mountedArchiveMemory mount first count source heap)

attribute [local irreducible] RegisterTimeline.position RegisterTimeline.issued
  RegisterTimeline.Menu.selectorAt traceAt archiveSelectorRow mountedArchiveMemory
local notation "rowAddress" => archiveSelectorRow G S (vertices:=n) (degree:=h) menu_ k
  (show ℕ → RegisterTimeline.Position from cursor_) captureDates

include age funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- The captured and mounted final memory reads the actual printed palette at each reached node. -/
private theorem purchasedRoleFromTerminal
    (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
    (state : terminalArchive X G S ordinary reset branch positive room shorten w c₀ (cursor_ (S).length)
      (lastAt x₀ z₀)) (mount : RoleMount w roleBase replayBase) :
    mountedArchiveResult G S (vertices:=n) (degree:=h) menu_ k w lastPrior (cursor_ (S).length)
      (FinalPrintedArchive X G S ordinary reset branch positive room shorten w c₀)
      (mountBase:=roleBase) (mountEnd:=replayBase) mount capture (captureDates).length rowAddress (lastAt x₀ z₀) :=by
  unfold mountedArchiveResult mountedArchiveMemory
  exact final_printed_archive_after_mount X G S ordinary reset branch positive room shorten w menu_ entry_ rfl rfl rfl
    (heads_).geometry (fun i e => purchased_calendar_placed X G rounds restart τ β siteCount payloadBits
      opened smaller low dyadic ordinary reset branch positive room shorten ratio₀ fit
      headRate_ datesRate_ codeRate_ lastRate_ slots_ funding i e)
    c₀ (startedAt x₀ z₀) age state capture (captureDates).length rowAddress mount (heads_).paid
    (Nat.le_max_left ..)

include age funding low dyadic opened smaller in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- The captured and mounted final memory reads the actual printed palette at each reached node. -/
theorem purchased_final_role_archive (words:HostWordRoom G S k tail p j ratio₀ payloadBits)
    (dates:StageDateResources G rot rounds f g restart R dateDegree n h τ β payloadBits siteCount w)
    (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
    (accepted:candidatePrior x₀ (erased z₀)=some c₀) (mount:RoleMount w roleBase replayBase) :
    mountedArchiveResult G S (vertices:=n) (degree:=h) menu_ k w lastPrior (cursor_ (S).length)
      (FinalPrintedArchive X G S ordinary reset branch positive room shorten w c₀)
      (mountBase:=roleBase) (mountEnd:=replayBase) mount capture (captureDates).length rowAddress (lastAt x₀ z₀) :=by
  have state:=purchased_terminal_archive (X:=X) (G:=G) (branch:=branch) (positive:=positive) (ordinary:=ordinary) (reset:=reset) (room:=room) (shorten:=shorten)
    (funding:=funding) (opened:=opened) (low:=low) (dyadic:=dyadic) (smaller:=smaller) (fit:=fit)
    (base:=base) (width:=width) (age:=age) (words:=words) (dates:=dates) (x₀:=x₀) (z₀:=z₀)
    (c₀:=c₀) (accepted:=accepted)
  exact purchasedRoleFromTerminal X G rounds restart τ β siteCount payloadBits opened smaller low dyadic
    ordinary reset branch positive room shorten base width age ratio₀ fit headRate_ datesRate_ codeRate_
    lastRate_ slots_ funding x₀ z₀ c₀ state mount

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
