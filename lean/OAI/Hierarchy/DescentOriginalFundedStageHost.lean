import OAI.Hierarchy.DescentNormalizedLastLookup
import OAI.Hierarchy.DescentOriginalHostPurchase
import OAI.Hierarchy.DescentFixedHostPlacement
import OAI.Hierarchy.DescentFundedRegisteredInstructions
import OAI.Hierarchy.DescentNamedSeedCompleteInvoice
import OAI.Hierarchy.DescentNormalizedCalendarPurchase
import OAI.Hierarchy.DescentOriginalStageFeeAxes
import OAI.Hierarchy.DescentNamedWideFoldTariff
import OAI.Hierarchy.DescentEarnedBootAndDates
import OAI.Hierarchy.DescentNamedWideEarnedStageHost
import OAI.Hierarchy.DescentOriginalMountedRegistered
import OAI.Hierarchy.DescentOriginalRoleMount
import OAI.Hierarchy.DescentFromSplitStageHosts
import OAI.Hierarchy.DescentOriginalRoleTableRoom
import OAI.Hierarchy.DescentOriginalMachineRatio
import OAI.Hierarchy.DescentFromDyadicStageHosts

import OAI.Hierarchy.DescentOriginalFundedDenseHeader
import OAI.Hierarchy.DescentNamedSelectorCapture

namespace OAI
/-! # The original finite host on the fixed public epoch calibration -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentKernelHistory CorrectionBatch Computability.BorderVNP.Crossing
open DescentExterior DescentExteriorShelf DescentTerminalChipRuntime DescentTerminalChipPins
open ThreeFlat Routing Diagonal Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentExteriorReplay
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 16000
set_option maxHeartbeats 3500000
set_option cleanup.letToHave false
attribute [local irreducible] SeedNamed.issued normalizedPackedChart Path.snapshotRanks
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F)
variable {cut n h C f g : ℕ} (rounds restart τ β siteCount payloadBits : ℕ)
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
variable (ordinary : OrdinaryRates G (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β)))) (groupBits rounds (Nat.log 2 payloadBits/(2*β)) (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g)) cut) (reset : ResetRates G (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β)))) (groupBits rounds (Nat.log 2 payloadBits/(2*β)) (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g)) (atRound ((stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))).rounds) n h C f g cut (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))
variable (branch : G.b ≤ 2^((stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))).capGain) (positive : 0<((NativeBranch.binLimit («k»:=(groupBits rounds (Nat.log 2 payloadBits/(2*β)) (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g))) (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β)))))*(payloadBits/(16*((2^(Nat.clog 2 (NativeBranch.localLimit G (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))))*(G.b^(rounds*(Nat.log 2 payloadBits/(2*β)))*G.b))*(NativeBranch.binLimit («k»:=(groupBits rounds (Nat.log 2 payloadBits/(2*β)) (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g))) (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β)))))))))) (room : 10*(X.size+1) ≤ ((stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))).initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^((stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))).rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
local notation "s" => (S).firstWidth G.b p
local notation "Z" => (S).grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
variable (base : ((stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))).baseGroups=2^(DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β)))) (width : ((stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))).groupWidth (groupBits rounds (Nat.log 2 payloadBits/(2*β)) (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g)) (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))) 0+(groupBits rounds (Nat.log 2 payloadBits/(2*β)) (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g))=(Nat.clog 2 (NativeBranch.localLimit G (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))))+((Nat.clog 2 (NativeBranch.localLimit G (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))))+(((stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))).groupWidth (groupBits rounds (Nat.log 2 payloadBits/(2*β)) (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g)) (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))) 0+(groupBits rounds (Nat.log 2 payloadBits/(2*β)) (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g))-2*(Nat.clog 2 (NativeBranch.localLimit G (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β)))))))))
variable {w : ℕ} (fit:(((stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))).firstWidth G.b ((NativeBranch.binLimit («k»:=(groupBits rounds (Nat.log 2 payloadBits/(2*β)) (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g))) (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β)))))*(payloadBits/(16*((2^(Nat.clog 2 (NativeBranch.localLimit G (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))))*(G.b^(rounds*(Nat.log 2 payloadBits/(2*β)))*G.b))*(NativeBranch.binLimit («k»:=(groupBits rounds (Nat.log 2 payloadBits/(2*β)) (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g))) (stageNumbers G rounds (Nat.log 2 payloadBits/(2*β)) f g restart siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))))))))<2^w)

local notation "chart" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local instance originalFundedChosenRankChartFinite : Fintype (chart).Pin := (chart).finite
local notation "E₀" => Fintype.card (Port P X.width)
variable {K rawWords : Nat}
local notation "Full" => DescentTerminalFullPins.Candidate ((chart).Pin⊕Hidden E₀ j rest s) K W q piece rawWords

local notation "power" => NativeBranch.copy_power S (radix:=ordinary.radix) base width
local notation "extPins" => Port (((S).copies*s)*P) (CorrectionFrame.copiesWidth ((S).copies*s) X.width)
local notation "view" x₀:arg => Branch.copyInput X s power x₀
local notation "histAt" z₀:arg => (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
local notation "candidatePrior" => wideChoicePrior X G S ordinary reset branch positive room shorten w fit base width
local notation "layout_" => fun c=>Branch.publicLayout X G S (issued X G S ordinary reset branch positive room shorten c)
  positive base width
local notation "oldVotes" z₀:arg => Sum.elim (histAt z₀) (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr)

private theorem original_chosen_rank_rooms
    (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
    (accepted:candidatePrior x₀ (erased z₀)=some c₀)
    (snapshotTable : Snapshots k) (rankFloor replayBase : Nat) (lastMem : Memory w)
    (priorFloor:rankFloor≤replayBase)
    (fundedRead : ∀c,(chart).read ((oldVotes z₀) ∘ Sum.inl) = some c →
      (issued X G S ordinary reset branch positive room shorten c).path.snapshotRanks snapshotTable rankFloor lastMem) :
    (chart).read (histAt z₀)=some c₀ ∧
    ∀i<(S).length,∀B₀:Bank,snapshotTable.compact i=some B₀ → B₀.Fits w replayBase := by
  have selected : (chart).read (histAt z₀)=some c₀ :=
    ((DescentExteriorShelf.proposed_eq (chart).read layout_ (DescentExterior.publicRows X (view x₀))
      (z₀ ∘ DescentTerminalFullPins.history) c₀).mp accepted).1
  have readRanks := fundedRead c₀ selected
  refine ⟨selected, ?_⟩
  intro i hi B₀ stored
  have old :=
    (issued X G S ordinary reset branch positive room shorten c₀).path.snapshot_rank_rooms
      snapshotTable rankFloor lastMem readRanks i hi B₀ stored
  exact ⟨old.1,old.2.1,old.2.2.trans priorFloor⟩

end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler TerminalScale Catalyst DescentInitialHost DescentTerminalPreflightSpace
open DescentTerminalCompiledPrefix DescentTerminalCompiledPrefix.AddressPlan DescentTerminalLocalPortBook ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
open DescentTerminalEmitter.Compact DescentTerminalVertexFields
open DescentStaticWordColumn ThreeFlat.RAM PhysicalProcedure
set_option hygiene false
set_option maxHeartbeats 1000000

variable {F : Type} [Field F] (G : PoweredGadget F) (t f g restart τ β n d C : ℕ)
    (op : RotorSpec) (drift : ℕ) {height : ℕ} (x : ShellSource F height)
local notation "J" => Nat.log 2 height/(2*β)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g restart x.sites tb
local notation "k" => groupBits t J (S).hostGain (S).capGain (cutRate t f g)
local notation "W" => NativeBranch.binLimit («k»:=k) S
local notation "j" => Nat.clog 2 (NativeBranch.localLimit G S)
local notation "q" => 2^j*(G.b^(t*J)*G.b)
local notation "piece" => height/(16*(q*W))
local notation "p" => W*piece
local notation "s" => (S).firstWidth G.b p
local notation "rest" => (S).groupWidth k tb 0+k-2*j
local notation "E" => Fintype.card (Port x.ports x.X.width)
local notation "H" => (S).hostSize (S).length
local notation "V" => earnedFormat G op S q p drift
local notation "slots" => (S).groupCount (S).length*2^k
local notation "A" => NativeBranch.localLimit G S
local notation "raw" => terminalRawRows x.X G S p q n d C f g
local notation "hdr" => terminalPool x.X G S p q W n d C f g
local notation "K" => calibratedBins x.X G t J f g restart x.sites τ height n d C
local notation "fmt" => Branch.geometryFormat G S k g p tb q drift op hdr hdr
local notation "prepared" => Branch.preflightSpec x.X G S k g p tb ({fmt with binSize:=W}:Branch.PreflightFormat)
local notation "codes" => DescentTerminalScalarHeader.range q (V).roles (V).privateWords (V).nodes (V).addresses p slots
local notation "T" => RouteSources.Tables.mk 4 slots (slots*A) A (Book.tokenBits (slots*A)) W q K

variable (front scan : ℕ) (peer homes : Bank) (wings : Fin (prepared).scalar.blocks → Fin (2*(prepared).cap) → Bank)
local notation "pages" => (prepared).scanPages scan q
local notation "rom" => front+DescentTerminalChipBootWords.total K W q piece codes
local notation "positive" => (show 0<x.sites from by have h:=x.opened;omega)


local notation "placement_" => originalPlacement G t f g restart τ β n d C op drift x front scan peer homes wings
local notation "shell_" => earnedShell G t f g restart τ β n d C x placement_
local notation "input_" => earnedInput G t f g restart τ β n d C op drift x placement_
local notation "fund_" => ((S).copies*s)*(x.sites+2^J*E)
local notation "rate_" => originalFrontierRate n d C t f g

set_option hygiene true
/-- Both original chip budgets at the concrete public shell and its input pages. -/
private theorem funded_chip_prices_at_placement (ratio limit : ℕ)
    (purchased : OriginalPurchaseAt G op t f g restart n d C drift limit ratio τ β height)
    (cfg : Shape) (native : AddressPlan.Input)
    (shape : cfg = shell_) (inputEq : native = input_)
    (channels : MaskAllocation.Channels (S).radix) (start head w vertices bits : ℕ)
    (short : vertices*span (V).publicArity (V).roles (V).privateWords (V).nodes (V).addresses (V).piece≤bits)
    (literal : Literals native.sources) (banks : DescentTerminalChipRuntime.Banks)
    (ambient : 2^height≤x.sites) (copies : 0<(S).copies) (live : 0<height) (bus : w=ratio*height) :
    let factor := originalChipFactor G t f g restart ratio τ
    let inputWords := DescentTerminalPublicIdentity.total K W q piece codes
      cfg.terminal.plane.rawRows cfg.terminal.plane.publicRows
    let boot := AddressPlan.clock V cfg native channels start head short literal (bw:=w)
    let controller := AddressPlan.chip cfg native (afterMeter V cfg channels start)
    let finalCost := AddressPlan.time V cfg native channels start head +
      DescentTerminalChipRuntime.clocks (K*W) cfg.terminal.pool +
      7*(names boot+names (DescentTerminalChipRuntime.program controller banks w (K*W) cfg.terminal.pool))
    inputWords*w*2^J≤originalAppendixPrice factor rate_*fund_ ∧
      finalCost*(w+1)*2^J≤originalChipPrice factor rate_*fund_ := by
  subst cfg
  subst native
  have support : 2^height≤2*(x.sites*(S).copies) :=
    (ambient.trans (Nat.le_mul_of_pos_right _ copies)).trans (Nat.le_mul_of_pos_left _ (by decide))
  have arch : w+1 ≤ originalChipFactor G t f g restart ratio τ*height := by
    calc
      w+1 ≤ ratio*height+height := by omega
      _ = (ratio+1)*height := by simp only [Nat.add_mul,Nat.one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_max_left ..)
  have appendix := purchased.appendix x placement_ w support arch
  constructor
  · exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ w))).trans appendix
  · exact purchased.chip x placement_ channels start head w vertices bits short literal banks support arch

end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentExteriorMatrixUpdate DescentExteriorShelf DescentStaticWordColumn Chronology
open DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory DescentGL DescentColonies DescentExterior PinCohorts
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (S : AtomSchedule)
    (roof : ℕ) (tag : ℕ→Bool) (rotation loc : ℕ→ℕ) (lo compact k tail j r s w : ℕ)
    (mount : NativePhase w) (term : Procedure w) (termClocks : ℕ)
    (plan : Reel) (dim wall : ℕ)
local notation "E" => Fintype.card (Port P X.width)
local notation "dates" => countDates 0 (kindCalendar S.rounds S.height)
local notation "countTicks" => 4+11*(dates).length
local notation "earlyTicks" => Calendar.earlyClock S k tail j r s E
local notation "post" => Calendar.postProgram plan dim S.length j r s E w compact wall
local notation "old" => historyCountReel X S roof tag rotation loc lo compact k tail j r s w
local notation "newReel" => historyMountedReel X S roof tag rotation loc lo compact k tail j r s w mount
local notation "oldProgram" => ((old).seq term).seq post
local notation "newProgram" => (((newReel).seq term).seq (relocate j r s E w compact wall)).seq
  (plan.program j r s E w dim S.length wall)
local notation "oldCharge" => countTicks+earlyTicks+termClocks+Calendar.postClock S.length j r s E+7*names oldProgram
local notation "newCharge" => ((countTicks+mount.ticks)+earlyTicks)+termClocks+
  (4+18*(17*span j r s E))+(10+((4+58*S.length)+(4+16*E)))+7*names newProgram


omit [Field F] in
private theorem reel_from_purchased_charges (height order factor rate fund sites : ℕ)
    (narrow : height+1 ≤ w) (home : sites ≤ fund)
    (oldPrice : oldCharge*(w+1)*2^order ≤
      (524288*(factor+1)+7*16384*(2*factor)+(128000+262144)*factor+
       7*24200200*(2*factor+6*(6*(32*factor)*(3+4*rate)+2*factor)))*fund)
    (installed : (mount.ticks+7*names mount.program)*(height+1)*2^order ≤ sites) :
    newCharge*(height+1)*2^order ≤ originalPostPrice factor rate*fund := by
  let quota := 524288*(factor+1)+7*16384*(2*factor)+(128000+262144)*factor+
    7*24200200*(2*factor+6*(6*(32*factor)*(3+4*rate)+2*factor))
  have previous : oldCharge*(height+1)*2^order ≤ quota*fund :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (narrow.trans (Nat.le_succ w)))).trans oldPrice
  have total := mounted_counted_post_price X S roof tag rotation loc lo compact k tail j r s w
    mount term termClocks plan dim wall (height+1) (2^order) (quota*fund) sites previous installed
  change _ ≤ (quota+1)*fund
  rw [Nat.add_mul quota 1 fund, Nat.one_mul]
  exact total.trans (Nat.add_le_add_left home _)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentTerminalFixedSlices

private theorem purchased_reel_slice {F : Type} [Field F] (G : PoweredGadget F)
    (t J f g restart sites τ drift height : ℕ) (P : Phase F)
    (fieldInfo : FinalSliceFields G (stageNumbers G t J f g restart sites (tail τ J))
      (groupBits t J (hostRate t restart) (capRate G t g) (cutRate t f g)) drift height P)
    (packed : drift + 1 ≤ scale J 1) :
    P.Paid height (scale J (1 + operandExponent G (stageNumbers G t 0 f g restart 0 0)
      + groupRate G t f g restart + 4)) := by
  refine ⟨fieldInfo.receiver, fieldInfo.lookup, ?_⟩
  exact (congrArg₂ (fun (slots blocks : ℕ) => ((2+3*slots)+1)*(blocks+1))
    fieldInfo.arguments fieldInfo.blocks).trans_le
    (slice_pass_multiplier G t J f g restart sites τ drift packed)

end Hierarchy.DescentSixParty.SeedNamed

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
set_option cleanup.letToHave false
set_option maxRecDepth 16000
set_option maxHeartbeats 3500000
attribute [local irreducible] SeedNamed.issued normalizedPackedChart

private theorem originalFinalWordCharge {payload word bill time rate fund : ℕ}
    (narrow : payload+1 ≤ word) (finish : bill*(word+1)*time ≤ rate*fund) :
    bill*(payload+1)*time ≤ rate*fund :=
  (Nat.mul_le_mul_right time (Nat.mul_le_mul_left bill (narrow.trans (Nat.le_succ word)))).trans finish

private theorem registeredDateSumFits {sum site copies p width depth ext : Nat}
    (paid : sum*2^depth ≤ 2*(site*(copies*p))) (grain : p≤width) :
    sum*2^depth ≤ 2*((copies*width)*(site+2^depth*ext)) := by
  apply Nat.le_trans paid
  apply Nat.mul_le_mul_left
  calc
    site*(copies*p) ≤ site*(copies*width) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ grain)
    _ = (copies*width)*site := Nat.mul_comm ..
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_right ..)

private theorem regroupBootInvoice {cost a b : ℕ} (paid : cost ≤ (4*a)*b) : cost ≤ 4*(a*b) :=
  paid.trans_eq (Nat.mul_assoc ..)

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F)
variable {cut n h C f g : ℕ} (rounds restart τ β siteCount payloadBits : ℕ)
local notation "depth_" => Nat.log 2 payloadBits/(2*β)
local notation "tail" => DescentCompiler.TerminalScale.tail τ depth_
private abbrev fundedInvoiceSchedule : AtomSchedule := stageNumbers G rounds depth_ f g restart siteCount tail
local notation "S" => (@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)
private abbrev fundedInvoiceGroupBits : ℕ := groupBits rounds depth_ (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g)
local notation "k" => (@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)
local notation "W" => NativeBranch.binLimit («k»:=k) S
private abbrev fundedInvoiceHead : ℕ := Nat.clog 2 (NativeBranch.localLimit G S)
local notation "j" => (@fundedInvoiceHead F _ G f g rounds restart τ β siteCount payloadBits)
private abbrev fundedInvoiceSlots : ℕ := 2^j*(G.b^(rounds*depth_)*G.b)
local notation "q" => (@fundedInvoiceSlots F _ G f g rounds restart τ β siteCount payloadBits)
local notation "piece" => payloadBits/(16*(q*W))
local notation "rest" => (S).groupWidth k tail 0+k-2*j
private abbrev fundedInvoiceCellWidth : ℕ := W*piece
local notation "p" => (@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits)
variable (ordinary : OrdinaryRates G ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) cut) (reset : ResetRates G ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) (atRound (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).rounds) n h C f g cut (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))))
variable (branch : G.b ≤ 2^(((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).capGain) (positive : 0<((@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits))) (room : 10*(X.size+1) ≤ (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^(((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
private abbrev fundedInvoiceFirstWidth : ℕ := (S).firstWidth G.b p
local notation "s" => (@fundedInvoiceFirstWidth F _ G f g rounds restart τ β siteCount payloadBits)
local notation "Z" => (S).grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
private abbrev fundedInvoiceDrift : ℕ := max 1 (max reset.bitsR (C*reset.bitsR))
local notation "R" => (@fundedInvoiceDrift F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset)
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => (S).epochPower^(S).localTokenExponent
local notation "venues" => (S).groupCount (S).length*2^k

variable (base : (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).baseGroups=2^(DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β)))) (width : (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupWidth ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))) 0+((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))=((@fundedInvoiceHead F _ G f g rounds restart τ β siteCount payloadBits))+(((@fundedInvoiceHead F _ G f g rounds restart τ β siteCount payloadBits))+((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupWidth ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))) 0+((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))-2*((@fundedInvoiceHead F _ G f g rounds restart τ β siteCount payloadBits)))))
variable (age : 0<(((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).height) (wFit : NativeBranch.binLimit («k»:=((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))) ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) ≤ (NativeBranch.binLimit («k»:=((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))) ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))))
  (qFit : NativeBranch.localLimit G ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) ≤ ((@fundedInvoiceSlots F _ G f g rounds restart τ β siteCount payloadBits))) (qh : 0<((@fundedInvoiceSlots F _ G f g rounds restart τ β siteCount payloadBits)))

open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalExteriorPackets DescentTerminalPublicIdentity
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall DescentPackedProfileTape
open DescentSeedRoot DescentExteriorShelf DescentTerminalPrimitiveArena
local notation "E₀" => Fintype.card (Port P X.width)
local notation "H₀" => (S).hostSize (S).length
local notation "count₀" => E₀*2^(j+rest)
variable (template:DescentTerminalCompiledPrefix.Shape) (sitesPositive:0<((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).hostSize (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).length))
local notation "rawWords" => terminalRawRows X G S p q n h C f g
local notation "headerRows" => terminalPool X G S p q W n h C f g
local notation "paidRows" => headerRows
private abbrev fundedInvoiceTerminalShape : DescentTerminalCompiledPrefix.Shape := Branch.exteriorShape template E₀ j rest s rawWords headerRows H₀ sitesPositive
local notation "cfg" => (@fundedInvoiceTerminalShape F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits template sitesPositive)
variable (pool : terminalPool X G ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) ((@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits)) ((@fundedInvoiceSlots F _ G f g rounds restart τ β siteCount payloadBits)) (NativeBranch.binLimit («k»:=((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))) ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))) n h C f g ≤ (((@fundedInvoiceTerminalShape F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits template sitesPositive))).terminal.pool)
    (raw : terminalRawRows X G ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) ((@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits)) ((@fundedInvoiceSlots F _ G f g rounds restart τ β siteCount payloadBits)) n h C f g ≤ (((@fundedInvoiceTerminalShape F _ cp P X G n h C f g rounds restart τ β siteCount payloadBits template sitesPositive))).terminal.plane.rawRows)
local notation "groupsAt" => (S).groupCount (S).length
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact
open DescentTerminalLocalPortBook DescentTerminalSpanBook DescentTerminalBinPack
open DescentTerminalPreflightSpace ThreeFlat.RAM PhysicalProcedure

open DescentPackedEpochFold DescentExteriorMatrixUpdate DescentPackedSeed DescentSeedRoot
open ThreeFlat Routing Diagonal
variable {w : ℕ} (fit:((@fundedInvoiceFirstWidth F _ G f g rounds restart τ β siteCount payloadBits))<2^w)
local notation "K" => calibratedBins X G rounds depth_ f g restart siteCount τ payloadBits n h C
private abbrev fundedInvoiceChoiceChart := normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "chart" => (@fundedInvoiceChoiceChart F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit)
local instance originalFundedStageOuterChartFinite : Fintype (chart).Pin := (chart).finite
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
private abbrev fundedInvoicePreflight : DescentTerminalPreflightSpace.Spec := Branch.preflightSpec X G S k g p tail ({fmt with binSize:=W}:Branch.PreflightFormat)
local notation "pre" => (@fundedInvoicePreflight F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits reset)
local notation "steps" => (chart).layout
local notation "lo" => DescentWideSeedFlags.selectorBase X (S).copies s payloadBits (steps).length
local notation "packWidth" => DescentPackedEpochShelves.grain (payloadBits/2) G.C
local notation "matrixAt" => end_ (lo+extent packWidth steps) G.C packWidth
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentResetInvoice CorrectionBatch
open DescentSixParty.SeedNamed.Branch DescentExteriorReplay DescentTerminalFixedSlices
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup DescentPackedColony
open ThreeFlat.Routing CallPool DescentColonies DescentActorRaster DescentColonies.SplitRAM
open DescentTerminalRoleTables DescentTerminalPointerIssue
open Chronology Chronology.RegisterTimeline DescentDatedSeedStartup.Input DescentTerminalEpochDecoder
variable {bootHosts : ℕ} (hostsEnough:Fintype.card (Vertex X)≤bootHosts) (startup:DescentDatedSeedStartup.Layout)
  (startingHeader dateDegree : ℕ)
local notation "primitiveLanes_" => DescentDatedSeedStartup.Primitive.paletteLanes G rot startup.seedWidth Z payloadBits k
local notation "initialSource_" => DescentPackedSeed.Primitive.Source.jobs X (S).copies startup.seedWidth payloadBits
local notation "seedEnd_" => (DescentDatedSeedStartup.Input.nodeChart startup k bootHosts ((S).groupCount 0)).seedEnd
  (DescentDatedSeedStartup.endAddress X startup bootHosts ((S).groupCount 0) k)
local notation "initialBound_" => DescentDatedSeedStartup.Primitive.initialEnd X (S).copies startup.seedWidth payloadBits k
  bootHosts ((S).groupCount 0) primitiveLanes_ seedEnd_

local notation "entry_" => (⟨DatePorts.initial G rot X (S).copies startup k bootHosts ((S).groupCount 0) payloadBits Z,
    initialBound_⟩ : RegisterTimeline.Position)
local notation "board" => reset.board
local notation "traces_" => traceAt X G S ordinary reset branch positive room shorten
local notation "menu_" => RegisterTimeline.fromProfiles G S board rot k tail p f g R dateDegree payloadBits lo startingHeader steps
local notation "cursor_" => RegisterTimeline.calendar (w:=w) traces_ menu_ entry_
local notation "datesAt" => RunTrace.machine traces_ (fun i _=>RegisterTimeline.instruction (w:=w) traces_ menu_ entry_ i)
local notation "dateAge" => (S).length-1
private abbrev fundedInvoicePrior : RegisterTimeline.Position := cursor_ dateAge
local notation "prior_" => (@fundedInvoicePrior F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit bootHosts startup startingHeader dateDegree)
local notation "ordinaryAt" => (menu_).ordinary
local notation "datePayload" => payloadBits
local notation "operandLanes" => (prior_).ports.operandLanes
local notation "primitiveLanes" => (prior_).ports.roleLanes
local notation "previousDate" => (prior_).ports.venue
local notation "priorAddress" => (prior_).ports.io.wire
local notation "rosterBank" => (prior_).ports.io.roster
local notation "datedFloor" => (prior_).ports.priorStart k (prior_).floor
local notation "dateTag" => RegisterTimeline.Menu.resetFlag S
local notation "dateRotation" => fun i=>(menu_).rotationAt G S k i (cursor_ i)
local notation "countAt" => fun i=>(menu_).selectorAt G S k i (cursor_ i)
local notation "rankDir_" => RegisterTimeline.snapshotDirectory (w:=w) traces_ menu_ entry_
local notation "snapshots" => SnapshotCalendar reset (kindCalendar (S).rounds (S).height)
  (capCalendar G.b (S).rounds g (S).height) rankDir_
local notation "rankFloor" => (cursor_ (S).length).floor
local notation "roleBase" => max rankFloor (matrixAt+32*DescentExteriorShelf.span j rest s E₀)
local notation "replayBase" => roleBase+DescentTerminalRoleTables.count (originalRoleBits G rot S p R)

private abbrev fundedInvoiceDateSpec : DescentTerminalPreflightSpace.Spec := preflightSpec X G S k g p tail (geometryFormat G S k g p tail q R rot headerRows paidRows)
local notation "dateSpec" => (@fundedInvoiceDateSpec F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits reset)
local notation "datePorts" => Fintype.card (Port P X.width)
private abbrev fundedInvoiceDatePhase : DescentTerminalFixedSlices.Phase F := Phase.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "datePhase" => (@fundedInvoiceDatePhase F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit bootHosts startup startingHeader dateDegree)
local notation "dateOut" => (datePhase).output
local notation "dateOrigin" => (datePhase).dateBase
local notation "dateMachine" => PhysicalReset.scheduled G S board k tail dateAge p f g R dateDegree datePayload ordinaryAt rot
  s Z operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateCalendar" => replayCalendar X S k tail j rest snapshots
local notation "earlyFloor" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail replayBase j rest s datePorts
local notation "earlyImage" => DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail replayBase dateTag dateRotation j rest s datePorts matrixAt
private abbrev fundedInvoiceSliceEnd : ℕ := (datePhase).stop earlyFloor
local notation "sliceEnd" => (@fundedInvoiceSliceEnd F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit bootHosts startup startingHeader dateDegree)
local notation "lookupBase" => (dateCalendar).packetEnd sliceEnd
private abbrev fundedInvoiceLookupPage : DescentTerminalControlROMs.Page := (dateSpec).scanPages lookupBase q
local notation "lookupPage" => (@fundedInvoiceLookupPage F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit bootHosts startup startingHeader dateDegree)
private abbrev fundedInvoiceCensusBase : ℕ := (lookupPage).stop
local notation "censusBase" => (@fundedInvoiceCensusBase F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit bootHosts startup startingHeader dateDegree)
local notation "dateHardware" => (dateOut).receiver
local notation "dateBlocks" => (dateSpec).scalar.blocks
local notation "blockCast" => (rfl : dateBlocks=(dateHardware).blocks)
local notation "paidBank" => fun x:Fin dateBlocks=>(dateOut).terminalPaid dateOrigin x.val
local notation "actorBank" => fun x:Fin dateBlocks=>(dateOut).terminalActor dateOrigin x.val
local notation "wingBank" => fun (x:Fin dateBlocks) (a:Fin (2*(dateSpec).cap))=>(dateOut).terminalWing dateOrigin x.val a.val
local notation "peerBank" => (dateOut).terminalPeer dateOrigin
local notation "dateColors" => DescentPrimitivePalette.colors G s Z rot
local notation "roleBankBits" => fun roleField : Fin 6 =>DescentTerminalCombinedRole.width dateColors (max 8 (2^(S).capGain))
  cap p R roleField*((S).epochPower^(S).localTokenExponent)*(dateSpec).groups
local notation "atomBits" => Nat.clog 2 (nodeCap+1)
local notation "operandWidths" => (⟨atomBits,Nat.clog 2 (cap+1),fun _=>DescentOperandWidth.recordBits G S k tail R 3 p,some nodeCap⟩:Widths)
local notation "terminalPin" => DescentExterior.terminalPin ((S).groupWidth k tail 0+k) ((S).groupWidth k tail (S).length+k) (k*(S).length)
local notation "publicCell" => DescentTerminalPointerDigits.publicCell («cap»:=(dateSpec).cap) (N:=nodeCap) (A:=cap)
  (d:=(dateSpec).scalar.pointerBits) 3 q G.b (poolBatchCount (s*1) p) (k*(S).length) (dateSpec).groups operandWidths
local notation "privateCell" => DescentTerminalPointerDigits.output (dateSpec).cap nodeCap cap 3 (dateSpec).groups
  (dateSpec).scalar.pointerBits (Nat.clog 2 (q+cap+1)) q G.b (poolBatchCount (s*1) p) operandWidths terminalPin
local notation "roleBanks" => DescentTerminalRoleTables.role roleBankBits ((datePhase).banks earlyFloor) roleBase
local notation "arityBanks" => DescentTerminalRoleTables.arity roleBankBits ((datePhase).banks earlyFloor) roleBase
local notation "matrixFloor" => DescentExteriorMatrixUpdate.Calendar.stop S k tail replayBase+(S).length
local notation "pointerBank" => fun (pointerField : Fin 4) (pointerLane : Fin (dateOut).argumentSlots) (pointerBlock : Fin dateBlocks) =>
  (dateOut).terminalPointers dateOrigin pointerField pointerLane (pointerBlock.cast blockCast)
local notation "oldOperands" => DescentTerminalOperandRepack.padded («K»:=cap) pointerBank paidBank
local notation "operandChart" => ((dateSpec).pointerPages censusBase matrixFloor oldOperands wingBank).address (N:=nodeCap)
variable (replayRoom : ((replayCalendar X ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))) ((@fundedInvoiceHead F _ G f g rounds restart τ β siteCount payloadBits)) ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupWidth ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))) 0+((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))-2*((@fundedInvoiceHead F _ G f g rounds restart τ β siteCount payloadBits))) (SnapshotCalendar reset (kindCalendar (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).rounds (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).height)   (capCalendar G.b (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).rounds g (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).height) (RegisterTimeline.snapshotDirectory (w:=w) (traceAt X G ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) ordinary reset branch positive room shorten) (RegisterTimeline.fromProfiles G ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) (reset.board) (RotorSpec.ofRates reset) ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))) ((@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits)) f g ((@fundedInvoiceDrift F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset)) dateDegree payloadBits (DescentWideSeedFlags.selectorBase X (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).copies ((@fundedInvoiceFirstWidth F _ G f g rounds restart τ β siteCount payloadBits)) payloadBits (((((@fundedInvoiceChoiceChart F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit))).layout)).length) startingHeader ((((@fundedInvoiceChoiceChart F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit))).layout)) ((⟨DatePorts.initial G (RotorSpec.ofRates reset) X (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).copies startup ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) bootHosts ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupCount 0) payloadBits ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).grainAt G.b ((@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits)) 0),     (DescentDatedSeedStartup.Primitive.initialEnd X (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).copies startup.seedWidth payloadBits ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))   bootHosts ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupCount 0) (DescentDatedSeedStartup.Primitive.paletteLanes G (RotorSpec.ofRates reset) startup.seedWidth ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).grainAt G.b ((@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits)) 0) payloadBits ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))) ((DescentDatedSeedStartup.Input.nodeChart startup ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) bootHosts ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupCount 0)).seedEnd   (DescentDatedSeedStartup.endAddress X startup bootHosts ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupCount 0) ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)))))⟩ : RegisterTimeline.Position)))))).stop ((@fundedInvoiceCensusBase F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit bootHosts startup startingHeader dateDegree))<2^w)
local notation "dateEntryAt" mu:arg => (dateCalendar).memory sliceEnd censusBase replayRoom ((datePhase).memory earlyFloor (earlyImage mu))
local notation "primitiveOf" mu:arg => (dateSpec).primitiveSnapshot (base:=censusBase) (w:=w) («q»:=q) («p»:=p) (nd:=atomBits)
  (nodes:=nodeCap) (hidden:=cap) (args:=cap) (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks)
  («chart»:=operandChart) (f0:=publicCell) (f7:=privateCell) ((lookupPage).image (dateEntryAt mu))
local notation "datedDecoder" => Branch.decodeBook S G base ordinary.radix p q 3
  (dateSpec).cap (dateSpec).printBits (by decide)
local notation "booksOf" mu:arg => (dateSpec).bookSnapshot (base:=censusBase) («peer»:=peerBank) (wing:=wingBank)
  (w:=w) («q»:=q) («p»:=p) (nd:=atomBits) (nodes:=nodeCap) (hidden:=cap) (args:=cap)
  (oldPaid:=paidBank) (actor:=actorBank) (first:=roleBanks) (second:=arityBanks) («chart»:=operandChart)
  (f0:=publicCell) (f7:=privateCell) (decode:=datedDecoder) ((lookupPage).image (dateEntryAt mu))
local notation "dateHomes" => (dateCalendar).homes sliceEnd

local notation "begin_" => censusBase
local notation "peer" => peerBank
local notation "old" => wingBank
local notation "org" => lookupBase
local notation "homes" => dateHomes
variable (other:AddressPlan.Input)
local notation "arity" => max 8 (2^(S).capGain)
local notation "groups" => cap
local notation "stride" => R
local notation "oldTags" => DescentPrimitivePalette.colors G s Z rot
local notation "codec" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=Z) rot
local notation "tagCount" => DescentBundleTagKeys.capacity oldTags arity groups p stride
private abbrev fundedInvoiceFormat : Home.Format := (⟨q,tagCount,cap,nodeCap,cap,p,groupsAt⟩:Home.Format)
local notation "V" => (@fundedInvoiceFormat F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset)
local notation "pages₀" => (pre).scanPages org q
local notation "total" => (pages₀).total
local notation "modulo" => (pages₀).modulo
local notation "boundary" => (pages₀).boundaries
local notation "routeTables" => (RouteSources.Tables.mk 4 venues (venues*NativeBranch.localLimit G S)
  (NativeBranch.localLimit G S) (Book.tokenBits (venues*NativeBranch.localLimit G S)) W q K)
local notation "B" => (pre).pageBits
local notation "grain" => p
local notation "codes" => DescentTerminalScalarHeader.range q tagCount cap nodeCap cap p venues
local notation "seed" => (chart).seed
local notation "clockCap" => G.C
local notation "front" => end_ (lo+extent packWidth steps) clockCap packWidth+17*DescentExteriorShelf.span j rest s E₀
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rawWords count₀
local notation "Full" => DescentTerminalFullPins.Candidate ((chart).Pin⊕Hidden E₀ j rest s) K W q piece rawWords
local notation "power" => NativeBranch.copy_power S (radix:=ordinary.radix) base width
local notation "rom" => front+DescentTerminalChipBootWords.total K W q piece codes
private abbrev fundedInvoiceReachedInput : AddressPlan.Input := (pre).reachedInput begin_ rom q piece W K codes front peer old total modulo homes
                          boundary cfg V other routeTables (pre).vertices B
local notation "I_" => (@fundedInvoiceReachedInput F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten template sitesPositive w fit bootHosts startup startingHeader dateDegree other)
local notation "R_" => (pre).channels begin_
local notation "start" => (pre).maskBase begin_
local notation "base_" => afterMeter V cfg R_ start
local notation "A_" => rowArena cfg I_ base_
local notation "J_" => (pre).chipInput begin_ rom q grain peer old total modulo homes boundary cfg other

local notation "head" => startingHeader
variable (short : (((@fundedInvoicePreflight F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits reset))).vertices*DescentTerminalVertexFields.span (((@fundedInvoiceFormat F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset))).publicArity (((@fundedInvoiceFormat F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset))).roles (((@fundedInvoiceFormat F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset))).privateWords (((@fundedInvoiceFormat F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset))).nodes (((@fundedInvoiceFormat F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset))).addresses (((@fundedInvoiceFormat F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset))).piece≤((((@fundedInvoicePreflight F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits reset))).pageBits))
local notation "literal" => ScalarLiterals.data q (V).roles (V).privateWords (V).nodes (V).addresses grain (pre).vertices W B
  (cfg).terminal.pool qh ((routeTables).columns A_ (J_).sources) ((routeTables).value (fun _ _=>0))
local notation "O_" => registers V cfg R_ start head
local notation "plan_" => AddressPlan.layout cfg I_ base_ O_

local notation "emptyCode" => (DescentTerminalChronologicalBooks.empty q tagCount cap nodeCap cap p venues p).val
local notation "bankSet" => DescentTerminalChipBootWords.chipBanks («K»:=K) («W»:=W) («q»:=q)
  («p»:=piece) codes (plan_).emit front emptyCode

local notation "wall" => AddressPlan.takeOff (cfg) I_ base_
local notation "compact" => end_ (lo+extent packWidth steps) G.C packWidth
local notation "firstFree" => front+extra
local notation "dst" => DescentPackedEpochShelves.finalAt firstFree lo packWidth steps
local notation "seedBase" => DescentWideSeedFlags.endInput X (S).copies s payloadBits
local notation "seedRows" => DescentPackedSeed.rows X (S).copies s payloadBits
local notation "B₀" => (S).groupWidth k tail 0+k
open Chronology Chronology.RegisterTimeline DescentDatedSeedStartup.Input DescentTerminalEpochDecoder DescentPackedSeed DescentExteriorShelf
local notation "capture" => seedBase+seedRows+1
variable (replayFits : ((max (((RegisterTimeline.calendar (w:=w) (traceAt X G ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) ordinary reset branch positive room shorten) (RegisterTimeline.fromProfiles G ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) (reset.board) (RotorSpec.ofRates reset) ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))) ((@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits)) f g ((@fundedInvoiceDrift F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset)) dateDegree payloadBits (DescentWideSeedFlags.selectorBase X (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).copies ((@fundedInvoiceFirstWidth F _ G f g rounds restart τ β siteCount payloadBits)) payloadBits (((((@fundedInvoiceChoiceChart F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit))).layout)).length) startingHeader ((((@fundedInvoiceChoiceChart F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit))).layout)) ((⟨DatePorts.initial G (RotorSpec.ofRates reset) X (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).copies startup ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) bootHosts ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupCount 0) payloadBits ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).grainAt G.b ((@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits)) 0),     (DescentDatedSeedStartup.Primitive.initialEnd X (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).copies startup.seedWidth payloadBits ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))   bootHosts ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupCount 0) (DescentDatedSeedStartup.Primitive.paletteLanes G (RotorSpec.ofRates reset) startup.seedWidth ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).grainAt G.b ((@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits)) 0) payloadBits ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))) ((DescentDatedSeedStartup.Input.nodeChart startup ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) bootHosts ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupCount 0)).seedEnd   (DescentDatedSeedStartup.endAddress X startup bootHosts ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupCount 0) ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)))))⟩ : RegisterTimeline.Position))) (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).length).floor) ((end_ ((DescentWideSeedFlags.selectorBase X (((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).copies ((@fundedInvoiceFirstWidth F _ G f g rounds restart τ β siteCount payloadBits)) payloadBits (((((@fundedInvoiceChoiceChart F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit))).layout)).length)+extent (DescentPackedEpochShelves.grain (payloadBits/2) G.C) ((((@fundedInvoiceChoiceChart F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit))).layout)) G.C (DescentPackedEpochShelves.grain (payloadBits/2) G.C))+32*DescentExteriorShelf.span ((@fundedInvoiceHead F _ G f g rounds restart τ β siteCount payloadBits)) ((((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))).groupWidth ((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits)) (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payloadBits/(2*β))) 0+((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))-2*((@fundedInvoiceHead F _ G f g rounds restart τ β siteCount payloadBits))) ((@fundedInvoiceFirstWidth F _ G f g rounds restart τ β siteCount payloadBits)) (Fintype.card (Port P X.width))))+DescentTerminalRoleTables.count (originalRoleBits G (RotorSpec.ofRates reset) ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits)) ((@fundedInvoiceCellWidth F _ G f g rounds restart τ β siteCount payloadBits)) ((@fundedInvoiceDrift F _ G cut n h C f g rounds restart τ β siteCount payloadBits reset))))<2^w)
local notation "roleMount" => originalRoleMount G rot S p R roleBase replayBase le_rfl replayFits
local notation "captureDates" => countDates 0 (kindCalendar (S).rounds (S).height)
local notation "rowAddress" => fun i:ℕ=>countAt ((captureDates)[i]?.getD 0)
local notation "oldReel" => DescentExteriorMatrixUpdate.Calendar.reel S k tail replayBase dateTag dateRotation
local notation "matrixEnd" => DescentExteriorMatrixUpdate.Calendar.stop S k tail replayBase
local notation "termCode" => Branch.postEarlyPreflight X G S base ordinary.radix g p q R rot headerRows paidRows
  j rest s replayBase datePhase snapshots blockCast roleBase peerBank paidBank actorBank wingBank replayRoom
local notation "termCost" => Branch.postEarlyPreflightClocks X G S («k»:=k) («tail»:=tail) g p q R rot headerRows paidRows
  j rest s replayBase datePhase snapshots blockCast peerBank paidBank actorBank wingBank replayRoom
local notation "bootCode" => completeAfter G rot X ((S).initialDigits ordinary.radix) hostsEnough startup startingHeader payloadBits Z w
local notation "bootCost" => completeTicks («S»:=S) («k»:=k) G rot X hostsEnough startup payloadBits Z w
local notation "originalMid" => ((DateCode.afterBoot bootCode datesAt (S).length).seq
   (Branch.historyMountedReel X S replayBase dateTag dateRotation countAt capture matrixAt k tail j rest s w (roleMount).phase)).seq termCode
local notation "originalCost" => (DateCode.afterTicks bootCost datesAt (S).length+
    (((4+11*(captureDates).length)+(roleMount).phase.ticks)+DescentExteriorMatrixUpdate.Calendar.earlyClock S k tail j rest s datePorts))+termCost
local notation "upperFence" => (pre).maskBase censusBase
local notation "freshReel" => (oldReel).late upperFence
local notation "countSlot" => fun i:ℕ=>capture+i
local notation "fence" => upperFence
local notation "count" => countSlot
local notation "plan" => freshReel

local notation "middle" => originalMid
local notation "cost" => originalCost
local notation "initialFlag" => seedBase+seedRows
local notation "foldSites" => DescentPackedEpochShelves.controlsAt firstFree lo G.C packWidth steps count (fun _=>initialFlag)
local notation "prefixCode" => DescentWideSeedFlags.check X (S).copies s payloadBits w
local notation "paidCode" => (((((prefixCode).seq ((middle).seq (relocate j rest s E₀ w compact wall))).seq
    ((plan).program j rest s E₀ w B₀ (S).length wall)).seq (fold w initialFlag dst foldSites)).seq
    (AddressPlan.clock V cfg I_ R_ start head short literal (bw:=w)))
local notation "paidTime" => ((4+(seedRows+1)*66+(cost+(4+18*(17*DescentExteriorShelf.span j rest s E₀))))+
    (10+((4+58*(S).length)+(4+16*E₀))))+bill initialFlag dst foldSites+AddressPlan.time V cfg I_ R_ start head
local notation "charge" => fun v=> (normalizedLeaf X G S ordinary reset branch positive room shorten v
  base width age wFit qFit qh cfg pool raw).debt cfg

local notation "extPins" => Port (((S).copies*s)*P) (CorrectionFrame.copiesWidth ((S).copies*s) X.width)
local notation "view" x₀:arg => Branch.copyInput X s power x₀
local notation "bootFor" x₀:arg z₀:arg => Root.appended front extra
    (Root.widePackedImage X (S).copies s payloadBits w seed lo G.C packWidth steps compact
      (DescentExterior.publicRows X (view x₀)) (Sum.elim (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
      (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr)))
    (DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀)

local notation "histAt" z₀:arg => (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
local notation "checkedAt" x₀:arg z₀:arg => DescentWideSeedFlags.countedAt X (S).copies s payloadBits seed
  (histAt z₀) (bootFor x₀ z₀)
local notation "startedAt" x₀:arg z₀:arg => completeImage G rot X ((S).initialDigits ordinary.radix) hostsEnough startup
  startingHeader payloadBits Z (checkedAt x₀ z₀)
local notation "lastAt" x₀:arg z₀:arg => DateCode.history datesAt (startedAt x₀ z₀) (S).length
local notation "capturedAt" x₀:arg z₀:arg => (roleMount).phase.image (DescentLowCountBook.output capture rowAddress (lastAt x₀ z₀) (captureDates).length)
local notation "primitiveBank" => fun (x₀:extPins→Bool)(z₀:Full→Bool)=>primitiveOf (capturedAt x₀ z₀)
local notation "booksBank" => fun (x₀:extPins→Bool)(z₀:Full→Bool)=>booksOf (capturedAt x₀ z₀)
local notation "selectedAt" z₀:arg => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow (histAt z₀)
local notation "honestAt" z₀:arg => issued X G S ordinary reset branch positive room shorten (selectedAt z₀)
local notation "acceptAt" z₀:arg => ∃c,(chart).read (histAt z₀)=some c
local notation "layout_" => fun c=>Branch.publicLayout X G S (issued X G S ordinary reset branch positive room shorten c)
  positive base width
local notation "whichAt" x₀:arg z₀:arg => proposed (chart).read layout_ (DescentExterior.publicRows X (view x₀))
  (z₀ ∘ DescentTerminalFullPins.history)
variable (machine:sliceWidth (NativeBranch.binLimit («k»:=((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))) ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))) ((@fundedInvoiceSlots F _ G f g rounds restart τ β siteCount payloadBits)) (payloadBits/(16*(((@fundedInvoiceSlots F _ G f g rounds restart τ β siteCount payloadBits))*(NativeBranch.binLimit («k»:=((@fundedInvoiceGroupBits F _ G f g rounds restart β payloadBits))) ((@fundedInvoiceSchedule F _ G f g rounds restart τ β siteCount payloadBits))))))≤w)

local notation "cols" => AddressPlan.observationColumns V cfg I_ R_ start head dst

local notation "candidatePrior" => wideChoicePrior X G S ordinary reset branch positive room shorten w fit base width
local notation "seedNet" => wideChoiceCircuit («K»:=K) («W»:=W) («q»:=q) («piece»:=piece) X G S ordinary reset branch positive room shorten w fit («j»:=j) («rest»:=rest) cfg
local notation "numBins" => DescentTerminalChronologicalBooks.Keys q tagCount cap nodeCap cap p venues p
local notation "numSlots" => (cfg).terminal.pool
local notation "cpu" => AddressPlan.chip cfg I_ base_
local notation "tapeDesc" => (cols).tape cpu (K*W)
local notation "widthWord" => q*p

local notation "countWidth_" => w+1
private abbrev fundedInvoiceReadoutEnd : ℕ := AddressPlan.last V cfg I_ R_ start
local notation "readoutEnd_" => (@fundedInvoiceReadoutEnd F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten template sitesPositive w fit bootHosts startup startingHeader dateDegree other)
local notation "cut_" => DescentTerminalLast.trailingCut readoutEnd_ (cfg).terminal.rows
private abbrev fundedInvoiceStop : ℕ := DescentTerminalLast.trailingStop cut_ rawWords numSlots numBins
local notation "stop_" => (@fundedInvoiceStop F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten template sitesPositive w fit bootHosts startup startingHeader dateDegree other)
variable (censusRoom : ((@fundedInvoiceStop F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten template sitesPositive w fit bootHosts startup startingHeader dateDegree other))+1<2^w)
local notation "banks_" => DescentTerminalLast.trailingBanks w numSlots numBins cut_ rawWords
  (Nat.lt_trans (Nat.lt_succ_self _) censusRoom)
local notation "fed" => (paidCode).seq (DescentTerminalChipRuntime.program cpu bankSet w (K*W) numSlots)
local notation "whole" => DescentTerminalReadout.complete tapeDesc banks_ (cut:=cut_) (stop:=stop_) (rows:=rawWords) (word:=widthWord) fed
local notation "pcs" => (whole).labels+3
local notation "regs" => (whole).registers+1
local notation "binsPaid" => Fintype.card Unit+numBins+1
local notation "obs" => rawWords+binsPaid
local notation "fuel" => paidTime+clocks (K*W) numSlots+ticks tapeDesc banks_ rawWords widthWord+3
local notation "runtime" => CheapISA.hostFuel fuel

local notation "sitePagesAt" x₀:arg z₀:arg c₀:arg => WideEarnedSitePages (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows)
      («paidRows»:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) («rom»:=rom)
      (other:=other) («lo»:=lo) («packWidth»:=packWidth) («head»:=head)
      («fence»:=fence) («count»:=count) («plan»:=plan) («codec»:=codec) (short:=short) (all:=z₀) (c:=c₀)
      (original:=view x₀) («board»:=board) («dateAge»:=dateAge) (dateDegree:=dateDegree)
      («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes)
      («previousDate»:=previousDate) («priorAddress»:=priorAddress) («rosterBank»:=rosterBank)
      («datedFloor»:=datedFloor) («replayBase»:=replayBase) (matrixTable:=matrixAt) («dateTag»:=dateTag)
      («dateRotation»:=dateRotation) («snapshots»:=snapshots) («roleBase»:=roleBase) (replayRoom:=replayRoom)
      (datedMem:=capturedAt x₀ z₀)
/-- Every dense terminal dictionary word is read from the original funded
capture at the same public address at which it was installed. -/
theorem original_funded_dense_words (x₀ : extPins → Bool) (z₀ : Full → Bool)
    {reported saved : ℕ → ℕ} {observed : Prop}
    (receipt : FundedDateInputs S datesAt (startedAt x₀ z₀) startingHeader capture replayBase
      (fun i => (cursor_ i).floor) reported saved observed)
    (archiveEnd : front+extra≤ startingHeader) (headerLow : startingHeader<startup.base)
    (sourceSpace : DescentPackedSeed.publicWords X+DescentDyadicSpan.span initialSource_≤ seedEnd_)
    (liveness : 0<primitiveLanes_) (embed : payloadBits≤w)
    (signedFit : DescentSignedCableCodec.width 3 256*startup.packedLanes≤w)
    (fieldsFit : startup.operandBits*startup.operandLanes≤w) (bootRoom : initialBound_<2^w)
    (i : ℕ) (hi : i<DescentTerminalDenseHeaderBoot.extent q p) :
    (capturedAt x₀ z₀) (rom+i)=DescentTerminalDenseHeaderBoot.back w q p i := by
  have countEnd : capture+(captureDates).length≤front :=
    capture_before_public_front («S»:=S) X payloadBits s (captureDates).length steps packWidth clockCap
      (17*DescentExteriorShelf.span j rest s E₀)
      (scheduled_capture_length X G S ordinary reset branch positive room shorten w fit)
  have later (age₀ : ℕ) : (cursor_ 0).floor≤(cursor_ age₀).floor := by
    induction age₀ with
    | zero => exact le_rfl
    | succ i ih =>
      exact ih.trans (RegisterTimeline.selected_floor (RegisterTimeline.issued (w:=w) traces_ menu_) i (cursor_ i))
  have roleStart : front+extra≤roleBase :=
    archive_before_role_start («S»:=S) (H:=bootHosts) («k»:=k) G rot X startup startingHeader payloadBits Z
      headerLow archiveEnd rfl (later (S).length)
  exact captured_dense_header G rot X ((S).initialDigits ordinary.radix) hostsEnough startup startingHeader
    payloadBits Z seed (histAt z₀) front codes count₀
    (Root.widePackedImage X (S).copies s payloadBits w seed lo G.C packWidth steps compact
      (DescentExterior.publicRows X (view x₀))
      (Sum.elim (histAt z₀) (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr)))
    (z₀ ∘ DescentTerminalFullPins.chip) datesAt rowAddress (captureDates).length roleMount receipt
    countEnd archiveEnd roleStart headerLow sourceSpace liveness embed signedFit fieldsFit bootRoom i hi

local notation "matrixAtSource" x₀:arg z₀:arg c₀:arg => primitiveBank x₀ z₀ matrixFloor =
  ((DescentExterior.matrixCode (Branch.pinSpine X G S (issued X G S ordinary reset branch positive room shorten c₀)
    positive base).matrix).val:Computability.VPVNP.BurstRAM.Word w)
local notation "paidPacketsAt" x₀:arg z₀:arg c₀:arg => WideMeasuredPackets (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary)
  (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c₀)
  (base:=base) (width:=width) («headerRows»:=headerRows) («paidRows»:=paidRows)
  («begin_»:=censusBase) («peer»:=peerBank) («old»:=wingBank) («org»:=lookupBase) («homes»:=dateHomes)
  (primitive:=primitiveBank x₀ z₀) (m:=booksBank x₀ z₀)
local notation "registeredAt" x₀:arg z₀:arg c₀:arg din:arg => WideRegisteredDateRows
    («q»:=q) («j»:=j) («rest»:=rest) («W»:=W) («piece»:=piece) (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary)
    (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=c₀)
    («board»:=board) («dateAge»:=dateAge) (dateDegree:=dateDegree) («datePayload»:=datePayload)
    («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes)
    («previousDate»:=previousDate) («priorAddress»:=priorAddress) («rosterBank»:=rosterBank)
    («datedFloor»:=datedFloor) («replayBase»:=replayBase) (matrixTable:=matrixAt) («dateRotation»:=dateRotation)
    («snapshots»:=snapshots) («roleBase»:=roleBase) (dateInput:=din) (datedMem:=capturedAt x₀ z₀)
    («headerRows»:=headerRows) («paidRows»:=paidRows)


open DescentDatedAddressBook.PhysicalReset DescentCompiler.TerminalScale
variable {driftRate ratio : ℕ}
local notation "baseR_" => (NativePitch.FundedBase.public_rate G rounds f g restart).choose
local notation "funds_" => 44*argumentDigitRate G rounds f g restart driftRate baseR_
local notation "stage_" i:arg H:arg => SignedStage.atDate G S g k i H
local notation "mark_" => countDates 0 (kindCalendar (S).rounds (S).height)

local notation "earnedFund_" => ((S).copies*s)*(siteCount+2^depth_*E₀)
local notation "sourceFee_" a:arg r:arg => 5+a+(1135*(r+1)+a)
local notation "isaFee_" r:arg => 257*(1000*(2*(7*(r+6))+2)*(2*4^7+1))+256*fixedISAPrice*(r+6)
local notation "reelBody_" => (((Branch.historyMountedReel X S replayBase dateTag dateRotation countAt capture matrixAt
  k tail j rest s w (roleMount).phase).seq termCode).seq (relocate j rest s E₀ w compact wall)).seq
  ((plan).program j rest s E₀ w B₀ (S).length wall)
local notation "reelFee_" => (((4+11*(captureDates).length)+(roleMount).phase.ticks)+
  DescentExteriorMatrixUpdate.Calendar.earlyClock S k tail j rest s datePorts)+termCost+
  (4+18*(17*DescentExteriorShelf.span j rest s E₀))+(10+((4+58*(S).length)+(4+16*E₀)))+
  7*DescentStaticWordColumn.names reelBody_
local notation "endFee_" => AddressPlan.time V cfg I_ R_ start head+clocks (K*W) numSlots+
  7*(DescentStaticWordColumn.names (AddressPlan.clock V cfg I_ R_ start head short literal (bw:=w))+
    DescentStaticWordColumn.names (DescentTerminalChipRuntime.program cpu bankSet w (K*W) numSlots))

local notation "bootHead_" wire:arg hist:arg => originalSeedHead G rot R X steps S k tail payloadBits
  bootHosts dateDegree wire hist (terminalBinCount X G S p q W n h C f g+1) rawWords

section
attribute [local irreducible] DescentStaticWordColumn.names DescentWideSeedFlags.check DescentPackedSeed.rows
  DescentDatedSeedStartup.Input.completeAfter DescentDatedSeedStartup.Input.completeTicks

/-- The funded seed of this chart and its selected cuts pay the complete boot prefix. -/
theorem original_funded_boot_dates (ratio limit startRate wire hist:ℕ)
    (bus:w=ratio*payloadBits) (factor:0 < payloadBits)
    (ambient:2^payloadBits≤ siteCount) (upper:siteCount≤(2^payloadBits)^2) (dyadic:∃a,siteCount=2^a)
    (heightMatch:bootHosts=DescentDyadicSpan.span siteCount) (degreeMatch:dateDegree≤ limit)
    (startupMatch:startup=(bootHead_ wire hist).layout G rounds f g R payloadBits)
    (headerMatch:startingHeader=(bootHead_ wire hist).base G payloadBits-1)
    (seedReceipt:DescentDatedSeedStartup.CompleteAfterAt G rot rounds f g restart R limit
      (DescentCompiler.quota rounds) τ β (ratio+1) payloadBits)
    (calendarReceipt:NormalizedRuns G board rot rounds f g restart cut R limit branch startRate ratio τ β payloadBits) :
    ((4+(seedRows+1)*66+7*DescentStaticWordColumn.names prefixCode)+
      (bootCost+7*DescentStaticWordColumn.names bootCode))*(w+1)*2^depth_≤4*earnedFund_ ∧
    (∑i∈Finset.range (S).length,(datesAt i).tariff)*2^depth_≤2*earnedFund_ :=by
  have transit : ∀i,datesAt i=RegisterTimeline.instruction (w:=w) traces_ menu_ entry_ i:=by
    intro i
    exact RegisterTimeline.fromCuts_date _ _ i
  simp_rw [transit]
  subst startup
  subst startingHeader
  have wide : siteCount≤ bootHosts:=heightMatch ▸ DescentDyadicSpan.span_ge _
  have rounded : bootHosts≤ hostRows siteCount:=heightMatch.le
  have bpos : 0 < G.b:=by have:=G.paid;omega
  have firstWidth_ge : p≤ s:=by
    change p ≤ (S).firstWidth G.b p
    unfold AtomSchedule.firstWidth AtomSchedule.grainAt
    exact (Nat.le_mul_of_pos_right p (pow_pos bpos _)).trans (Nat.le_mul_of_pos_right _ bpos)
  constructor
  · have paid:=DescentDatedSeedStartup.SeedHeader.Input.complete_invoice_at G rot rot rounds f g restart R
      limit τ β (ratio+1) payloadBits siteCount bootHosts dateDegree wire hist
      (terminalBinCount X G S p q W n h C f g+1) rawWords X steps w w E₀ seedReceipt rfl heightMatch
      hostsEnough ambient degreeMatch (by rw [bus,Nat.add_mul,Nat.one_mul];omega) le_rfl
    exact regroupBootInvoice paid
  · subst w
    have actual:=(calendarReceipt siteCount ambient upper dyadic X ordinary reset rfl positive room shorten fit
      bootHosts dateDegree wire hist wide rounded degreeMatch).2
    exact registeredDateSumFits actual firstWidth_ge

end


local notation "frontierRate_" => originalFrontierRate n h C rounds f g
local notation "receiptFactor_" ratio:arg => originalChipFactor G rounds f g restart ratio τ
local notation "selectedTemplate_" => shellTemplate X G rounds depth_ f g restart siteCount τ payloadBits
  n h C (show 0 < siteCount from by have fine:=room;change 10*(X.size+1)≤ siteCount at fine;omega)

include base ordinary in
/-- The sixteen original input banks and the final compiled chip use the same
chosen public shell and the same preflight input pages. -/
theorem original_funded_chip_tables (ratio limit:ℕ)
    (purchased:OriginalPurchaseAt G rot rounds f g restart n h C R limit ratio τ β payloadBits)
    (ambient:2^payloadBits≤ siteCount) (upper:siteCount≤(2^payloadBits)^2)
    (live:0 < payloadBits) (bus:w=ratio*payloadBits)
    (shape:template=selectedTemplate_) (fallback:other=AddressPlan.fixedFallback) :
    extra*w*2^depth_≤ originalAppendixPrice (receiptFactor_ ratio) frontierRate_*earnedFund_ ∧
    endFee_*(w+1)*2^depth_≤ originalChipPrice (receiptFactor_ ratio) frontierRate_*earnedFund_:=by
  classical
  let x : ShellSource F payloadBits := ⟨cp,P,siteCount,X,room,upper⟩
  let L := originalPlacement G rounds f g restart τ β n h C rot R x front lookupBase peerBank dateHomes wingBank
  have copies : 0 < (S).copies := by
    rw [AtomSchedule.copies,base,ordinary.radix]
    positivity
  have shell_eq : cfg = earnedShell G rounds f g restart τ β n h C x L := by
    rw [shape]
    exact original_placement_shape G rounds f g restart τ β n h C rot R x front lookupBase peerBank dateHomes wingBank
  have input_eq : I_ = earnedInput G rounds f g restart τ β n h C rot R x L := by
    rw [shape, fallback]
    exact original_placement_input G rounds f g restart τ β n h C rot R x front lookupBase peerBank dateHomes wingBank
  exact funded_chip_prices_at_placement G rounds f g restart τ β n h C rot R x front lookupBase peerBank dateHomes wingBank
    ratio limit purchased cfg I_ shell_eq input_eq R_ start head w (pre).vertices B short literal bankSet ambient copies live bus



/-- The acquired final registers drive the old count, the newly issued dictionary,
both matrix reels, the preflight and the public relocation of the actual machine. -/
theorem original_funded_reel_price (ratio limit : ℕ) :
  let reelDepth := Nat.log 2 payloadBits/(2*β)
  let reelTail := DescentCompiler.TerminalScale.tail τ reelDepth
  let reelSchedule := stageNumbers G rounds reelDepth f g restart siteCount reelTail
  let reelGroupBits := groupBits rounds reelDepth (hostRate rounds restart) (capRate G rounds g) (cutRate rounds f g)
  let reelBinWidth := NativeBranch.binLimit («k»:=reelGroupBits) reelSchedule
  let reelLocalBits := Nat.clog 2 (NativeBranch.localLimit G reelSchedule)
  let reelPublicSlots := 2^reelLocalBits*(G.b^(rounds*reelDepth)*G.b)
  let reelPiece := payloadBits/(16*(reelPublicSlots*reelBinWidth))
  let reelRest := (reelSchedule).groupWidth reelGroupBits reelTail 0+reelGroupBits-2*reelLocalBits
  let reelGrainBundle := reelBinWidth*reelPiece
  let reelFirstWidth := (reelSchedule).firstWidth G.b reelGrainBundle
  let reelInitialGrain := (reelSchedule).grainAt G.b reelGrainBundle 0
  let reelRot := RotorSpec.ofRates reset
  let reelDrift := max 1 (max reset.bitsR (C*reset.bitsR))
  let reelCap := NativeBranch.privateSlotCapacity G reelSchedule reelDrift
  let reelNodeCap := (reelSchedule).epochPower^(reelSchedule).localTokenExponent
  let reelVenues := (reelSchedule).groupCount (reelSchedule).length*2^reelGroupBits
  let reelPorts := Fintype.card (Port P X.width)
  let reelHosts := (reelSchedule).hostSize (reelSchedule).length
  let reelRawWords := terminalRawRows X G reelSchedule reelGrainBundle reelPublicSlots n h C f g
  let reelHeaderRows := terminalPool X G reelSchedule reelGrainBundle reelPublicSlots reelBinWidth n h C f g
  let reelPaidRows := reelHeaderRows
  let reelShape := Branch.exteriorShape template reelPorts reelLocalBits reelRest reelFirstWidth reelRawWords reelHeaderRows reelHosts sitesPositive
  let reelGroupsAt := (reelSchedule).groupCount (reelSchedule).length
  let reelBins := calibratedBins X G rounds reelDepth f g restart siteCount τ payloadBits n h C
  let reelChart := normalizedPackedChart X G reelSchedule ordinary reset branch positive room shorten w fit
  let reelFormat := Branch.geometryFormat G reelSchedule reelGroupBits g reelGrainBundle reelTail reelPublicSlots reelDrift reelRot reelHeaderRows reelPaidRows
  let reelPreflight := Branch.preflightSpec X G reelSchedule reelGroupBits g reelGrainBundle reelTail ({reelFormat with binSize:=reelBinWidth}:Branch.PreflightFormat)
  let reelSteps := (reelChart).layout
  let reelSelectorBase := DescentWideSeedFlags.selectorBase X (reelSchedule).copies reelFirstWidth payloadBits (reelSteps).length
  let reelPackWidth := DescentPackedEpochShelves.grain (payloadBits/2) G.C
  let reelMatrixAt := end_ (reelSelectorBase+extent reelPackWidth reelSteps) G.C reelPackWidth
  let reelStartupPrimitiveLanes := DescentDatedSeedStartup.Primitive.paletteLanes G reelRot startup.seedWidth reelInitialGrain payloadBits reelGroupBits
  let reelSeedEnd := (DescentDatedSeedStartup.Input.nodeChart startup reelGroupBits bootHosts ((reelSchedule).groupCount 0)).seedEnd (DescentDatedSeedStartup.endAddress X startup bootHosts ((reelSchedule).groupCount 0) reelGroupBits)
  let reelInitialBound := DescentDatedSeedStartup.Primitive.initialEnd X (reelSchedule).copies startup.seedWidth payloadBits reelGroupBits bootHosts ((reelSchedule).groupCount 0) reelStartupPrimitiveLanes reelSeedEnd
  let reelEntry := (⟨DatePorts.initial G reelRot X (reelSchedule).copies startup reelGroupBits bootHosts ((reelSchedule).groupCount 0) payloadBits reelInitialGrain, reelInitialBound⟩ : RegisterTimeline.Position)
  let reelBoard := reset.board
  let reelTraces := traceAt X G reelSchedule ordinary reset branch positive room shorten
  let reelMenu := RegisterTimeline.fromProfiles G reelSchedule reelBoard reelRot reelGroupBits reelTail reelGrainBundle f g reelDrift dateDegree payloadBits reelSelectorBase startingHeader reelSteps
  let reelCursor := RegisterTimeline.calendar (w:=w) reelTraces reelMenu reelEntry
  let reelDateAge := (reelSchedule).length-1
  let reelPrior := reelCursor reelDateAge
  let reelOrdinaryAt := (reelMenu).ordinary
  let reelDatePayload := payloadBits
  let reelOperandLanes := (reelPrior).ports.operandLanes
  let reelCalendarPrimitiveLanes := (reelPrior).ports.roleLanes
  let reelPreviousDate := (reelPrior).ports.venue
  let reelPriorAddress := (reelPrior).ports.io.wire
  let reelRosterBank := (reelPrior).ports.io.roster
  let reelDatedFloor := (reelPrior).ports.priorStart reelGroupBits (reelPrior).floor
  let reelDateTag := RegisterTimeline.Menu.resetFlag reelSchedule
  let reelDateRotation := fun i=>(reelMenu).rotationAt G reelSchedule reelGroupBits i (reelCursor i)
  let reelCountAt := fun i=>(reelMenu).selectorAt G reelSchedule reelGroupBits i (reelCursor i)
  let reelSnapshotDirectory := RegisterTimeline.snapshotDirectory (w:=w) reelTraces reelMenu reelEntry
  let reelSnapshots := Hierarchy.DescentSixParty.Chronology.SnapshotCalendar reset (kindCalendar (reelSchedule).rounds (reelSchedule).height) (capCalendar G.b (reelSchedule).rounds g (reelSchedule).height) reelSnapshotDirectory
  let reelRankFloor := (reelCursor (reelSchedule).length).floor
  let reelRoleBase := max reelRankFloor (reelMatrixAt+32*DescentExteriorShelf.span reelLocalBits reelRest reelFirstWidth reelPorts)
  let reelReplayBase := reelRoleBase+DescentTerminalRoleTables.count (originalRoleBits G reelRot reelSchedule reelGrainBundle reelDrift)
  let reelDateSpec := preflightSpec X G reelSchedule reelGroupBits g reelGrainBundle reelTail (geometryFormat G reelSchedule reelGroupBits g reelGrainBundle reelTail reelPublicSlots reelDrift reelRot reelHeaderRows reelPaidRows)
  let reelDatePorts := Fintype.card (Port P X.width)
  let reelDatePhase := Phase.scheduled G reelSchedule reelBoard reelGroupBits reelTail reelDateAge reelGrainBundle f g reelDrift dateDegree reelDatePayload reelOrdinaryAt reelRot reelOperandLanes reelCalendarPrimitiveLanes reelPreviousDate reelPriorAddress reelRosterBank reelDatedFloor
  let reelDateOut := (reelDatePhase).output
  let reelDateOrigin := (reelDatePhase).dateBase
  let reelDateCalendar := replayCalendar X reelSchedule reelGroupBits reelTail reelLocalBits reelRest reelSnapshots
  let reelEarlyFloor := DescentExteriorMatrixUpdate.Calendar.earlyEnd reelSchedule reelGroupBits reelTail reelReplayBase reelLocalBits reelRest reelFirstWidth reelDatePorts
  let reelSliceEnd := (reelDatePhase).stop reelEarlyFloor
  let reelLookupBase := (reelDateCalendar).packetEnd reelSliceEnd
  let reelLookupPage := (reelDateSpec).scanPages reelLookupBase reelPublicSlots
  let reelCensusBase := (reelLookupPage).stop
  let reelDateHardware := (reelDateOut).receiver
  let reelDateBlocks := (reelDateSpec).scalar.blocks
  let reelBlockCast := (rfl : reelDateBlocks=(reelDateHardware).blocks)
  let reelPaidBank := fun x:Fin reelDateBlocks=>(reelDateOut).terminalPaid reelDateOrigin x.val
  let reelActorBank := fun x:Fin reelDateBlocks=>(reelDateOut).terminalActor reelDateOrigin x.val
  let reelWingBank := fun (x:Fin reelDateBlocks) (a:Fin (2*(reelDateSpec).cap))=>(reelDateOut).terminalWing reelDateOrigin x.val a.val
  let reelPeerBank := (reelDateOut).terminalPeer reelDateOrigin
  let reelDateHomes := (reelDateCalendar).homes reelSliceEnd
  let reelBegin := reelCensusBase
  let reelPeer := reelPeerBank
  let reelOld := reelWingBank
  let reelOrigin := reelLookupBase
  let reelHomes := reelDateHomes
  let reelArity := max 8 (2^(reelSchedule).capGain)
  let reelGroups := reelCap
  let reelStride := reelDrift
  let reelOldTags := DescentPrimitivePalette.colors G reelFirstWidth reelInitialGrain reelRot
  let reelTagCount := DescentBundleTagKeys.capacity reelOldTags reelArity reelGroups reelGrainBundle reelStride
  let reelHomeFormat := (⟨reelPublicSlots,reelTagCount,reelCap,reelNodeCap,reelCap,reelGrainBundle,reelGroupsAt⟩:Home.Format)
  let reelPagesZero := (reelPreflight).scanPages reelOrigin reelPublicSlots
  let reelTotal := (reelPagesZero).total
  let reelModulo := (reelPagesZero).modulo
  let reelBoundary := (reelPagesZero).boundaries
  let reelTables := (RouteSources.Tables.mk 4 reelVenues (reelVenues*NativeBranch.localLimit G reelSchedule) (NativeBranch.localLimit G reelSchedule) (Book.tokenBits (reelVenues*NativeBranch.localLimit G reelSchedule)) reelBinWidth reelPublicSlots reelBins)
  let reelPageBits := (reelPreflight).pageBits
  let reelCodes := DescentTerminalScalarHeader.range reelPublicSlots reelTagCount reelCap reelNodeCap reelCap reelGrainBundle reelVenues
  let reelClockCap := G.C
  let reelFront := end_ (reelSelectorBase+extent reelPackWidth reelSteps) reelClockCap reelPackWidth+17*DescentExteriorShelf.span reelLocalBits reelRest reelFirstWidth reelPorts
  let reelBootRom := reelFront+DescentTerminalChipBootWords.total reelBins reelBinWidth reelPublicSlots reelPiece reelCodes
  let reelInput := (reelPreflight).reachedInput reelBegin reelBootRom reelPublicSlots reelPiece reelBinWidth reelBins reelCodes reelFront reelPeer reelOld reelTotal reelModulo reelHomes reelBoundary reelShape reelHomeFormat other reelTables (reelPreflight).vertices reelPageBits
  let reelChannels := (reelPreflight).channels reelBegin
  let reelStart := (reelPreflight).maskBase reelBegin
  let reelBase := afterMeter reelHomeFormat reelShape reelChannels reelStart
  let reelWall := AddressPlan.takeOff (reelShape) reelInput reelBase
  let reelCompact := end_ (reelSelectorBase+extent reelPackWidth reelSteps) G.C reelPackWidth
  let reelSeedBase := DescentWideSeedFlags.endInput X (reelSchedule).copies reelFirstWidth payloadBits
  let reelSeedRows := DescentPackedSeed.rows X (reelSchedule).copies reelFirstWidth payloadBits
  let reelDimension := (reelSchedule).groupWidth reelGroupBits reelTail 0+reelGroupBits
  let reelCapture := reelSeedBase+reelSeedRows+1
  let reelRoleMount := originalRoleMount G reelRot reelSchedule reelGrainBundle reelDrift reelRoleBase reelReplayBase le_rfl replayFits
  let reelCaptureDates := countDates 0 (kindCalendar (reelSchedule).rounds (reelSchedule).height)
  let reelOldReel := DescentExteriorMatrixUpdate.Calendar.reel reelSchedule reelGroupBits reelTail reelReplayBase reelDateTag reelDateRotation
  let reelTermCode := Branch.postEarlyPreflight X G reelSchedule base ordinary.radix g reelGrainBundle reelPublicSlots reelDrift reelRot reelHeaderRows reelPaidRows reelLocalBits reelRest reelFirstWidth reelReplayBase reelDatePhase reelSnapshots reelBlockCast reelRoleBase reelPeerBank reelPaidBank reelActorBank reelWingBank replayRoom
  let reelTermCost := Branch.postEarlyPreflightClocks X G reelSchedule («k»:=reelGroupBits) («tail»:=reelTail) g reelGrainBundle reelPublicSlots reelDrift reelRot reelHeaderRows reelPaidRows reelLocalBits reelRest reelFirstWidth reelReplayBase reelDatePhase reelSnapshots reelBlockCast reelPeerBank reelPaidBank reelActorBank reelWingBank replayRoom
  let reelUpperFence := (reelPreflight).maskBase reelCensusBase
  let reelFreshReel := (reelOldReel).late reelUpperFence
  let reelPlan := reelFreshReel
  let reelEarnedFund := ((reelSchedule).copies*reelFirstWidth)*(siteCount+2^reelDepth*reelPorts)
  let reelReelBody := (((Branch.historyMountedReel X reelSchedule reelReplayBase reelDateTag reelDateRotation reelCountAt reelCapture reelMatrixAt reelGroupBits reelTail reelLocalBits reelRest reelFirstWidth w (reelRoleMount).phase).seq reelTermCode).seq (relocate reelLocalBits reelRest reelFirstWidth reelPorts w reelCompact reelWall)).seq ((reelPlan).program reelLocalBits reelRest reelFirstWidth reelPorts w reelDimension (reelSchedule).length reelWall)
  let reelReelFee := (((4+11*(reelCaptureDates).length)+(reelRoleMount).phase.ticks)+ DescentExteriorMatrixUpdate.Calendar.earlyClock reelSchedule reelGroupBits reelTail reelLocalBits reelRest reelFirstWidth reelDatePorts)+reelTermCost+ (4+18*(17*DescentExteriorShelf.span reelLocalBits reelRest reelFirstWidth reelPorts))+(10+((4+58*(reelSchedule).length)+(4+16*reelPorts)))+ 7*DescentStaticWordColumn.names reelReelBody
  let reelFrontierRate := originalFrontierRate n h C rounds f g
  ∀
    (_purchased:OriginalPurchaseAt G reelRot rounds f g restart n h C reelDrift limit ratio τ β payloadBits)
    (_ambient:2^payloadBits≤ siteCount) (_upper:siteCount≤(2^payloadBits)^2)
    (_live:0 < payloadBits) (_bus:w=ratio*payloadBits) (_narrow:payloadBits+1≤ w)
    («_fields»:FinalSliceFields G reelSchedule reelGroupBits reelDrift payloadBits reelDatePhase) (_lastDate:reelDateAge+1=(reelSchedule).length)
    (_attained:(reelDateOut).metadataEnd reelDateOrigin≤ DescentExteriorMatrixUpdate.Calendar.earlyEnd
      reelSchedule reelGroupBits reelTail reelReplayBase reelLocalBits reelRest reelFirstWidth reelPorts),

    reelReelFee*(payloadBits+1)*2^reelDepth≤ originalPostPrice (receiptFactor_ ratio) reelFrontierRate*reelEarnedFund := by
  intro reelDepth reelTail reelSchedule reelGroupBits reelBinWidth reelLocalBits reelPublicSlots reelPiece reelRest reelGrainBundle reelFirstWidth reelInitialGrain reelRot reelDrift reelCap reelNodeCap reelVenues reelPorts reelHosts reelRawWords reelHeaderRows reelPaidRows reelShape reelGroupsAt reelBins reelChart reelFormat reelPreflight reelSteps reelSelectorBase reelPackWidth reelMatrixAt reelStartupPrimitiveLanes reelSeedEnd reelInitialBound reelEntry reelBoard reelTraces reelMenu reelCursor reelDateAge reelPrior reelOrdinaryAt reelDatePayload reelOperandLanes reelCalendarPrimitiveLanes reelPreviousDate reelPriorAddress reelRosterBank reelDatedFloor reelDateTag reelDateRotation reelCountAt reelSnapshotDirectory reelSnapshots reelRankFloor reelRoleBase reelReplayBase reelDateSpec reelDatePorts reelDatePhase reelDateOut reelDateOrigin reelDateCalendar reelEarlyFloor reelSliceEnd reelLookupBase reelLookupPage reelCensusBase reelDateHardware reelDateBlocks reelBlockCast reelPaidBank reelActorBank reelWingBank reelPeerBank reelDateHomes reelBegin reelPeer reelOld reelOrigin reelHomes reelArity reelGroups reelStride reelOldTags reelTagCount reelHomeFormat reelPagesZero reelTotal reelModulo reelBoundary reelTables reelPageBits reelCodes reelClockCap reelFront reelBootRom reelInput reelChannels reelStart reelBase reelWall reelCompact reelSeedBase reelSeedRows reelDimension reelCapture reelRoleMount reelCaptureDates reelOldReel reelTermCode reelTermCost reelUpperFence reelFreshReel reelPlan reelEarnedFund reelReelBody reelReelFee reelFrontierRate purchased ambient upper live bus narrow sliceFields lastDate attained
  classical

  let x : ShellSource F payloadBits:=⟨cp,P,siteCount,X,room,upper⟩

  let L:=originalPlacement G rounds f g restart τ β n h C reelRot reelDrift x reelFront reelLookupBase reelPeerBank reelDateHomes reelWingBank
  have copies:0 < (reelSchedule).copies:=by rw [AtomSchedule.copies,base,ordinary.radix];positivity
  have support:2^payloadBits≤2*(siteCount*(reelSchedule).copies):=
    (ambient.trans (Nat.le_mul_of_pos_right _ copies)).trans (Nat.le_mul_of_pos_left _ (by decide))
  have arch:w+1≤(receiptFactor_ ratio)*payloadBits:=by
    calc
      w+1 ≤ ratio*payloadBits+payloadBits:=by rw [bus]; exact Nat.add_le_add_left live _
      _=(ratio+1)*payloadBits:=by ring
      _≤ _:=Nat.mul_le_mul_right _ (Nat.le_max_left ..)

  obtain ⟨p₀,small,sites,bulk,b₀,b₁,sweep,headers,payers,packing⟩:=purchased.rows x L w support arch

  have acquired := purchased_reel_slice G rounds reelDepth f g restart siteCount τ reelDrift payloadBits reelDatePhase sliceFields packing
  let selection:=(normalizedRoute X G reelSchedule ordinary reset branch positive room shorten w fit).follow (fun _=>false)
  let b:=issued X G reelSchedule ordinary reset branch positive room shorten selection

  have oldPrice:=purchased.replay.counted siteCount w (receiptFactor_ ratio) reelReplayBase reelCapture reelMatrixAt reelUpperFence reelWall
    X ordinary.radix base b reelDateTag reelDateRotation reelCountAt reelOldReel reelDatePhase reelSnapshots
    reelHeaderRows reelPaidRows reelPublicSlots reelGrainBundle reelBinWidth reelHosts reelFrontierRate (reelSchedule).radix reelRoleBase reelBlockCast reelPeerBank reelPaidBank reelActorBank reelWingBank replayRoom
    p₀ small purchased.before purchased.scalar sites support (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) narrow) arch bulk b₀ b₁ sweep headers payers packing
    acquired attained sliceFields.hosts (sitesPositive.trans_eq sliceFields.hosts.symm) sliceFields.arguments.le sliceFields.blocks.le rfl

  have installed:=purchased.replay.installed siteCount reelGrainBundle reelRoleBase reelReplayBase w le_rfl replayFits ambient small

  have dpos:0 < (reelSchedule).copies*reelFirstWidth:=Nat.mul_pos copies (Nat.mul_pos ((reelSchedule).grain_positive G.base_pos p₀ 0) G.base_pos)
  have home:siteCount≤ reelEarnedFund:=(Nat.le_add_right ..).trans (Nat.le_mul_of_pos_left _ dpos)

  exact Branch.reel_from_purchased_charges X reelSchedule reelReplayBase reelDateTag reelDateRotation reelCountAt reelCapture reelMatrixAt
    reelGroupBits reelTail reelLocalBits reelRest reelFirstWidth w (reelRoleMount).phase reelTermCode reelTermCost reelPlan reelDimension reelWall payloadBits reelDepth
    (receiptFactor_ ratio) reelFrontierRate reelEarnedFund siteCount narrow home oldPrice installed



private theorem originalSeedPaid (ratio appendixRate:ℕ)
    (bus : w=ratio*payloadBits)
    (ambient : 2^payloadBits≤ siteCount) (upper : siteCount≤(2^payloadBits)^2)
    (initialBill : OriginalInitialPriceAt G rounds f g restart τ β ratio payloadBits)
    (tables : extra*w*2^depth_≤ appendixRate*earnedFund_) :
    (4*((seedNet).cells+(seedNet).internal)+Fintype.card Full+Fintype.card extPins+
      firstFree*(payloadBits+1))*2^depth_≤(sourceFee_ appendixRate ratio)*earnedFund_ := by
  let x : ShellSource F payloadBits:=⟨cp,P,siteCount,X,room,upper⟩
  subst w
  exact initialBill x ambient cut n h C K codes appendixRate cfg ordinary reset branch positive shorten fit tables



private theorem originalFoldPaid
    (axes : StageFeeAxes G rot R rounds f g restart τ β payloadBits siteCount)
    (voteBill : WideFoldTariffAt G rounds f g restart τ β (localSocketRate G rounds g) payloadBits) :
    (bill initialFlag dst foldSites+7*DescentStaticWordColumn.names
      (fold w initialFlag dst foldSites))*(payloadBits+1)*2^depth_≤2048*earnedFund_ := by
  have verdict:=voteBill siteCount X (2^j) p E₀ k cut n h C tail w
    ordinary reset branch positive room shorten fit (Nat.two_pow_pos _) axes.slots axes.bulk axes.dates
    firstFree lo initialFlag count (fun _=>initialFlag)
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))).trans verdict



/-- The native machine uses the measured initial input, counted verdict, installed
dates, mounted replay and compiled chip at the same dyadic site count. -/
theorem original_funded_stage_invoice (ratio appendixRate postRate chipRate:ℕ)
    (bus : w=ratio*payloadBits) (narrow : payloadBits+1≤ w)
    (ambient : 2^payloadBits≤ siteCount) (upper : siteCount≤(2^payloadBits)^2)
    (axes : StageFeeAxes G rot R rounds f g restart τ β payloadBits siteCount)
    (initialBill : OriginalInitialPriceAt G rounds f g restart τ β ratio payloadBits)
    (voteBill : WideFoldTariffAt G rounds f g restart τ β (localSocketRate G rounds g) payloadBits)
    (tables : extra*w*2^depth_≤ appendixRate*earnedFund_)
    («initialize» : ((4+(seedRows+1)*66+7*DescentStaticWordColumn.names prefixCode)+
      (bootCost+7*DescentStaticWordColumn.names bootCode))*(w+1)*2^depth_≤4*earnedFund_)
    (issuedDates : (∑i∈Finset.range (S).length,(datesAt i).tariff)*2^depth_≤2*earnedFund_)
    (replay : reelFee_*(payloadBits+1)*2^depth_≤ postRate*earnedFund_)
    (finish : endFee_*(w+1)*2^depth_≤ chipRate*earnedFund_) :
    (4*((seedNet).cells+(seedNet).internal)+9*(rawWords*widthWord)+binsPaid*(w+1)+
      Fintype.card Full+Fintype.card extPins+
      (isaFee_ ratio)*(pcs+regs+firstFree+fuel+obs+2^payloadBits+1)*(payloadBits+1))*2^depth_≤
    earnedHostPrice (sourceFee_ appendixRate ratio) (sourceFee_ appendixRate ratio)
      (6+postRate+2048+chipRate) ratio (isaFee_ ratio)*earnedFund_ :=by
  have seedPaid := @originalSeedPaid F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset
    branch positive room shorten template sitesPositive w fit ratio appendixRate bus
    ambient upper initialBill tables
  have vote := @originalFoldPaid F _ cp P X G cut n h C f g rounds restart τ β siteCount payloadBits ordinary reset
    branch positive room shorten w fit axes voteBill
  have boot := DateCode.paid_original_boot prefixCode bootCode datesAt (4+(seedRows+1)*66)
    bootCost (S).length (payloadBits+1) (2^depth_) earnedFund_ 4 2 narrow «initialize» issuedDates
  have ending := originalFinalWordCharge narrow finish
  exact @wide_earned_native_bill
    F _ cp P X G S k cut tail n h C f g W q piece ordinary reset branch positive room shorten j rest
    base qh template sitesPositive rawWords headerRows paidRows w K payloadBits fit lo packWidth h
    board dateAge dateDegree datePayload ordinaryAt operandLanes primitiveLanes previousDate
    priorAddress rosterBank datedFloor replayBase dateTag dateRotation snapshots roleBase replayRoom
    rom other head short bootHosts hostsEnough startup startingHeader datesAt capture countAt
    roleMount censusRoom ratio (2^depth_) siteCount (sourceFee_ appendixRate ratio) 6 postRate 2048
    chipRate bus.le ((Nat.two_pow_pos _).trans_le ambient) ambient axes.mode axes.keys seedPaid boot
    replay vote ending (axes.inventory E₀)


open Lean Elab Term Meta in
local elab "useFundedReceipt " receiptDecl:ident " with " "[" keys:ident,* "]" "[" args:term,* "]" : term => do
  let keys := keys.getElems.map (·.getId)
  let args := args.getElems
  unless keys.size == args.size do throwError "mismatched receipt arguments"
  let fn ← try getFVarFromUserName receiptDecl.getId catch _ =>
    pure <| mkConst (← resolveGlobalConstNoOverload receiptDecl)
  let mut type ← inferType fn
  let mut values := #[]
  let mut afterLet := false
  repeat
    match type with
    | .forallE name dom body info =>
      let value ← if let some i := keys.findIdx? (· == name) then
        elabTerm args[i]! none
      else if info.isInstImplicit then
        if afterLet then throwError "unexpected section instance after a receipt definition: {name}"
        synthInstance (dom.instantiateRev values)
      else
        getFVarFromUserName name
      values := values.push value
      type := body
    | .letE _ _ _ body _ =>
      afterLet := true
      type := body
    | .mdata _ body => type := body
    | _ => break
  return mkAppN fn values

include hostsEnough qh short replayRoom replayFits in
/-- The fixed price covers the whole original dyadic host for every circuit at
the purchased height. All operational data come from the installed starting state
and the attained last reset. -/
theorem original_funded_invoice_from_purchase (ratio limit startRate wire hist:ℕ)
    (purchased:OriginalPurchaseAt G rot rounds f g restart n h C R limit ratio τ β payloadBits)
    (calendarReceipt:NormalizedRuns G board rot rounds f g restart cut R limit branch startRate ratio τ β payloadBits)
    (bus:w=ratio*payloadBits) (narrow:payloadBits+1≤ w) (live:0 < payloadBits)
    (ambient:2^payloadBits≤ siteCount) (upper:siteCount≤(2^payloadBits)^2) (dyadic:∃a,siteCount=2^a)
    (heightMatch:bootHosts=DescentDyadicSpan.span siteCount) (degreeMatch:dateDegree≤ limit)
    (startupMatch:startup=(bootHead_ wire hist).layout G rounds f g R payloadBits)
    (headerMatch:startingHeader=(bootHead_ wire hist).base G payloadBits-1)
    (shape:template=selectedTemplate_) (fallback:other=AddressPlan.fixedFallback)
    («fields»:FinalSliceFields G S k R payloadBits datePhase) (lastDate:dateAge+1=(S).length)
    (attained:(dateOut).metadataEnd dateOrigin≤ DescentExteriorMatrixUpdate.Calendar.earlyEnd
      S k tail replayBase j rest s E₀) :
    (4*((seedNet).cells+(seedNet).internal)+9*(rawWords*widthWord)+binsPaid*(w+1)+
       Fintype.card Full+Fintype.card extPins+
       (isaFee_ ratio)*(pcs+regs+firstFree+fuel+obs+2^payloadBits+1)*(payloadBits+1))*2^depth_≤
    originalHostPrice G rounds f g restart n h C ratio τ*earnedFund_:= by
  let factor := originalChipFactor G rounds f g restart ratio τ
  let rate := originalFrontierRate n h C rounds f g
  have started := useFundedReceipt original_funded_boot_dates with [factor, seedReceipt] [live, purchased.seed]
  have terminal := useFundedReceipt original_funded_chip_tables with [] []
  have reel := useFundedReceipt original_funded_reel_price with
    [_purchased, _ambient, _upper, _live, _bus, _narrow, _fields, _lastDate, _attained]
    [purchased, ambient, upper, live, bus, narrow, «fields», lastDate, attained]
  exact useFundedReceipt original_funded_stage_invoice with
    [appendixRate, postRate, chipRate, axes, initialBill, voteBill, tables, «initialize», issuedDates, replay, finish]
    [originalAppendixPrice factor rate, originalPostPrice factor rate, originalChipPrice factor rate,
     purchased.axes siteCount ambient, purchased.initial, purchased.verdict, terminal.1, started.1, started.2,
     reel, terminal.2]


open Chronology.RegisterTimeline
attribute [local irreducible] RunTrace.machine DateCode.history Path.snapshotRanks Path.dateReadbacks Path.Held
open Lean Elab Term in
local elab "hostPurchaseRank% " fn:term:arg "[" args:term,* "]" : term => do
  let f ← elabTerm fn none
  let context ← getLCtx
  let lvar (n : Name) : TermElabM Lean.Expr := do
    let some d := context.findFromUserName? n | throwError "missing funded input {n}"
    return d.toExpr
  let knownArgs ← args.getElems.mapM fun x => do
    if x.isIdent then
      if let some d := context.findFromUserName? x.getId then return d.toExpr
    elabTerm x none
  let ballot := mkApp2 (← lvar `funded) (← lvar `x₀) (← lvar `z₀)
  let recordedRead := mkProj ``And 1 (mkProj ``And 1 ballot)
  let readTy ← instantiateMVars (← Meta.inferType recordedRead)
  let rankTy := readTy.consumeMData.bindingBody!.consumeMData.bindingBody!.consumeMData
  unless rankTy.getAppFn.isConstOf ``Chronology.Path.snapshotRanks do
    throwError "unexpected funded rank head {rankTy.getAppFn}"
  let rankArgs := rankTy.getAppArgs
  let lower := ← lvar `priorFloor
  let bounds := (← Meta.inferType lower).getAppArgs
  return mkAppN f (knownArgs ++ #[rankArgs[rankArgs.size-4]!, bounds[bounds.size-2]!,bounds.back!,
    rankArgs.back!,lower,recordedRead])


set_option maxHeartbeats 7500000 in
include machine in
/-- Evaluating the earned finite machine at a single physical scale gives precisely the
independent-copies host used by dyadic descent. All histories share its date program. -/
theorem original_funded_stage_host
    (seedWord:2*digitsNeeded s≤payloadBits) (epochWord:2*DescentPackedEpochShelves.unit G.C≤payloadBits/2)
    (edgeWord:2^j*s≤w) (seatsWord:(S).batch+2*packWidth<2^w)
    (reelAbove:dst<DescentExteriorMatrixUpdate.Calendar.earlyAt S k tail replayBase)
    (headerBelow:head<censusBase) (headerVote:head<front+extra ∨ dst<head)
    (shopCount:(dateSpec).scalar.shops=(dateHardware).hosts)
    (alive:0<(dateSpec).scalar.shops)
    (priorMetadata:(dateOut).metadataEnd dateOrigin≤earlyFloor) (one:chunks (dateHardware).groups (dateHardware).lanes=1)
    (roleEnd:roleBase+DescentTerminalRoleTables.count roleBankBits≤(dateSpec).cohortEnd censusBase)
    (layout:(dateSpec).Before censusBase paidBank actorBank wingBank peerBank (lookupPage).total (lookupPage).modulo
      dateHomes (lookupPage).boundaries)
    (paidRowsFit:∀b₀,(dateSpec).scalar.shops≤(paidBank b₀).size)
    (signedRows:∀b₀ j₀,(dateSpec).scalar.shops≤(wingBank b₀ j₀).size)
    (retainedWidth:j≤(S).groupWidth k tail (S).length+k)
    (replayPayload:(k*(S).length+1)*2^(8+(S).capGain*(S).length)≤w)
    (signedFit:DescentSignedCableCodec.width 3 256*startup.packedLanes≤w)
    (fieldsFit:startup.operandBits*startup.operandLanes≤w) (headerLow:startingHeader<startup.base)
    (sourceSpace:DescentPackedSeed.publicWords X+DescentDyadicSpan.span initialSource_≤ seedEnd_)
    (liveness:0<primitiveLanes_) (embed:payloadBits≤w) (bootRoom:initialBound_<2^w)
    (proofRate startRate degreeMax:ℕ)
    (grant:ProfiledRate.Covers G board rot rounds f g restart τ R degreeMax β payloadBits proofRate)
    (purchase:ArgumentCalendar G rot rounds f g restart τ β R driftRate degreeMax payloadBits)
    (returns:ReturnCalendar G rounds f g restart driftRate funds_ τ β ratio payloadBits)
    (receiver:ReceiverCalendar G board rot rounds f g restart τ R degreeMax β payloadBits)
    (growth:R+1≤ DescentCompiler.TerminalScale.scale depth_ driftRate) (sites:siteCount≤(2^payloadBits)^2)
    (input:p≤payloadBits) (coeff:dateDegree≤degreeMax) (original:s≤payloadBits)
    (prepaid:Geometry G S menu_ k w 0 entry_) (positiveK:0<k)
    (headerFits:initialBound_≤2^(startRate*payloadBits))
    (machineWord:(rounds+1+max proofRate startRate+2)*payloadBits≤w)
    (matcher:MatcherRoom G S k p payloadBits)
    (signed:∀i H:ℕ,i≤(S).length→2*(stage_ i H).unit≤payloadBits)
    (palette:OrdinaryBooks.PrimitiveCalendar G rot rounds f g restart τ β R degreeMax driftRate payloadBits)
    (spare:0<2^j) (observed:ObservationRoom G S payloadBits w)
    (seedDegree:(entry_).ports.venue.degree=3) (degreeRoom:maximumDegree ((S).rounds+1)+1<2^w)
    (resetWords:SnapshotWordRoom S n h k tail p f g payloadBits w)
    (capturePaid:capture+(mark_).length≤ initialBound_)
    (batchFit:(S).batch<2^w)
    (archiveEnd:front+extra≤ startingHeader) (reelData:front+extra≤replayBase)
    (below:compact+32*DescentExteriorShelf.span j rest s datePorts≤replayBase)
    (headLow:head<replayBase) (headApart:head<capture ∨ capture+(captureDates).length≤head)
    (earned:∀(x₀:extPins→Bool)(z₀:Full→Bool)(c₀:(last).Choice),candidatePrior x₀ (erased z₀)=some c₀→
      ∀din:(dateMachine).DateInputs ((dateMachine).stageStart datedFloor) w,registeredAt x₀ z₀ c₀ din→
      paidPacketsAt x₀ z₀ c₀→matrixAtSource x₀ z₀ c₀→(∀i<DescentTerminalDenseHeaderBoot.extent q p,
        (capturedAt x₀ z₀) (rom+i)=DescentTerminalDenseHeaderBoot.back w q p i)→sitePagesAt x₀ z₀ c₀)
    (signedPitch:(dateOut).venue.next.signedLanes=(S).groupCount (S).length)
    (maskRoom:(dateSpec).maskBase censusBase<2^w) (shops:0<(dateSpec).scalar.shops)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (headerRoom:(cfg).terminal.pool≤headerRows) (headersPositive:0<headerRows)
    (chipRows:(cfg).terminal.rows=K*W) (dataRoom:q*p≤w)
    (word:Nat.log 2 (NativeBranch.privateMax G S p)+1≤w)
    (slotCapacity:numSlots≤DescentDyadicSpan.span (cfg).terminal.rows)
    (hp:pcs≤2^(w+1)) (hr:regs≤2^(w+1))
    (ht:runtime+obs≤2^(CheapISA.width w+1))
    (rate:ℕ) (height:4≤payloadBits) (widthRate:w≤rate*payloadBits)
    (addr:(CheapISA.dataBase pcs regs+firstFree)+(runtime+obs)≤2^(3*payloadBits))
    (price:ℕ)
    (bill_:(4*((seedNet).cells+(seedNet).internal)+9*(rawWords*widthWord)+binsPaid*countWidth_+
      Fintype.card Full+Fintype.card extPins+
      (257*(1000*(2*(7*(rate+6))+2)*(2*4^7+1))+256*fixedISAPrice*(rate+6))*
        (pcs+regs+firstFree+fuel+obs+2^payloadBits+1)*(payloadBits+1))*2^depth_≤price*((S).copies*s)*(siteCount+2^depth_*E₀)) :
    ∃calls:ℕ,∃H:Host F cp (((S).copies*s)*P) (Sockets (List.replicate calls (CollapseOracle.tagCall payloadBits (referenceReplacement (F:=F) payloadBits cp)))),
      Agrees (independentCopies ((S).copies*s) X) (tableApprox H.width (exactValue _ H)) ∧
      hostSize H*2^depth_≤price*((S).copies*s)*(siteCount+2^depth_*E₀) := by
  have priorFloor : rankFloor≤replayBase := (Nat.le_max_left ..).trans (Nat.le_add_right ..)
  have away (i:ℕ) (_hi:i<(S).length) (bank₀:Bank) (past:(snapshots).compact i=some bank₀) :
      (bank₀).base+(bank₀).size≤capture ∨ capture+(captureDates).length≤(bank₀).base :=
    Or.inr (capturePaid.trans (RegisterTimeline.snapshotCalendar_above reset traces_ menu_ entry_ i bank₀ past))
  have funded (x₀:extPins→Bool) (z₀:Full→Bool) :=
    original_funded_ballot X G rounds restart τ β siteCount payloadBits ordinary reset branch positive
      room shorten w fit R dateDegree degreeMax lo startingHeader entry_ startup hostsEnough Z extra
      (DescentExterior.publicRows X (view x₀))
      (Sum.elim (histAt z₀) (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr))
      (DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀)
      proofRate startRate grant purchase returns receiver growth sites input coeff original prepaid positiveK
      headerFits machineWord matcher signed palette W (2^j) spare rfl seedWord sourceSpace liveness embed
      signedFit fieldsFit rfl archiveEnd headerLow bootRoom rfl observed seedDegree degreeRoom resetWords
      capture replayBase capturePaid priorFloor replayFits
  have dateReceipt := (funded (fun _=>false) (fun _=>false)).1
  have rotRole (i:ℕ) (hi:i<(S).length) : dateRotation i<roleBase :=
    (dateReceipt.matrixBefore i hi (S).length le_rfl hi).trans_le (Nat.le_max_left ..)
  have startFloor (i:ℕ) : (cursor_ 0).floor≤(cursor_ i).floor := by
    induction i with
    | zero => exact le_rfl
    | succ i ih => exact ih.trans (RegisterTimeline.selected_floor (RegisterTimeline.issued (w:=w) traces_ menu_) i (cursor_ i))
  have nonempty : 0<(S).length := Nat.mul_pos (Nat.succ_pos _) age
  have startupRole : startingHeader<roleBase :=
    ((dateReceipt.order 0 nonempty).trans_le (startFloor (S).length)).trans_le (Nat.le_max_left ..)
  have returned (x₀:extPins→Bool) (z₀:Full→Bool) (c₀:(last).Choice)
      (accepted:candidatePrior x₀ (erased z₀)=some c₀) :
      ∃din:(dateMachine).DateInputs ((dateMachine).stageStart datedFloor) w,
        registeredAt x₀ z₀ c₀ din := by
    let rankReport := hostPurchaseRank% (@original_chosen_rank_rooms) [
      F, (inferInstance : Field F), cp, P, X, G, cut, n, h, C, f, g,
      rounds, restart, τ, β, siteCount, payloadBits, ordinary, reset, branch, positive, room, shorten,
      base, width, w, fit, K, rawWords, x₀, z₀, c₀, accepted]
    have selected := rankReport.1
    have ranks := rankReport.2
    exact original_funded_mounted_registered («W»:=W) («piece»:=piece) («q»:=q)
      X G rounds restart τ β siteCount payloadBits ordinary reset branch positive room shorten w fit
      dateDegree degreeMax lo startingHeader entry_ startup hostsEnough Z extra
      (DescentExterior.publicRows X (view x₀))
      (Sum.elim (histAt z₀) (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr))
      (DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀)
      headerRows paidRows replayBase matrixAt roleBase capture proofRate startRate
      grant purchase returns receiver growth sites input coeff original prepaid positiveK headerFits
      machineWord matcher signed palette W (2^j) spare rfl seedWord sourceSpace liveness embed
      signedFit fieldsFit rfl archiveEnd headerLow bootRoom rfl observed seedDegree degreeRoom
      resetWords c₀ selected capturePaid priorFloor maskRoom shops below signedPitch ranks le_rfl
      roleMount (Nat.le_max_left ..)
  apply wide_earned_stage_host
    («roleMount»:=roleMount) («X»:=X) («G»:=G) («S»:=S) («ordinary»:=ordinary)
    («reset»:=reset) («branch»:=branch) («positive»:=positive) («room»:=room)
    («shorten»:=shorten) («base»:=base) («width»:=width) («age»:=age)
    («wFit»:=wFit) («qFit»:=qFit) («qh»:=qh) («template»:=template)
    («sitesPositive»:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows) («paidRows»:=paidRows)
    («pool»:=pool) («raw»:=raw) («payloadBits»:=payloadBits) («fit»:=fit)
    («lo»:=lo) («packWidth»:=packWidth) («board»:=board) («dateAge»:=dateAge)
    («dateDegree»:=dateDegree) («datePayload»:=datePayload) («ordinaryAt»:=ordinaryAt) («operandLanes»:=operandLanes)
    («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate) («priorAddress»:=priorAddress) («rosterBank»:=rosterBank)
    («datedFloor»:=datedFloor) («replayBase»:=replayBase) («dateTag»:=dateTag) («dateRotation»:=dateRotation)
    («snapshots»:=snapshots) («roleBase»:=roleBase) («replayRoom»:=replayRoom) («rom»:=rom)
    («other»:=other) («head»:=head) («short»:=short) («hostsEnough»:=hostsEnough)
    («startup»:=startup) («startingHeader»:=startingHeader) («datesAt»:=datesAt) («capture»:=capture)
    («countAt»:=countAt) («machine»:=machine) («censusRoom»:=censusRoom)
    rfl rfl seedWord epochWord edgeWord seatsWord reelAbove headerBelow headerVote
    shopCount alive priorMetadata one roleEnd layout paidRowsFit signedRows rankDir_ rfl rankFloor priorFloor (Nat.le_max_left ..) away
    retainedWidth replayPayload signedFit fieldsFit headerLow sourceSpace liveness embed bootRoom rfl
    (fun i=>(cursor_ i).floor) ?_ batchFit rfl rfl archiveEnd reelData below headLow headApart
    (Nat.le_max_right ..) rotRole startupRole startupRole
    (fun x₀ z₀ c₀ selected din reached packets matrixRead=>earned x₀ z₀ c₀ selected din reached packets matrixRead
      (by
        intro i hi
        apply original_funded_dense_words (X:=X) (G:=G) (ordinary:=ordinary) (reset:=reset)
          (x₀:=x₀) (z₀:=z₀) (receipt:=(funded x₀ z₀).1) (archiveEnd:=archiveEnd)
          (headerLow:=headerLow) (sourceSpace:=sourceSpace) (liveness:=liveness) (embed:=embed)
          (signedFit:=signedFit) (fieldsFit:=fieldsFit) (bootRoom:=bootRoom) (i:=i) (hi:=hi)
        all_goals assumption))
    returned romTop headerRoom headersPositive chipRows dataRoom word slotCapacity hp hr ht
    payloadBits rate height widthRate addr (referenceReplacement (F:=F) payloadBits cp)
    siteCount depth_ price bill_
  intro x₀ z₀ _ _ _ _ _
  have funding := funded x₀ z₀
  run_tac Lean.Elab.Tactic.withMainContext do
    let h := (← Lean.Meta.getLocalDeclFromUserName `funding).toExpr
    (← Lean.Elab.Tactic.getMainGoal).assign h
    Lean.Elab.Tactic.replaceMainGoal []

end
end Hierarchy.DescentSixParty.SeedNamed

-- Skip the costly local suggestion index for these large theorem types during export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun prior =>
  ["original_funded_dense_words", "original_funded_boot_dates", "original_funded_reel_price", "original_funded_stage_invoice", "original_funded_invoice_from_purchase", "original_funded_stage_host"] ++ prior

end OAI
