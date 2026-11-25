import OAI.Hierarchy.TraceReceiverJournalPublication
import OAI.Hierarchy.TraceReceiverSelectedMaps
import OAI.Hierarchy.TraceReceiverElectedSites

namespace OAI
/-! # The executable terminal map source of the installed receiving tick -/
namespace Hierarchy.TraceReceiverJournalMemory
open ThreeFlat Diagonal PhysicalStage NavigationPass HistoryContraction NavigationDirectory
open NativeNavigation NodePublication RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.HistoryNodeDirectory
open RAM.HistoryNodeDirectory.Selected RAM.HistoryStageBody.Physical RAM.HistoryInitialSeed
open HistoryStageSetup HistoryPartyBatchExec TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM GridThrough FactorPinIntervals
open TraceReceiverElectedCache GridRegisteredSetting HistorySelectedReceiverLoop TraceReceiverLeafSetup
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
variable {F : Type} [Field F] [Fintype F] {w pc regs slots S addr fuel axes : ℕ}
variable (I : RunData F (64*w) pc regs slots S addr fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "u" => TraceAdmission.receiverAge w
local notation "W" => (64*w)
local notation "B" => I.block
local notation "M" => I.machine
local notation "ft" => I.fit
local notation "hF" => I.field
local notation "st" => I.state
local notation "hk" => I.axesFit
local notation "d" => (axes+1)+(w/2)
local notation "G" => TraceStaticRow.gateTable hF (ft).width (ft).labels addr fuel st regs slots d
local notation "O" => (GridReceiverDirectory.archive I l).cursorSeedSites B hk (w/2) (1+(d+d)) (G).cells rfl rfl
local notation "a" => GridReceiverDirectory.archive I l
local notation "dn" => GridReceiverDirectory.native I l
local notation "stop" => finish (a).K (dn).stages (a).cursor
local notation "b" => (dn).node.banks
local notation "phase" => ((B).repeat I.passes).length
local notation "P" => GridReceiverBanks.pinPlan I l
local notation "C" => I.issuedCharges
local notation "r" => I.run
local notation "K" => (B).localCoefficient*(W+1)^3
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
local notation "L" => TraceReceiverSeedWords.wordsLayout M ft hF st B hk
local notation "trees" => TraceReceiverSeedWords.forest M ft hF st B hk
local notation "J" => (TraceReceiverCofinalPrices.assembly I).steps
local notation "T" => (l.sideMinusOne+1)^(l.dimension+1)*l.copies
local notation "full" => (2^(axes+1):ℕ)
local notation "dim" => (l.dimension+1)
local notation "g" => GridPinArena.slab w
local notation "radix" => (20*(w+1)+2)^(dim+2)
local notation "table" => TraceReceiverTablesMount.output I
local notation "fees" => I.issuedUnit w l.degree l.stageRate l.rootRate

variable {geom : GridReceiverDirectory.ElectionRoom I l} {safe : GridNativeDispatch.WordRoom I}
    {z : I.trace} {sel : Fin (l.selectorCap+1)→Bool} {t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies)}
    {input origin elected : Memory (64*w)}
    (j : TraceReceiverElectedJournal.Journal I l geom safe z sel t input origin elected)
    (Q : FactorPinIntervals.Layout (Cell (l.dimension+1) l.sideMinusOne×Fin l.copies) S (I.roots z.1) l.pinWidth)
local notation "last" => ((r).finalArchive z.1 C O j.path).1
local notation "total" => (last).first+(last).count
local notation "costs" => I.costs (GridNativeImage.resources I l) z.1 l.dimension l.sideMinusOne l.bank C fees
local notation "price" => (fun i : Fin (last).count => costs (i.cast j.card.symm))
local notation "owners" => (fun i : Fin (last).count => ((FactorAllocation.owner geom.teams_pos w price i).val:Word W))
local notation "chron" => (r).archiveDirectory z.1 C O j.path b (numeric j.saved) j.stored rfl (last).first (last).count rfl rfl
local notation "D" => TraceReceiverOwnerMount.directory chron owners (t.val:Word W)
local notation "node" => (r).archiveNode z.1 J L trees C O j.path rfl
local notation "ptr" => TraceReceiverOriginal.pin M ft hF st Q
local notation "val" => (fun i : Fin total=>NodeValue.ofSite (node i) ptr (streamAt u (O).layer.count i.val)
    (endsAt u (O).layer.count i.val))
local notation "entry" => TraceReceiverDescendantExecution.entry I (last).first (last).count P elected

local notation "ids" => FactorAllocation.factors w costs (List.finRange (I.roots z.1)) t
local notation "selector" => GridReceiverTickDirectory.banks w u
local notation "args" => GridStructuralHeader.parameters B (axes+1) I.passes l.selectorCap M ft hF st 0 (gateBase I)
local notation "tables" => TraceReceiverTablesMount.output I elected
local notation "finalSites" => (r).endSites z.1 C O j.path
local notation "oldPages" => (fun pos : ℕ=>(TickWorkspace.base u 20≤pos ∧ pos<TickWorkspace.base u 38) ∨
  (TickWorkspace.base u 43≤pos ∧ pos<TickWorkspace.base u 45))

open RAM.TickTerminalRoot
local notation "x" => (a).terminal (dn).stages (dn).edges W
local notation "X" => ((r).terminalLayer z.1).state
local notation "V" => HistoryStageBody.Physical.volume u
local notation "sector" => GridReceiverBanks.base w
local notation "value" => selectedValue I l j Q
local notation "site" => I.terminalSite z.1

local notation "sites" => (fun i : Fin (ids).length=>site (ids[i.val]))
local notation "vals" => (fun i : Fin (ids).length=>value (ids[i.val]))
local notation "td" => GridReceiverBanks.tasks w
local notation "rootBase" => TickWorkspace.base u 9

variable (ok : TraceReceiverInstalledScalars.Ready I l j) (afterDesc restored : Memory (64*w))
    (done : published I l j Q afterDesc)
    (second : GridReceiverTickDirectory.Ticked (GridReceiverTickDirectory.banks w (TraceAdmission.receiverAge w))
      (FactorAllocation.factors w (I.costs (GridNativeImage.resources I l) z.1 l.dimension l.sideMinusOne l.bank
        I.issuedCharges (I.issuedUnit w l.degree l.stageRate l.rootRate)) (List.finRange (I.roots z.1)) t)
      (t.val:Word (64*w)) afterDesc restored)
    (R : GridPinArena.Scalars (64*w) (GridReceiverBanks.pinPlan I l) S (2^(axes+1))
      ((20*(w+1)+2)^((l.dimension+1)+2)) (GridPinArena.slab w))
    (small : GridPinArena.Small w (GridReceiverBanks.pinPlan I l) S (2^(axes+1))
      ((GridReceiverDirectory.native I l).stages.length*(2^(axes+1))) ((20*(w+1)+2)^((l.dimension+1)+2)))
    (source : ∀ k,Q.origin k=I.origin z.1 k)
    (textFit : SelfAdvice.textSize (64*w) pc slots≤w^2) (self : Fin (w^2)→Bool) (inBit : ℕ→Bool)
    (header : (GridReceiverHeader.header _ textFit self (t.val:Word (64*w))
      (GridStructuralHeader.parameters I.block (axes+1) I.passes l.selectorCap I.machine I.fit I.field I.state 0 (gateBase I)) sel).length≤l.pinWidth)
    (read : ∀ k : Fin (GridReceiverHeader.header _ textFit self (t.val:Word (64*w))
      (GridStructuralHeader.parameters I.block (axes+1) I.passes l.selectorCap I.machine I.fit I.field I.state 0 (gateBase I)) sel).length,
      inBit k.val=(GridReceiverHeader.header _ textFit self (t.val:Word (64*w))
      (GridStructuralHeader.parameters I.block (axes+1) I.passes l.selectorCap I.machine I.fit I.field I.state 0 (gateBase I)) sel)[k.val])
    (frame : ∀ address,address<2+l.pinWidth → elected address=TickMountedPins.memory (w:=(64*w)) (fun k : Fin l.pinWidth=>inBit k.val) address)
    (terminals : (GridReceiverDirectory.archive I l).TerminalRoom (GridReceiverDirectory.native I l).stages (GridReceiverDirectory.native I l).edges (64*w))
    (selectorRoom : GridSelector.Room I.run.plan (GridNativeDispatch.actualTable I safe).codes
      (GridPhysicalSelector.bits I.run) l.selectorCap)
    (paid : ∀ f,I.issuedTreeWork z.1 l.degree l.stageRate l.rootRate f ≤
      I.work z.1 I.issuedCharges (I.issuedUnit w l.degree l.stageRate l.rootRate) f)
    (degree : 2*(I.run.terminalLayer z.1).degree≤(HistoryStageBody.Physical.volume (TraceAdmission.receiverAge w)))
    {suffix : ℕ} (suffixIn : suffix≤l.pinWidth)

include I l j Q ok afterDesc restored done second R small source textFit self inBit header read frame terminals selectorRoom paid degree suffixIn in
private theorem selectedPublication (i : Fin (ids).length) :
    TraceReceiverRootRetain.Publication u sector l.pinWidth suffix (O).layer.count
      (TickWorkspace.base u 20) (stop).heap restored j.mid X (I.terminalWords z.1) finalSites (sites i)
      (vals i) HistoryRefreshEmitter.tag b x i (fun k=>(vals k).net.cells) := by
  obtain ⟨tablesKept,ownersKept⟩:=mounted_tables I l j Q ok R small source textFit self inBit header read frame
  exact publication I l j Q ok afterDesc restored done second R small.bits tablesKept ownersKept
    terminals selectorRoom paid degree suffixIn i

include j ok in
private theorem selectedCount : (ids).length≤2^(3*w/5) := by
  have bounded : (ids).length≤I.roots z.1:=by
    simpa using (FactorAllocation.factors_nodup geom.teams_pos w costs t).length_le_card
  have length:=j.card
  have totalBound:=ok.bound
  omega

set_option maxHeartbeats 2000000 in
include I l j Q ok afterDesc restored done second R small source textFit self inBit header read frame terminals selectorRoom paid degree suffixIn in
/-- All five mounted S18 words, each of the installed five-word tasks,
and the exact original reads of the native scan on this receiving tick. -/
theorem selectedInputs :
    TraceReceiverTasks.SelectedInputFacts selector td ids (TickWorkspace.base u 18+1)
      (GridReceiverBanks.limit w) (GridReceiverBanks.width w) (finalSites).layer.first
      (TraceReceiverForward.columns X (I.terminalWords z.1) sites vals) restored rootBase l.pinWidth := by
  have big:=ok.big
  have cap:=selectedCount I l j ok
  have selectedPrice:=TraceReceiverForward.columns_paid X (I.terminalWords z.1) ids sites vals
    (fun i=>(physical_width I l j Q (ids[i.val])).2)
    (fun i=>selected_budget I l j Q (ids[i.val]) l.degree l.stageRate l.rootRate (paid _) (ok.paid _))
  exact TraceReceiverForward.selected_facts X (I.terminalWords z.1) finalSites ids sites vals
    HistoryRefreshEmitter.tag b x restored j.mid rootBase (O).layer.count (TickWorkspace.base u 20) (stop).heap
    afterDesc (t.val:Word W) second (first_word I l j Q ok afterDesc restored done second)
    (fun i=>(chosenOrdinal I l j (ids[i.val])).2) (by omega) (TraceAdmission.receiverAge_chart w big).2 cap selectedPrice
    (selectedPublication I l j Q ok afterDesc restored done second R small source textFit self inBit header read frame terminals selectorRoom paid degree suffixIn)

set_option maxHeartbeats 2000000 in
include I l j Q ok afterDesc restored done second R small source textFit self inBit header read frame terminals selectorRoom paid degree suffixIn in
/-- The chronological root loop obtained from the actual authenticated archive,
election, compiled forest, installed tables and wire-prefix image. -/
def selectedSource : TraceReceiverForward.Source F (Fin S→Bool) w u l.pinWidth suffix (ids).length
    ((r).terminalLayer z.1).degree ((r).terminalLayer z.1).lanes := by
  have big:=ok.big
  have wires:=j.wires I l geom safe z sel t input origin elected ok.big terminals selectorRoom
  exact TraceReceiverForward.Source.ofSelected X (I.terminalWords z.1) finalSites ids sites vals
    HistoryRefreshEmitter.tag b x restored j.mid rootBase (O).layer.count (TickWorkspace.base u 20) (stop).heap
    (TraceReceiverElectedSites.terminal_ordered I z.1) (fun i=>(chosenOrdinal I l j (ids[i.val])).2)
    (selectedInputs I l j Q ok afterDesc restored done second R small source textFit self inBit header read frame terminals selectorRoom paid degree suffixIn) (by omega) (TraceAdmission.receiverAge_chart w big).2
    (selectedCount I l j ok) (margins I l j ok).2 (wires.stop.trans (Nat.sub_le ..))
    (selectedPublication I l j Q ok afterDesc restored done second R small source textFit self inBit header read frame terminals selectorRoom paid degree suffixIn)

end
end Hierarchy.TraceReceiverJournalMemory

end OAI
