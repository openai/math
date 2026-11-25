import OAI.Hierarchy.TraceReceiverElectedRoot
import OAI.Hierarchy.TraceReceiverRegisteredGeometry

namespace OAI
/-! # Site ordinals and external origins on the actual selected terminal layer -/

namespace Hierarchy.TraceReceiverElectedSites
open ThreeFlat Diagonal PhysicalStage NavigationPass HistoryContraction NavigationDirectory
open NativeNavigation NodePublication RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.HistoryNodeDirectory
open RAM.HistoryNodeDirectory.Selected RAM.HistoryStageBody.Physical RAM.HistoryInitialSeed
open HistoryStageSetup HistoryPartyBatchExec TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM GridThrough FactorPinIntervals
open GridRegisteredSetting HistorySelectedReceiverLoop TraceReceiverLeafSetup
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
local notation "last" => ((r).finalArchive z.1 C O j.path).1
local notation "total" => (last).first+(last).count


/-- The physical site tied to a selected S17 ordinal keeps exactly that ordinal in
the terminal layer's incidence table. -/
theorem terminal_ordinal (f : Fin (I.roots z.1)) :
    (((r).endSites z.1 C O j.path).ord (I.terminalSite z.1 f)).val=f.val := by
  have hit:=TraceReceiverElectedCache.selected_index I l j f
  rw [(r).archivePlanIndex_physical] at hit
  change ((r).endSites z.1 C O j.path).layer.first+
    (((r).endSites z.1 C O j.path).ord (I.terminalSite z.1 f)).val=(last).first+f.val at hit
  rw [congrArg (fun row => row.first) ((r).endSites_layer z.1 C O j.path)] at hit
  exact Nat.add_left_cancel hit

/-- The selected root's complete S44 ID is the stage base plus its original factor ordinal. -/
theorem terminal_id (f : Fin (I.roots z.1)) :
    ((r).endSites z.1 C O j.path).id (I.terminalSite z.1 f)=(last).first+f.val := by
  exact congrArg₂ Nat.add (congrArg (fun row => row.first) ((r).endSites_layer z.1 C O j.path))
    (terminal_ordinal I l j f)

end
end Hierarchy.TraceReceiverElectedSites

namespace Hierarchy.TraceReceiverElectedSites
open ThreeFlat Diagonal PhysicalStage Diagonal.TraceBitHeader
open GridRegisteredSetting HistoryContraction Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] [Fintype F] {W pc regs slots S addr fuel k low : ℕ}
variable (I : RunData F W pc regs slots S addr fuel k low) (h : I.run.plan.History)
local notation "r" => I.run
local notation "L" => TraceReceiverSeedWords.wordsLayout I.machine I.fit I.field I.state I.block I.axesFit
local notation "J" => I.issuedRegister.1.steps
local notation "src" => TraceReceiverSeedWords.source I.machine I.fit I.field I.state

theorem terminal_ordered : ((r).terminalLayer h).state.OrderedHalves (I.terminalWords h) :=
  (r).endWords_halves h J L (TraceReceiverSeedWords.words_ordered I.machine I.fit I.field I.state I.block I.axesFit)

theorem terminal_heq (f : Fin (I.roots h)) :
    HEq (I.terminalSite h f) ((I.ordinal h).symm f) :=
  cast_heq _ _

theorem source_site_iff (x : PairedCursor.Site (k+1)) (f : Fin (I.roots h)) :
    HEq ((r).plan.destination h x) (I.terminalSite h f) ↔ I.ordinal h ((r).plan.destination h x)=f := by
  constructor
  · intro physical
    have eq:=eq_of_heq (physical.trans (terminal_heq I h f))
    rw [eq,Equiv.apply_symm_apply]
  · intro eq
    have same : (r).plan.destination h x=(I.ordinal h).symm f :=
      (I.ordinal h).injective (eq.trans ((I.ordinal h).apply_symm_apply f).symm)
    exact (heq_of_eq same).trans (terminal_heq I h f).symm

theorem original_site_iff (a : Fin S) (f : Fin (I.roots h)) :
    HEq ((r).plan.destination h (PairedCursor.owner (TraceDistribution.layout I.machine I.fit I.field I.state) a))
      (I.terminalSite h f) ↔ I.origin h a=f :=
  source_site_iff I h _ f

theorem original_owner (f : Fin (I.roots h)) (pin : Fin ((I.terminalWords h).ext (I.terminalSite h f))) :
    let a:=(r).extAncestor h J L (I.terminalSite h f) pin
    I.origin h (src a.1 a.2)=f := by
  intro a
  apply (original_site_iff I h _ f).1
  have home := TraceReceiverSeedWords.source_owner I.machine I.fit I.field I.state a.1 a.2
  exact (heq_of_eq (congrArg ((r).plan.destination h) home)).trans
    ((r).extAncestor_destination h J L (I.terminalSite h f) pin)

end
end Hierarchy.TraceReceiverElectedSites

end OAI
