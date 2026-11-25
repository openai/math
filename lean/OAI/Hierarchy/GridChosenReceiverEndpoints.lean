import OAI.Hierarchy.GridChosenReceiverWires
import OAI.Hierarchy.TraceReceiverElectedRoot
import OAI.ThreeFlat.RAM.TickTerminalRootGeometry

namespace OAI
/-! # Terminal external pin addresses from their registered S13 origins -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open TraceAdmission GridScale GridThrough GridRegisteredSetting GridInstalledEvaluator GridReceiverDirectory GridPhysicalCompiler
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}
variable {blk : Block F} {m A w degree stageRate rootRate tariff power : ℕ}
variable {v : TickSelection F (m+1) A w Q loss} (I : Installed blk m A w degree stageRate rootRate v)
variable (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I tariff power)
set_option quotPrecheck false
local notation "l" => layout m A w (overhead Q loss w) v.copies degree stageRate rootRate
local notation "D" => I.D
local notation "W" => (64*w)
local notation "U" => TraceReceiverSeedWords.wordsLayout (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
local notation "trees" => TraceReceiverSeedWords.forest (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
variable (geom : ElectionRoom I.D (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate))
    (recv : Machine (64*w) (GridDescription.capacity w) (GridDescription.capacity w) (GridDescription.capacity w))
    (safe : GridNativeDispatch.WordRoom I.D)
variable (z : I.D.trace)
local notation "P" => streamLayout I R geom recv safe z
local notation "r" => (D).run
local notation "words" => (r).endWords z.1 (receiverAssembly I).steps U
local notation "site" => ((D).ordinal z.1).symm
local notation "dir" => GridReceiverDirectory.native D l
local notation "finalDirectory" => (dir).archive.terminal (dir).stages (dir).edges W

/-- The receiver's RAM arena begins its shared-bit suffix exactly two words
after the corresponding bit on the compact tick input. -/
theorem arena_eq :
    GridReceiverBanks.arena D l = TickTerminalRoot.mounted (TraceAdmission.receiverAge w) (l).pinWidth
      (2+wireSuffix I safe z) (finalDirectory).prefixBase := by
  have start := GridReceiverBanks.suffix_address D l safe z.1
  change (GridReceiverBanks.arena D l).wireStart =
    GridStructuralHeader.receiverPhase w (l).receiverText (GridNativeImage.parameterCount D l)+1+
      ((D).run.plan.write (GridNativeDispatch.actualTable D safe).codes z.1).length at start
  apply congrArg (fun n=>TickTerminalRoot.mounted (TraceAdmission.receiverAge w) (l).pinWidth n (finalDirectory).prefixBase)
  exact start.trans (by unfold GridStructuralHeader.receiverPhase wireSuffix; omega)

variable {sel : Fin ((layout m A w (overhead Q loss w) v.copies degree stageRate rootRate).selectorCap+1)→Bool}
    {tick : Fin (((layout m A w (overhead Q loss w) v.copies degree stageRate rootRate).sideMinusOne+1)^
      ((layout m A w (overhead Q loss w) v.copies degree stageRate rootRate).dimension+1)*v.copies)}
    {input origin elected : Memory (64*w)}
    (j : TraceReceiverElectedJournal.Journal I.D (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate)
      geom safe z sel tick input origin elected)
local notation "valueAt" => (TraceReceiverElectedCache.selectedValue D l j P)

private theorem ofFn_at_cast {α : Type*} {a b : ℕ} (f : Fin a→α) (g : Fin b→α)
    (sizes : a=b) (rows : List.ofFn f=List.ofFn g) (i : Fin b) :
    f (i.cast sizes.symm)=g i := by
  subst b
  exact congrFun (List.ofFn_injective rows) i

/-- The endpoint stored by the selected tree is the scheduled input pin of
its chronological external ancestor, with the two literals at words 0 and 1. -/
theorem slotEndpoint_at_value (f : Fin ((D).roots z.1)) (u : ((r).terminalLayer z.1).state.Site)
    (same : HEq u (site f)) (external : (valueAt f).external=(words).ext u)
    (k : Fin ((words).ext u)) :
    (valueAt f).endpoint (k.cast external.symm)=2+(slotEndpoint I R geom recv safe z u k).val := by
  have root : u=(r).physicalTerminal z.1 (site f) := by
    apply eq_of_heq
    exact same.trans (cast_heq (congrArg Diagonal.HistoryContraction.Shape.Site ((r).terminalLayer_shape z.1)).symm (site f)).symm
  subst u
  have origins := (r).archivePlanExternal z.1 (receiverAssembly I).steps U trees (D).issuedCharges
    _ j.path rfl (site f)
  exact congrArg (TraceReceiverOriginal.pin (D).machine (D).fit (D).field (D).state P)
    (ofFn_at_cast _ _ external origins.2 k)

end Hierarchy.GridChosenReceiver

end
end OAI
