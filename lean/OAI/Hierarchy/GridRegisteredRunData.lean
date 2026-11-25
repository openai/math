import OAI.Hierarchy.PhysicalTracePlan
import OAI.ThreeFlat.Diagonal.PhysicalRunRootNumber
import OAI.Hierarchy.TraceReceiverSeedDimensions
import OAI.Hierarchy.TraceReceiverPublishedWork

namespace OAI
/-! # The real native machine and the work of its numbered terminal sites -/

noncomputable section
namespace Hierarchy.GridRegisteredSetting
open ThreeFlat Diagonal Diagonal.PhysicalStage
open TraceDistribution Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F]

/-- The very machine passed to the native compressor and its installed block. -/
structure RunData (F : Type) [Field F] [Fintype F] (W pc regs words S base fuel axes low : ℕ) where
  machine : Machine W pc regs words
  fit : NativeTrace.Fits machine S base ((axes+1)+low) fuel
  field : Fintype.card F ≤ 2^W
  state : Word W
  block : Block F
  axesFit : 2 ≤ axes+1
  passes : ℕ
  passesFit : block.blockCharge*passes ≤ axes+1

namespace RunData
variable {W pc regs words S base fuel axes low : ℕ}
variable (D : RunData F W pc regs words S base fuel axes low)

abbrev run := Physical.nativeRun D.block D.axesFit D.machine D.fit D.field D.state D.passes D.passesFit
abbrev roots (h : D.run.plan.History) := Fintype.card (D.run.plan.finish h).Site
abbrev ordinal (h : D.run.plan.History) := D.run.terminalOrderEquiv h
def work (h : D.run.plan.History) (C : D.run.Charges) (unit : ℕ) (i : Fin (D.roots h)) : ℕ :=
  Physical.publishedWork D.run h C
    (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit) unit ((D.ordinal h).symm i)

/-- Numbering the terminal sites for the registered table preserves the whole work column. -/
theorem work_sum (h : D.run.plan.History) (C : D.run.Charges) (unit : ℕ) :
    (∑ i,D.work h C unit i)=unit*D.run.rootTotal h C
      (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit) := by
  let start := TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit
  exact ((D.ordinal h).symm.sum_comp (Physical.publishedWork D.run h C start unit)).trans
    (Physical.publishedWork_sum D.run h C start unit)


end RunData
end Hierarchy.GridRegisteredSetting
end

end OAI
