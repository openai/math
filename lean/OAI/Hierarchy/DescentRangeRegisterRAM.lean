import OAI.Hierarchy.DescentRangeRegisterCore
import OAI.Hierarchy.DescentReachedRangeHistory
import OAI.Hierarchy.DescentPriorResetArchive

namespace OAI
/-! # Range registers from the actual dated node archive, SIMD lane and local number -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentOperandStateBanks
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentDatedAddressBook DescentLocalArchiveOrder
open DescentDatedPriorOperand ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

/-- On either real previous archive (seed or later), the property block read by the
reset mover agrees with the registered old operand bank. -/
theorem prior_range_bank (a : PriorResetArchive) (v : DescentResetRetainedSetup.Layout)
    (x : Fin v.blocks) (i : Fin v.previousArgs) (f : Fin 3) :
    a.prior v (v.sourceID (v.operandField (page f) i) x)=
      previousBank v.previousLayout a.arguments x (DescentOperandStateBanks.page (page f) i) := by
  unfold PriorResetArchive.prior
  split
  · exact v.directory_property (v.previousChart.seedBank a.nodeBase)
      (fun pg block => previousBank v.previousLayout a.arguments block pg) (page f) i x
  · exact v.directory_property (v.previousChart.bank a.nodeBase)
      (fun pg block => previousBank v.previousLayout a.arguments block pg) (page f) i x

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
