import OAI.Computability.VPVNP.PairRefreshHookReadSupport

/-! # Source ranges for a selected refresh job at the dispatcher -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM Compression CompressorRecords DescriptorSpace PortRefresh NewSlots
open TraversalControllerInputs
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {hist : ℕ}

/-- Published row ranges in the live block layout. The dispatched tag is read
below the terminal header, like the two node cells and the level directory. -/
structure GuardLayout {n w : ℕ} (R : Site B n hist w) (pub : Fin 11 → Word w) (m : Memory w)
    (start positions blocks : ℕ)
    (prev next : Fin (BlockProgram.layout B start positions blocks).levels)
    : Prop where
  size : R.state.positions ≤ positions
  below : endAddress (BlockProgram.layout B start positions blocks) ≤ (TerminalLink.header pub).val
  headerFit : (TerminalLink.header pub).val + 32 ≤ 2 ^ w
  oldHead : (levelHead pub m R.level).val =
    levelStart (BlockProgram.layout B start positions blocks) prev
  newHead : (levelHead pub m (R.level + 1)).val =
    levelStart (BlockProgram.layout B start positions blocks) next
  scratch : R.start = arrayBase (BlockProgram.layout B start positions blocks) prev
  oldCols : R.prev = packedIncidence (BlockProgram.layout B start positions blocks) w prev
    (R.state.positions * 2 ^ S.portExponent)
  newCols : R.next = packedIncidence (BlockProgram.layout B start positions blocks) w next
    (R.nextState.positions * 2 ^ S.degreeExponent 0)
  levels : ∀ i, R.level + 1 ≤ i → i ≤ R.level + 1 + R.later →
    (levelHead pub m i + 14).val < (TerminalLink.header pub).val
  parentBefore : R.parent + 1 < (TerminalLink.header pub).val
  listBefore : R.listHead < (TerminalLink.header pub).val
  tagBefore : (R.roleOffset + word R.parent).val < (TerminalLink.header pub).val

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
