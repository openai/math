import OAI.Hierarchy.GridReceiverSpendingSums
import OAI.Hierarchy.TraceReceiverTerminalExecution
import OAI.Hierarchy.TraceReceiverFullRate

namespace OAI
/-! # Exact cost accounting for the native terminal writer and its gather -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM
open TraceReceiverTasks TraceFactorReceiver TraceFactorReceiver.Gather
open scoped BigOperators

variable {W n : ℕ}

/-- Memory at entry to the chronological terminal map loop. -/
def mapInput (D : Layout) (A : TickTerminalRoot.Arena) (count cap : ℕ)
    (width : Fin 3 → ℕ) (n : ℕ) (m : Memory W) :=
  beforeImage D count cap width n (TraceAdmission.Resources.mounted D.parent [A.metadata,A.physicalPins,0,0] m)

/-- The decoded work of the selected S13 root at the actual map-loop memory. -/
def rootClock (D : Layout) (A : TickTerminalRoot.Arena) (count cap header : ℕ)
    (width : Fin 3 → ℕ) (dst len : ℕ → ℕ) (n : ℕ) (m : Memory W) (i : Fin n) : ℕ :=
  nativeRootCost A D.tasks header dst len (mapInput D A count cap width n m) i.val

/-- Restore forward root order after the native countdown. The constant pays the
parent mount, map header, range seed, command header and final cursor store. -/
theorem terminalClock_le (D : Layout) (A : TickTerminalRoot.Arena) (count cap header commands cursor : ℕ)
    (width : Fin 3 → ℕ) (dst len : ℕ → ℕ) (n : ℕ) (m : Memory W) :
    TraceReceiverProgram.terminalClock D A count cap header commands cursor width dst len n m ≤
      (4226+before_clock 0) + ∑ i : Fin n,
        (7224+rootClock D A count cap header width dst len n m i+(perRoot+22*len i.val)) := by
  let ini := mapInput D A count cap width n m
  let cost := nativeRootCost A D.tasks header dst len ini
  have counted := maps_clock A D.tasks header dst len ini n
  change before_clock n + TraceReceiverProgram.mapClock D A count cap header width dst len n m =
    before_clock 0+4+perRoot*n+(∑ i ∈ Finset.range n, cost i)+22*(∑ i ∈ Finset.range n, len i) at counted
  have priced := Cursor.cost W cursor commands count
  change _ ≤ (4226+before_clock 0)+∑ i : Fin n, (7224+cost i.val+(perRoot+22*len i.val))
  rw [terminal_root_sum]
  exact writer_headers counted priced

end Hierarchy.GridChosenReceiver
end

end OAI
