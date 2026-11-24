import OAI.Computability.VPVNP.PairTerminalReachableFrame
import OAI.Computability.VPVNP.PairSimulationSharedBitControl
import OAI.Computability.VPVNP.PairSimulationVertexControlFrame
import OAI.Computability.VPVNP.LiveTerminalReachableFrame

/-!
# Reachable frames of the actual terminal bit and vertex workers

The bit cursor preserves every word outside its wire bank and controller.
A finishing bit prefix supplies a full assignment, which selects the
genuine vertex calls. At each active ordinal the vertex worker writes only
the histogram, even if another ordinal later has no accepting choice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram
open BurstRAM LiveProgram CompressorRecords SourceTransport TerminalLink VertexImage
open scoped Fin.CommRing

variable {w cap n g base grammar : ℕ} (F : DescriptorSpace.Shape) (limit : ℕ)
    {geometry rootFields leaf shrink refresh : VertexImage.Segment} (pub : Fin 11 → Word w)
    (m : Memory w)

local notation "segments₀" => VertexImage.segments geometry rootFields leaf shrink refresh
local notation "workers₀" => TerminalProgram.workers F limit segments₀

/-- This statement concerns every physically reached boundary in the entire
five-stage fixed instruction table, including successful partial histories.
The data in `active` classify one original site burst and its native effects. -/
theorem preservesCell {I : Type*} (q : QuietPrefix workers₀ pub cap m) (arc : I ≃ q.BitPaths)
    (word : ℕ) (wide : 32 ≤ 2^w) (clock : 26 ≤ cap)
    (first : ReplayFrame word m q.reportList)
    (entered : (Entry.resume TerminalLink.Stage.sharedBits (0 : Word w)).Valid (header pub) q.traversalRows.val.memory)
    {lo count : ℕ} (src : Memory w) (layout : FinalBits.Worker.Layout pub src lo count)
    (room : (header pub).val+32 ≤ 2^w) (agree : Agree (workerCell (header pub)) src q.traversalRows.val.memory)
    (wire : word < lo ∨ lo+count ≤ word)
    (cell : workerCell (header pub) word)
    (D : I → IndexedSites n g) (ref : I → Memory w)
    (active : ∀ i, ActiveCalls (D i) ((VertexImage.template segments₀).instantiate w pub).program cap base grammar
      (VertexFrame.Linked (header pub) base grammar g (ref i)))
    (stored : ∀ i mem, VertexFrame.Linked (header pub) base grammar g (ref i) n mem →
      mem (TerminalSiteStart.headerWord pub+7).val = (n : Word w))
    (initial : ∀ i, VertexFrame.Linked (header pub) base grammar g (ref i) 0 (arc i).val.memory)
    (counter : word < base+grammar ∨ base+grammar+g ≤ word) :
    BurstRAM.PreservesCell (TerminalLink.program workers₀ pub) cap 0 m word := by
  apply q.preservesCell word wide clock first entered
  · exact FinalBits.Worker.control workers₀ rfl cap word src _ layout room agree wire cell
  · intro b
    let i := arc.symm b
    have h : b = arc i := (arc.apply_symm_apply b).symm
    rw [h]
    apply VertexImage.ordinalWorkerControl F limit (ref i) (arc i).val.memory word (active i)
    · exact template_closes (pub := pub) (by omega : 15 ≤ cap) (stored i)
    · exact counter
    · exact cell
    · exact initial i

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
