import OAI.Computability.VPVNP.PairVertexFrameData

/-! # Private cells updated by a selected shrinking row -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM PrivateRAM DFS TreeDecode NodeArguments LeafSourceLoad
open scoped Fin.CommRing

variable {w n h : ℕ} {L : Type}

/-- The scratch-cell laws of a successful body read. The child scan writes
the argument arena, and the resident scans add the selected label counts. -/
structure RowUpdate (R : LeafArena.Regions) (order : L ≃ Fin h) (data : Fin 10 → Word w)
    (offset : Word w) (vals : Static 34 → Word w) (s : Scratch w n) (job : VisitPath w n)
    (children : List Packet) (exponent : L → ℕ) : Prop where
  enabled_eq : ∀ t, job.enabled t → t = s
  frame : VertexFrameData R data offset vals (job.update s)
  arguments : ∀ a : ℕ, n ≤ a → a < R.histBase →
    rawScratch (job.update s) (a : Word w) =
      rawScratch (writePackets R.arguments children s) (a : Word w)
  counters : ∀ l, let a : Word w := (R.histBase + (order l).val : ℕ)
    rawScratch (job.update s) a = rawScratch s a + (exponent l : Word w)

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
