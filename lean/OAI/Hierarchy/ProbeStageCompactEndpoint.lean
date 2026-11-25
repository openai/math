import OAI.Hierarchy.ProbeStageCompactEndpointSetup
import OAI.Hierarchy.ProbeStageCompactEndpointScatter

namespace OAI
/-! # Exact native endpoint image and actual saturation charge at the fixed row -/
namespace Hierarchy.ProbeStage.Native.Compact
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section

theorem endpoint_model {h d : ℕ} (hd : 1≤d) (hh : 4≤h) (j : Fin (rounds d)) (i : Fin (2^h))
    (l : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) (r : ℕ)
    (m n : Memory (ramWidth h d)) (saved : Fin 8→Word (ramWidth h d))
    (rel : Model j i saved m n) (src : SideSource j i l b c r m) :
    let stage := Record.side (recordAdvice h d j) (row h) (recordScratch h d j) l
    Model j i saved (RankUpdate.image (physicalSide j i l) m) (RankUpdate.image stage n) ∧
      RankUpdate.occurrenceCount stage n=RankUpdate.occurrenceCount (physicalSide j i l) m :=
  scatter_model j i hd hh l b c r m n saved src (endpoint_prepared j i hd hh l b c r m n saved rel src)

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
