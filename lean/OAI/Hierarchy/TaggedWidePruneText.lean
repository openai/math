import OAI.Hierarchy.TaggedWideInstalledLayout
import OAI.Hierarchy.ProtocolRAMPruneText

namespace OAI
/-! # Fixed pruning code on the shared native parent format -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Tagged
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
  (dated : WideCPU.Dated (events v.mesh).length)

theorem wide_installed_prune_text :
    let l:=v.wideInstalledLayout x m ell short u δ ξ unitCost dated
    let b:=BoughtSockets.Public.maxMetric v.radius
    Native.text (SumScores.procedure (Native.wordBits x.h (2^v.W) Native.copies)
      l.pruneScratch l.pruneRows l.threshold l.prune)=87+4*(47+20*b+9*b*(b+1)) := by
  intro l b
  exact PruneFlag.program_text ..

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
