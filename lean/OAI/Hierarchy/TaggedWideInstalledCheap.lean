import OAI.Hierarchy.ProbeFixedWideCountedPrefix
import OAI.Hierarchy.TaggedWideProgramRates
import OAI.Hierarchy.TaggedWideInstalledLayout
import OAI.Hierarchy.ProbeFixedWideTerminalText

namespace OAI
/-! # Admissible instruction set of the two authentic installed controllers -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Tagged
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
  (dated : WideCPU.Dated (events v.mesh).length)

theorem wide_installed_cheap :
    let l:=v.wideInstalledLayout x m ell short u δ ξ unitCost dated
    let progs:=v.widePrograms x.h x.w v.maxBits l
    CheapCode progs.1 ∧ CheapCode progs.2 := by
  intro l progs
  let R:=v.wideInstalledRoot x
  let S:=v.wideInstalledSize x m ell unitCost dated
  have inverseCheap : CheapCode (TagInverse.program (Native.wordBits x.h (2^v.W) Native.copies) x.h l.tagScratch) :=
    TagInverse.cheap _ _ _
  constructor
  · exact cheap_seq inverseCheap (Boot.compact_program_cheap _ _)
  · exact cheap_seq inverseCheap (l.finish_cheap _ _
      (v.wide_counted_cheap x.h x.w v.maxBits)
      (v.wide_terminal_cheap x.h x.w v.maxBits (dated.romEnd R) (dated.workEnd S)))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
