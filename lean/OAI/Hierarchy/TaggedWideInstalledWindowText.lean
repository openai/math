import OAI.Hierarchy.TaggedWideInstalledLayout
import OAI.Hierarchy.ProtocolRAMFrozenWindowText
import OAI.Hierarchy.TaggedWideProgramRates
import OAI.Hierarchy.TaggedWidePruneText

namespace OAI
/-! # Installed format modules contribute a fixed amount of native code per width class -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Tagged
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
  (dated : WideCPU.Dated (events v.mesh).length)
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies

theorem wide_installed_window_text :
    (∑i,Native.text ((l).banks W i))=(m+1)*5450 := by
  have row (i : Fin (m+1)) : Native.text ((l).banks W i)=5450 := by
    change Native.text (((l).windows i).phase W ((l).windowBase i) ((l).inputs i))=_
    rw [ProtocolRAMFrozenWindow.Format.phase_text]
    rfl
  simp only [row,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

/-- The only remaining site-dependent text is the instruction table of the finite dated
scatters. Each full purchased format pass is a fixed 5,450 native code resources. -/
theorem wide_installed_second_text :
    let pfx:=v.wideCountedPrefix x.h x.w v.maxBits
    let last:=(v.wideWidthLayout x.h x.w (v.widePaidSlices x.h x.w v.maxBits)).bank (events v.mesh).length
    let b:=BoughtSockets.Public.maxMetric v.radius
    Native.text (v.widePrograms x.h x.w v.maxBits l).2 =
      93+(((Native.text pfx+((∑i,Native.text (((l).scatter i).code W))+Native.text ((l).terminal.code W last)))+
        (m+1)*5450)+(87+4*(47+20*b+9*b*(b+1)))) := by
  intro pfx last b
  change Native.text ((TagInverse.program W x.h (l).tagScratch).seq ((l).finish pfx last))=_
  rw [Native.text_seq,TagInverse.cost,WideCPU.Layout.finish_text,v.wide_installed_window_text x m ell short u δ ξ unitCost dated,
    v.wide_installed_prune_text x m ell short u δ ξ unitCost dated]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
