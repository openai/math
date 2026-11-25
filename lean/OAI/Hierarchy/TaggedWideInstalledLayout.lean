import OAI.Hierarchy.TaggedWideInstalledWindowGeometry
import OAI.Hierarchy.TaggedWideWindowWords
import OAI.Hierarchy.TaggedWideDatedROM
import OAI.Hierarchy.ProbeFixedWideFundedSpace
import OAI.Hierarchy.ProbeFixedWideFunded
import OAI.Hierarchy.ProbeFixedBroadcastCap

namespace OAI
/-! # A common mounted layout for the original signed admission and paid readout -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles Tagged
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) {κ A : ℝ} (x : WideParent κ A)
local notation "P" => v.widePlacement x.h x.w
local notation "stock" => v.fixedTerminalStock P x.h x.w
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices x.h x.w bits
local notation "T" => (events v.mesh).length

variable (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ) (dated : WideCPU.Dated (events v.mesh).length)

local notation "rom" => v.wideInstalledRoot x
local notation "S" => v.wideInstalledSize x m ell unitCost dated
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies

/-- Install original-numbering and original-edge-classification tables, all
signed chronology, and the format directories on the same finite input. -/
def wideInstalledHeader (sites : dated.siteDirectorySize=SiteDirectory.size x.h (2^v.W) k)
    (edges : dated.rawEdges=(P).catalogue.rows) (initial : Memory W) : Memory W :=
  let publicSites := fun j=>SiteDirectory.table x.h (2^v.W) k (Fin.cast sites j)
  let stage := fun j=>decide ((P).catalogue.transport (v.wideOrder x.h x.w) (Fin.cast edges j))
  let dates:=dated.words rom publicSites stage initial
  let terminal:=v.wideTerminalWords x.h x.w bits (dated.romEnd rom) (dated.workEnd S) dates
  v.wideWindowWords x m ell short u δ ξ (v.wideInstalledCap unitCost) dated bits rom terminal

theorem wideInstalled_upper :
    let l:=v.wideInstalledLayout x m ell short u δ ξ unitCost dated
    l.floor=v.wideTerminalWorkEnd x.h x.w bits (dated.workEnd S) ∧
      l.pruneScratch=WindowSeries.finish l.floor l.need := ⟨rfl,rfl⟩

theorem cofinal_installed_root :
    ∃ C : ℕ, ∀ᶠ y : WideParent κ A in WideParent.large κ A,
      v.wideInstalledRoot y≤C*2^y.h ∧
      v.wideInstalledRoot y<2^Native.wordBits y.h (2^v.W) Native.copies := by
  obtain ⟨C,h⟩:=v.cofinal_funded_scan (κ:=κ) (X:=A)
  exact ⟨C,h.mono fun y hy=>(hy v.maxBits).2⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
