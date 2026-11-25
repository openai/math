import OAI.Hierarchy.TaggedWideWindowProgramLayout
import OAI.Hierarchy.TaggedWideReplaySpace
import OAI.Hierarchy.ProbeFixedBroadcastCap

namespace OAI
/-! # Physical addresses and extent of the installed calendar windows -/

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

def wideInstalledRoot :=
  v.wideScanEnd x.h x.w ss (2^v.wideSignedPage x.h x.w stock)

/-- For normalized width above one the native compactor uses one cell per
whole unit and one residual cell. -/
def wideInstalledCap (unitCost : ℕ) := v.widePrivateUnit unitCost+1

variable (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ) (dated : WideCPU.Dated (events v.mesh).length)

def wideInstalledLayout : WideCPU.Layout m :=
  v.wideWindowProgramLayout x m ell short u δ ξ (v.wideInstalledCap unitCost) dated bits (v.wideInstalledRoot x)

def wideInstalledSize :=
  v.wideFormatEnd x m ell (v.wideInstalledCap unitCost) dated bits (v.wideInstalledRoot x)


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Tagged
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A)
local notation "P" => v.widePlacement x.h x.w
local notation "stock" => v.fixedTerminalStock P x.h x.w
local notation "flag" => (v.privateArena P x.h x.w).endAddress v.mesh
local notation "bits" => v.maxBits

theorem wide_installed_root_le_size (m ell unitCost : ℕ) (g : WideCPU.Dated (events v.mesh).length) :
    v.wideInstalledRoot x≤v.wideInstalledSize x m ell unitCost g := by
  let start := v.wideInstalledRoot x
  calc
    start ≤ g.siteROM start := Nat.le_add_right ..
    _ ≤ g.firstROM start := Nat.le_add_right ..
    _ ≤ g.controlROMStart start := Nat.le_add_right ..
    _ ≤ g.maskROM start := Nat.le_add_right ..
    _ ≤ g.romEnd start := Nat.le_add_right ..
    _ ≤ v.wideGroupROM x g v.maxBits start := by
      have bound (a b : ℕ) : b ≤ a + 2*b + 2 := by omega
      exact bound _ _
    _ ≤ v.wideLayersROM x g v.maxBits start := Nat.le_add_right ..
    _ ≤ v.wideFormatROM x g v.maxBits start := Nat.le_add_right ..
    _ ≤ v.wideInstalledSize x m ell unitCost g := Nat.le_add_right ..

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end OAI
