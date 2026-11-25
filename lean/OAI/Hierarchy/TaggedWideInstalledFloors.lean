import OAI.Hierarchy.TaggedWideInstalledLayout

namespace OAI
/-! # Containment of the original tape in the paid parent program's finite header -/
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

theorem wide_root_rows_le_flag : 2^x.h≤flag := by
  have layout:=v.catalyst_market_layout_at P x.h x.w flag (v.wideGeometryPrefix x.h x.w).2.1 le_rfl
  exact (Boot.root_extent (z:=x.h) (d:=2^v.W)).trans layout.subdivision

theorem wide_funded_le_installed_root : v.wideFundedSize x.h x.w bits≤v.wideInstalledRoot x := by
  unfold wideInstalledRoot wideScanEnd wideReserveLayout
  rw [PrefixWidths.Layout.reserve_scratch]
  change v.wideFundedSize x.h x.w bits≤v.wideFundedSize x.h x.w bits+_+_+_
  omega

theorem wide_installed_tape_bounds (m ell unitCost : ℕ) (g : WideCPU.Dated (events v.mesh).length) :
    let S:=v.wideInstalledSize x m ell unitCost g
    2^x.h≤flag ∧ flag≤v.wideFundedSize x.h x.w bits ∧ v.wideFundedSize x.h x.w bits≤S := by
  intro S
  exact ⟨v.wide_root_rows_le_flag x,v.wide_funded_extent x.h x.w bits,
    (v.wide_funded_le_installed_root x).trans (v.wide_installed_root_le_size x m ell unitCost g)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
