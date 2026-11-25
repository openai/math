import OAI.Hierarchy.TaggedWideInstalledFloors
import OAI.Hierarchy.ProbeFixedWidePrefixRoom

namespace OAI
/-! # The permanent native directories precede the chronological spill replay -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Tagged CatalystArchive
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A)
local notation "h" => x.h
local notation "w" => x.w
local notation "P" => v.widePlacement h w
local notation "stock" => v.fixedTerminalStock P h w
local notation "arena" => v.privateArena P h w
local notation "s" => v.wideSignedPage h w stock
local notation "ss" => v.widePaidSlices h w v.maxBits
local notation "n" => PurchaseInventory.footprint h (Stages h (2^v.W)) k
variable (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
  (g : WideCPU.Dated (events v.mesh).length)
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (l).pruneScratch+(l).pruneRows+1

theorem wide_installed_size_le_field_floor : S≤(l).floor := by
  have later : S≤g.workEnd S := by
    simp only [WideCPU.Dated.workEnd,WideCPU.Dated.slotStart,WideCPU.Dated.maskStart,
      WideCPU.Dated.controlStart,WideCPU.endOf,WideCPU.Dated.rolesEnd]
    omega
  let t := g.workEnd S
  let lo := v.wideTerminalRankStart h w v.maxBits t
  let turn := v.wideTurnWindow h w v.maxBits t
  have heads : t≤lo := by
    change t≤t+_+_+_+_+_
    omega
  have floor : lo≤turn.floor := by
    change lo≤lo+_+_+_+_+_+_+_+_
    omega
  have a := turn.bounds
  have stop : turn.floor≤turn.stop := by
    obtain ⟨a,b,c,d,e⟩:=a
    omega
  exact later.trans (heads.trans (floor.trans stop))

theorem wide_installed_size_le_prune : S≤first := by
  have base := v.wide_installed_size_le_field_floor x m ell short u δ ξ unitCost g
  have take : (l).floor≤(l).pruneScratch := Nat.le_add_right _ _
  omega

theorem wide_spill_rank_floors :
    (arena).endAddress v.mesh+ProtocolRAMPurchaseSampler.span n≤first ∧
    6*2^s≤first ∧ v.wideRoleSize h w stock ss≤first := by
  have inventory : v.wideRoleSize h w stock ss≤S :=
    (v.wide_funded_le_installed_root x).trans (v.wide_installed_root_le_size x m ell unitCost g)
  have header : 28*2^s≤v.wideRoleSize h w stock ss := v.wide_prefix_starts h w ss
  have fp : TerminalLayout.footprint v.mesh arena stock _ _ _ _ _<2^s := Nat.lt_log2_self
  unfold TerminalLayout.footprint at fp
  have size : (stock).size=ProtocolRAMPurchaseSampler.span n := rfl
  have mem := v.wide_installed_size_le_prune x m ell short u δ ξ unitCost g
  exact ⟨by omega,by omega,inventory.trans mem⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
