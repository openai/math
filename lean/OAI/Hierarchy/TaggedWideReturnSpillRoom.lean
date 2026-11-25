import OAI.Hierarchy.TaggedWideFundedLocalRoom
import OAI.Hierarchy.TaggedWideSpillFloors
import OAI.Hierarchy.TaggedWideFullSpace

namespace OAI
/-! # Room for the corrected spill sweep on the installed paid parent gate -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Tagged Filter
open scoped Classical
set_option quotPrecheck false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A s : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
    (m ell short : ℕ) (u : ℝ → ℝ) (δ ξ : ℝ) (unitCost : ℕ)
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "place" => v.widePlacement x.h x.w
local notation "arena" => v.privateArena place x.h x.w
local notation "root" => v.wideInstalledRoot x
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "bits" => v.maxBits
local notation "slices" => v.widePaidSlices x.h x.w bits
local notation "stock" => v.fixedTerminalStock place x.h x.w
local notation "page" => v.wideSignedPage x.h x.w stock
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "first" => (l).pruneScratch+(l).pruneRows+1
local notation "rankEnd" => v.wideSpillRankEnd x.h x.w bits first
local notation "correct" => v.wideSpillDates x.h x.w ell unitCost bits first
local notation "tRom" => (dated).romEnd root
local notation "tWork" => (dated).workEnd size
local notation "endAll" => v.wideCorrectedSpillEnd x.h x.w ell unitCost bits root size tRom tWork first

structure ReturnSpillRoom : Prop where
  archiveFloor : (arena).endAddress v.mesh+
    ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint x.h (Stages x.h (2^v.W)) k) ≤ first
  headFloor : 6*2^page ≤ first
  funded : v.wideFundedSize x.h x.w bits ≤ first
  heap : (v.wideReserveLayout x.h x.w slices).scratch ≤ first
  oldBefore : size ≤ first
  room : (correct).endAt rankEnd < 2^W
  wide : 2 < 2^W
  endRoom : endAll ≤ 2^W
  readOnly : v.wideTerminalROMEnd x.h x.w bits tRom tWork ≤ tWork
  replayed : v.wideReplayedTurnBase x.h x.w slices ≤ tWork
  terminalFloor : v.wideTerminalWorkEnd x.h x.w bits tWork ≤ first
  top : (arena).endAddress v.mesh ≤ root
  gap : 3*tRom+2 ≤ size
  highFit : v.wideFundedSize x.h x.w bits < 2^W

theorem wide_return_spill_room (lim : v.FullGateRoom x m ell short u δ ξ unitCost)
    (dateRoom : (correct).endAt rankEnd < 2^W) :
    v.ReturnSpillRoom x m ell short u δ ξ unitCost := by
  have prior := v.wide_funded_local_room x m ell short u δ ξ unitCost lim
  obtain ⟨a,b,c⟩ := v.wide_spill_rank_floors x m ell short u δ ξ unitCost dated
  have oldBefore := v.wide_installed_size_le_prune x m ell short u δ ξ unitCost dated
  have later : size ≤ tWork := by
    unfold WideCPU.Dated.workEnd WideCPU.Dated.slotStart WideCPU.Dated.maskStart
      WideCPU.Dated.controlStart WideCPU.Dated.rolesEnd WideCPU.endOf
    omega
  have scratch : (v.wideReserveLayout x.h x.w slices).scratch ≤
      v.wideReplayedTurnBase x.h x.w slices := Nat.le_add_right _ _
  have word : 4 ≤ 2^W := Nat.pow_le_pow_right (n:=2) (by decide) (show 2 ≤ W by
    rw [Native.wordBits_linear]
    omega)
  have terminalFloor : (l).floor ≤ (l).pruneScratch := Nat.le_add_right _ _
  exact ⟨a,b,c,scratch.trans (prior.afterReplay.trans oldBefore),oldBefore,dateRoom,
    (by omega), (le_max_right first endAll).trans lim.upper,prior.publicRoom.trans later,
    prior.afterReplay.trans later,terminalFloor.trans (by omega),prior.top,prior.gap,prior.highFit⟩

theorem cofinal_return_spill_room {u : ℝ → ℝ} (hu : TaggedWidthProfile.Admissible s u)
    (δ ξ : ℝ) (unitCost : ℕ) :
    ∀ᶠ y : WideParent κ A in WideParent.large κ A,
      ∀_lim : v.FullGateRoom y m ell short u δ ξ unitCost,
        v.ReturnSpillRoom y m ell short u δ ξ unitCost := by
  filter_upwards [v.cofinal_full_spill_space (κ:=κ) (A:=A) m ell short hu δ ξ unitCost]
    with y room
  intro _lim
  exact v.wide_return_spill_room y m ell short u δ ξ unitCost _lim (lt_of_le_of_lt room.2.1 room.2.2)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
