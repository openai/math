import OAI.Hierarchy.ProbeFixedWideLocalRun
import OAI.Hierarchy.TaggedWideInstalledFloors
import OAI.Hierarchy.TaggedWideWindowResident
import OAI.Hierarchy.TaggedWideFullGates
import OAI.Hierarchy.TaggedWideReplayLengths

namespace OAI
/-! # Numeric operands of the dated and terminal programs on the installed tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard Tagged Filter
open scoped Classical
set_option quotPrecheck false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
    (m ell short : ℕ) (u : ℝ → ℝ) (δ ξ : ℝ) (unitCost : ℕ)
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "catalogue" => (v.widePlacement x.h x.w).catalogue
local notation "root" => v.wideInstalledRoot x
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "bits" => v.maxBits
local notation "slices" => v.widePaidSlices x.h x.w bits
local notation "numRows" => (catalogue).rows
local notation "stock" => v.fixedTerminalStock (v.widePlacement x.h x.w) x.h x.w
local notation "page" => v.wideSignedPage x.h x.w stock
local notation "dst" => CatalystArchive.TerminalLayout.destination page
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated

/-- All source and destination bounds used by the installed local block. -/
structure FundedLocalRoom : Prop where
  afterReplay : v.wideReplayedTurnBase x.h x.w slices ≤ size
  top : (v.privateArena (v.widePlacement x.h x.w) x.h x.w).endAddress v.mesh ≤ root
  funded : v.wideFundedSize x.h x.w bits ≤ size
  gap : 3*(dated).romEnd root+2 ≤ size
  publicRoom : v.wideTerminalROMEnd x.h x.w bits ((dated).romEnd root) ((dated).workEnd size) ≤ size
  room : v.wideTerminalWorkEnd x.h x.w bits ((dated).workEnd size) ≤ 2^W
  beforeROM : dst+6*numRows+ProtocolRAMPurchaseSampler.span (3*numRows) ≤ root
  highFit : v.wideFundedSize x.h x.w bits < 2^W

theorem wide_funded_local_room (lim : v.FullGateRoom x m ell short u δ ξ unitCost) :
    v.FundedLocalRoom x m ell unitCost := by
  have scratch : wideSliceBound slices ≤ 2^page :=
    wideSliceBound_le slices _ (v.wide_paid_lengths x.h x.w bits)
  have replay : v.wideReplayedTurnBase x.h x.w slices ≤ root :=
    Nat.add_le_add_left ((Nat.mul_le_mul_left 2) (max_le_max_right _ scratch)) _
  have low := v.wide_funded_le_installed_root x
  have enough := v.wide_installed_root_le_size x m ell unitCost dated
  obtain ⟨guard,terminal⟩ := v.wide_local_public_room x m ell unitCost
  have floorBound : (l).floor ≤ (l).pruneScratch := Nat.le_add_right _ _
  have allFit : (l).pruneScratch+(l).pruneRows+1 ≤ 2^W := lim.original.upper
  have before : root ≤ (dated).romEnd root := by
    unfold WideCPU.Dated.romEnd WideCPU.Dated.maskROM WideCPU.Dated.controlROMStart
      WideCPU.Dated.firstROM WideCPU.Dated.siteROM WideCPU.endOf
    omega
  have sizeFits : size ≤ 2^W := lim.original.initial
  have high : v.wideFundedSize x.h x.w bits < 2^W :=
    lt_of_le_of_lt low (by omega)
  exact ⟨replay.trans enough,(v.wide_funded_extent x.h x.w bits).trans low,
    low.trans enough,guard,terminal,floorBound.trans (by omega),v.wide_report_before_root x,high⟩

/-- The four lower age bounds hold together at the original wide parent. -/
theorem cofinal_funded_local_ages :
    ∀ᶠ y : WideParent κ A in WideParent.large κ A,
      v.wideFundedHeight ≤ y.h ∧ v.wideOperandHeight ≤ y.h ∧
      v.wideDatedSupportHeight ≤ y.h ∧ v.wideBallotHeight ≤ y.h := by
  have tall : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop := tendsto_comap
  filter_upwards [tall.eventually (eventually_ge_atTop
    (max (max v.wideFundedHeight v.wideOperandHeight) (max v.wideDatedSupportHeight v.wideBallotHeight)))]
    with y h
  exact ⟨(le_max_left ..).trans ((le_max_left ..).trans h),
    (le_max_right ..).trans ((le_max_left ..).trans h),
    (le_max_left ..).trans ((le_max_right ..).trans h),
    (le_max_right ..).trans ((le_max_right ..).trans h)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
