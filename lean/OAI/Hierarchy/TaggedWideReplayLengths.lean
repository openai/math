import OAI.Hierarchy.TaggedWideReplaySpace
import OAI.Hierarchy.ProbeFixedWidePaidRun

namespace OAI
/-! # Row capacity chosen directly from the native paid-slice directory -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires Filter
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "D" => 2^v.W
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "s" => v.nativeBoards P h width
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "r" => Fintype.card (Slots h D k)
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl

/-- The original revenue, forest and commodity directories are all covered by
the dyadic page that the settlement code already allocated. -/
theorem wide_paid_lengths (bits : ℕ) :
    ∀ t∈v.widePaidSlices h width bits,t.count≤2^page := by
  let roles:=max (Fintype.card (StripDirectory.PayloadRole (Stages h D) k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k))
  let stride:=ownerRowFactor D k v.sampler.degree v.depth roles*2^h
  have fits : TerminalLayout.footprint v.mesh A stock stride (P).catalogue.rows r
      (Fintype.card (Columns h D)*k) cnt<2^page := Nat.lt_log2_self
  unfold TerminalLayout.footprint at fits
  have first : (A).first≤(A).endAddress v.mesh := Nat.le_add_right ..
  have low : v.catalystStaticStart P h width≤(A).first := v.catalyst_static_before P h width
  have firstFit : (A).first≤2^page := by omega
  have slotsFit : r≤2^page := by omega
  intro t ht
  exact (v.paid_pair_geometry P h width _ _ _ _ _ _ _ _ _ bits (2^page) firstFit
    (low.trans firstFit) slotsFit t ht).2.2

/-- One fixed page choice pays the maximum slice count and the actual reserve
scan above the original mounted archive throughout the wide-parent filter. -/
theorem cofinal_paid_scan {κ X : ℝ} (K : ℕ) :
    ∃ C : ℕ,∀ᶠ x : Tagged.WideParent κ X in Tagged.WideParent.large κ X,
      ∀ bits : ℕ,
      let placement:=v.widePlacement x.h x.w
      let terminalStock:=v.fixedTerminalStock placement x.h x.w
      let maxRows:=2^v.wideSignedPage x.h x.w terminalStock
      let ss:=v.widePaidSlices x.h x.w bits
      v.wideRoleSize x.h x.w terminalStock ss≤K*2^x.h →
      (∀ t∈ss,t.count≤ maxRows) ∧ v.wideScanEnd x.h x.w ss maxRows≤C*2^x.h ∧
        v.wideScanEnd x.h x.w ss maxRows<2^Native.wordBits x.h D Native.copies := by
  obtain ⟨C,ready⟩:=v.cofinal_scan_linear (κ:=κ) (X:=X) K
  refine ⟨C,?_⟩
  filter_upwards [ready] with x bound bits placement terminalStock maxRows ss cap
  exact ⟨v.wide_paid_lengths x.h x.w bits,bound ss maxRows le_rfl cap⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
