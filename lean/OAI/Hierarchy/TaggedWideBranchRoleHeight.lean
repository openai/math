import OAI.Hierarchy.TaggedWireReportedPath
import OAI.Hierarchy.TaggedWireFundedCursorReplay
import OAI.Hierarchy.ProbeFixedDatedWireFits
import OAI.Hierarchy.ProbeFixedDatedWireLedger
import OAI.Hierarchy.TaggedWideWidthRoom

namespace OAI
/-! # One parent threshold for every reported path and every original dated wire -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows WireTelescope Tagged Filter
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "stock" => v.fixedTerminalStock P h width
local notation "order" => wideRouteOrder h (2^v.W) k
local notation "arena" => (v.privateArena P h width).endAddress v.mesh

/-- Every threshold is public. The aperture assertion is uniform over the
size and contents of the original funded parent, and over all larger unit prices. -/
structure BranchRoleHeight : Prop where
  report : v.reportHeight≤ h
  wordRoom : v.ReportWordRoom h width
  replay : v.cursorReplayHeight≤ h
  measure : v.wideDatedLedgerHeight≤ h
  floor : v.widthFloor≤ width
  age : v.wideStockHeight≤ h
  small : width≤ 2^h
  credit : v.keepLimit*width+1≤ 2^h
  aperture : ∀size,arena≤ size→∀(perm:Equiv.Perm (Fin (2^h))) (raw:Boot.Tape h (2^v.W)),
    let m:=v.wideSignedMidAt h width size stock v.radius perm order raw
    let c:=v.wideSignedCheckoutAt h width size stock v.radius perm order raw
    c arena=0→∀unitCost,v.sharpPaidUnit≤ unitCost→v.DatedWireFits h width perm m c unitCost

theorem cofinal_BranchRoleHeight : ∀ᶠ x : WideParent κ A in WideParent.large κ A,v.BranchRoleHeight x.h x.w := by
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [v.cofinal_report_sources (κ:=κ) (B:=A), high.eventually (eventually_ge_atTop v.cursorReplayHeight),
    high.eventually (eventually_ge_atTop v.wideDatedLedgerHeight),high.eventually (eventually_ge_atTop v.widthFloor),
    high.eventually (eventually_ge_atTop v.wideStockHeight),high.eventually v.wide_dated_wire_fits,
    WideParent.fixed_mul_width (κ:=κ) (A:=A) 1,
    WideParent.fixed_mul_width (κ:=κ) (A:=A) v.keepLimit] with x report replay measure tall age
      aperture size credit
  have small : x.w≤ 2^x.h:=by simpa only [Nat.one_mul] using (Nat.le_succ (1*x.w)).trans size
  have floor : v.widthFloor≤ x.w:=tall.trans x.property.1.2.1
  exact ⟨report.1,report.2,replay,measure,floor,age,small,credit,aperture x.w small floor credit⟩

/-- This is the function accepted verbatim by the original path-role constructor
on its actual funded tape size. -/
theorem BranchRoleHeight.funded_aperture {v : FixedProtocolFormat F k p q Q σ Λ} {h width : ℕ}
    (H : v.BranchRoleHeight h width) (size unitCost : ℕ)
    (extent : v.wideFundedSize h width v.maxBits≤ size) (rate : v.sharpPaidUnit≤ unitCost) :
    ∀(perm:Equiv.Perm (Fin (2^h))) (raw:Boot.Tape h (2^v.W)),
    let m:=v.wideSignedMidAt h width size (v.fixedTerminalStock (v.widePlacement h width) h width)
      v.radius perm (wideRouteOrder h (2^v.W) k) raw
    let c:=v.wideSignedCheckoutAt h width size (v.fixedTerminalStock (v.widePlacement h width) h width)
      v.radius perm (wideRouteOrder h (2^v.W) k) raw
    c ((v.privateArena (v.widePlacement h width) h width).endAddress v.mesh)=0 →
      v.DatedWireFits h width perm m c unitCost := by
  intro perm raw m c accepted
  exact H.aperture size ((v.wide_funded_extent h width v.maxBits).trans extent) perm raw accepted unitCost rate

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
