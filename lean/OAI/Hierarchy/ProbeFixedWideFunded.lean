import OAI.Hierarchy.ProbeFixedWideFundedSize
import OAI.Hierarchy.ProbeFixedWidePaidRun
import OAI.Hierarchy.ProbeFixedWideStockRun

namespace OAI
/-! # One funded run from the original finite signed input and paid date directories -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "stock" => v.fixedTerminalStock P h width
local notation "w" => Native.wordBits h D Native.copies
local notation "order" => wideRouteOrder h D k
local notation "C" => v.wideSignedChart h width stock
local notation "page" => v.wideSignedPage h width stock
local notation "banks" => TerminalLayout.settlement page stock
local notation "ss" => v.widePaidSlices h width

/-- All repeated repair and reporter word bounds at one public height. -/
def wideFundedHeight := max v.wideSignedHeight v.wideStockHeight

def wideFundedRaw (bits : ℕ) (raw : Boot.Tape h D) : Boot.Tape h D :=
  v.wideRoleWords h width stock (ss bits) (v.widePairedWords h width raw)

theorem wide_funded_extent (bits : ℕ) : (A).endAddress v.mesh≤v.wideFundedSize h width bits := by
  let high:=v.wideRoleStart h width stock (ss bits)
  let z:=RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler
    (WideMemory.dir h v.W k v.wideJobs) (P).catalogue.rows
  have first : (A).endAddress v.mesh≤high:=le_max_left ..
  change (A).endAddress v.mesh≤z.ceiling high
  dsimp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
    RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
  omega

section FundedExecution
set_option maxRecDepth 4096

/-- The remaining input suffix may carry additional immutable directories for the
readback program. The signed roles and pair directories occupy their original addresses. -/
theorem wide_funded_stock_at_size (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (bits : ℕ)
    (endPos : ℕ) (extent : (v.wideFundedSize h width bits)≤endPos) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) :
    StockBound.Run C (v.stockBanks P h width) (v.wideSignedMidAt h width endPos stock M π order (v.wideFundedRaw h width bits raw))
      h (Stages h D) k (v.keepLimit*width) :=
  v.wide_stock_at h width endPos ((v.wide_funded_extent h width bits).trans extent) M π (v.wideFundedRaw h width bits raw)
    ((le_max_right ..).trans height) budget small

theorem wide_funded_paid_at_size (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (bits : ℕ)
    (endPos : ℕ) (extent : (v.wideFundedSize h width bits)≤endPos) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) :
    PaidWidths.Mounted (banks).width (P).catalogue.rows (TerminalLayout.source page) (ss bits)
      (v.wideSignedCheckoutAt h width endPos stock M π order (v.wideFundedRaw h width bits raw)) := by
  let roleRaw:=v.wideRoleWords h width stock (ss bits) raw
  have commute : (v.wideFundedRaw h width bits raw)=v.widePairedWords h width roleRaw:=v.wide_role_pair_words h width stock _ raw
  have mounted:=(v.wide_funded_stock_at_size h width M π raw bits endPos extent height budget small).mounted_all
  change Calendar.mounted C (events v.mesh) (v.wideSignedMidAt h width endPos stock M π order (v.wideFundedRaw h width bits raw)) at mounted
  rw [commute] at mounted ⊢
  exact v.wide_paid_mounted_at h width endPos ((v.wide_funded_extent h width bits).trans extent) M π
    roleRaw bits ((le_max_left ..).trans height) budget mounted

set_option maxHeartbeats 2000000 in
/-- Execute the charged calendar and its terminal settlement on the actual finite
tape. The result includes reconciliation, the final flag, and the physical debit sums. -/
abbrev wide_funded_run_at (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (bits : ℕ)
    (endPos : ℕ) (extent : (v.wideFundedSize h width bits)≤endPos) (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (state : Word w) :=
  let run:=v.wide_funded_stock_at_size h width M π raw bits endPos extent height budget small
  let paid:=v.wide_funded_paid_at_size h width M π raw bits endPos extent height budget small
  let settle := v.wide_retained_run_at h width endPos ((v.wide_funded_extent h width bits).trans extent) M π
    (v.wideFundedRaw h width bits raw) (ss bits) ((le_max_left ..).trans height) small budget state run.mounted_all
  settle paid

theorem wide_funded_stock_at (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (bits : ℕ)
    (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) :
    StockBound.Run C (v.stockBanks P h width) (v.wideSignedMidAt h width (v.wideFundedSize h width bits) stock M π order (v.wideFundedRaw h width bits raw)) h (Stages h D) k (v.keepLimit*width) :=
  v.wide_funded_stock_at_size h width M π raw bits (v.wideFundedSize h width bits) le_rfl height budget small

theorem wide_funded_paid_at (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (bits : ℕ)
    (height : v.wideFundedHeight≤h)
    (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) :
    PaidWidths.Mounted (banks).width (P).catalogue.rows (TerminalLayout.source page) (ss bits) (v.wideSignedCheckoutAt h width (v.wideFundedSize h width bits) stock M π order (v.wideFundedRaw h width bits raw)) :=
  v.wide_funded_paid_at_size h width M π raw bits (v.wideFundedSize h width bits) le_rfl height budget small

set_option maxHeartbeats 2000000 in
abbrev wide_funded_run (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (bits : ℕ)
   := v.wide_funded_run_at h width M π raw bits (v.wideFundedSize h width bits) le_rfl

end FundedExecution

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
