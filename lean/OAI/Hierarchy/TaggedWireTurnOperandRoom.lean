import OAI.Hierarchy.ProbeFixedWideSignedFits
import OAI.Hierarchy.ProbeStripSizeAge
import OAI.Hierarchy.ProbePublicStageCount

namespace OAI
/-! # Word sizes for all original paid operands -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open CatalystArchive StripChart CatalogueRows ColumnWires
open BoughtSockets CoreRoute PurchaseCT ProtocolRAMEmit
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable (h width : ℕ)
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "G" => (directory).groups
local notation "rows" => (P).catalogue.rows
local notation "N" => Fintype.card (Old h v.W k rows)
local notation "base" => CoreCatalogue.headBase h v.W K G H
local notation "sites" => CoreCatalogue.siteBase h v.W K
local notation "super" => CoreCatalogue.superStart h v.W
local notation "bits" => CoreCatalogue.pointBits h v.W
local notation "published" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K G H R

def wideOperandHeight := max v.wideJobs (max (publicStages v.W*(2*k)) ((v.depth+1)*v.sampler.degree^v.depth))

theorem wide_operand_room (late : v.wideOperandHeight≤h) (room : (A).endAddress v.mesh<2^w) :
    CoreCatalogue.top h v.W K G H R<2^w ∧ v.wideJobs≤2^w ∧ PurchaseFrozen.count h D k≤2^w ∧
      (v.depth+1)*PurchaseFrozen.paths h v.sampler.degree v.depth≤2^w := by
  let top:=CoreCatalogue.top h v.W K G H R
  have borders:=BoughtSockets.Public.borders v.sampler top h v.W k v.wideJobs v.depth
  have early : top≤CoreRoute.stop v.sampler h v.W k v.wideJobs v.depth K G H R :=
    (Nat.le_add_right ..).trans (borders.1.trans (borders.2.trans (Nat.le_add_right ..)))
  have arena : (A).first ≤ (A).endAddress v.mesh := Nat.le_add_right ..
  have lo := (v.wideGeometryPrefix h width).2.2.trans
    ((v.catalyst_initial_le_first P h width).trans arena)
  have small : h≤2^w:=(Nat.lt_two_pow_self (n:=h)).le.trans (v.date_prefix_fit h).le
  obtain ⟨jobs, stages, roots⟩ : v.wideJobs ≤ h ∧ publicStages v.W*(2*k) ≤ h ∧
      (v.depth+1)*v.sampler.degree^v.depth ≤ h := by
    simpa only [wideOperandHeight, max_le_iff] using late
  refine ⟨early.trans_lt (lo.trans_lt room),jobs.trans small,?_,?_⟩
  · rw [PurchaseFrozen.count,fixed_stage_count]
    exact stages.trans small
  · calc
      (v.depth+1)*PurchaseFrozen.paths h v.sampler.degree v.depth =
          2^h*((v.depth+1)*v.sampler.degree^v.depth) := Nat.mul_left_comm _ _ _
      _ ≤ 2^w := (CatalystArchive.linear_count h D Native.copies _ roots).le

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
