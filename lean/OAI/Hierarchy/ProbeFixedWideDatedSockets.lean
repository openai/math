import OAI.Hierarchy.TaggedWireOriginalWork
import OAI.Hierarchy.ProbeFixedWideDated
import OAI.Hierarchy.ProbeFixedWideDatedCost
import OAI.Hierarchy.TaggedWideDatedSocketWork

namespace OAI
/-! Dated socket work on the original wide priced board. -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open CoreRoute HistoryRoles RoleProgram
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width ell unitCost : ℕ)
local notation "P" => v.widePlacement h width
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "G" => (dir).groups
local notation "shape" => RoleRoom.shape («R»:=R) v.sampler dir (P).catalogue.rows
local notation "base" => CoreCatalogue.headBase h v.W K G H
local notation "sites" => CoreCatalogue.siteBase h v.W K
local notation "super" => CoreCatalogue.superStart h v.W
local notation "bits" => CoreCatalogue.pointBits h v.W
local notation "published" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K G H R
local notation "start" => v.wideRoleStart h width (v.fixedTerminalStock P h width) (v.widePaidSlices h width v.maxBits)
local notation "B" => v.wideTerminalBoard h width v.maxBits 0
local notation "D" => v.wideDated h width ell unitCost
local notation "u" => paidWidthWork v.W k v.wideJobs
local notation "old" => oldWork k u (coreWidthWork k v.wideJobs)

theorem wide_terminal_before_work (side : Bool) : ((B).before side).Work old :=
  full_original_work ((shape).chart start) (P).catalogue published v.sampler start (B).old ((shape).ext start)
    ((shape).axis start) base ((shape).free start) R bits sites super K G H h v.W k v.depth side

theorem wide_terminal_finish_work (side : Bool) : ((B).finish side).Work u :=
  paid_work (P).catalogue published v.sampler h v.W k v.depth K base ((shape).free start) R bits super side

def wideDatedSocketWork := max (22*v.wideRoleWorkBound+4) (4*(22*old+4)+18)
def wideDatedSlotWork := 2*(4*u+18)+2*u+1

theorem wide_dated_input_work (j : Fin ((events v.mesh).length+1)) :
    DatedRoleSheets.InputWork (D).physical (D).chart (D).sockets ((D).amount j) (D).ordinal v.wideDatedSocketWork := by
  obtain ⟨ordinal,widths⟩:=v.wide_role_work_at h width v.maxBits
  exact DatedRows.input_work (B).old (B).chart (B).before _ _ (v.wide_terminal_before_work h width)
    (widths j.val) ordinal

theorem wide_dated_slot_work (side : Bool) : ((D).orderedSlot side).work≤v.wideDatedSlotWork :=
  (normalized_work (B).chart (B).finish (v.wide_terminal_finish_work h width) side).slot


theorem wide_dated_role_inputs : ∃U:ℕ,∀h width ell unitCost,
    let a:=v.wideDated h width ell unitCost
    (∀j,DatedRoleSheets.InputWork a.physical a.chart a.sockets (a.amount j) a.ordinal U) ∧
      ∀side,(a.orderedSlot side).work≤U := by
  refine ⟨max v.wideDatedSocketWork v.wideDatedSlotWork,?_⟩
  intro h width ell unitCost
  constructor
  · intro j
    obtain ⟨a,b,c,d,e⟩:=v.wide_dated_input_work h width ell unitCost j
    have le:=Nat.le_max_left v.wideDatedSocketWork v.wideDatedSlotWork
    exact ⟨a.trans le,b.trans le,c.trans le,d.trans le,e.trans le⟩
  · intro side
    exact (v.wide_dated_slot_work h width ell unitCost side).trans (Nat.le_max_right ..)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
