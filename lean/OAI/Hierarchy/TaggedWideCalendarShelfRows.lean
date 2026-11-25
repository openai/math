import OAI.Hierarchy.TaggedWideFundedReceiptCuts
import OAI.Hierarchy.TaggedWireTerminalOutputSite
import OAI.Hierarchy.TaggedWideFundedShelfFinish
import OAI.Hierarchy.ProbeFixedFundedShelfContents
import OAI.Hierarchy.TaggedWideCalendarFrame

namespace OAI
/-! # The selected installed compactor uses its original fixed shelf sockets -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows CatalystArchive
open Tagged Tagged.WideStack TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMEmit
open ProtocolRAMReportedPorts PurchaseFrozen
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (tapeSize : ℕ)
    (π : Equiv.Perm (Fin (2^x.h))) (input : Boot.Tape x.h (2^v.W)) (m ell short unitCost : ℕ)
local notation "b" => (v.widePlacement x.h x.w).catalogue
local notation "jobs" => v.wideJobs
local notation "geom" => typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
local notation "slots" => purchaseSlots x.h v.W k jobs ell
local notation "ports" => WideMemory.H x.h v.W k jobs
local notation "dir" => WideMemory.dir x.h v.W k jobs
local notation "order" => v.wideOrder x.h x.w
local notation "positive" => (b).transport order
local notation "reserve" => fuel v.mesh*x.w
variable (raw : Fin (b).rows→ ProtocolRAMEmit.Row)
    (geometry : Geometry (boardLayout x.h (2^v.W) k x.w reserve) v.radius 1 raw)
    (actual : v.FundedCutRows x.h x.w tapeSize π input raw geometry unitCost)
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates x.h v.W k jobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k jobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (kept : geometry.links.Keep (2^x.h)) (lanesFit : v.wideInstalledCap unitCost≤2^ell)

local notation "real" => FundedCutRows.installed v x tapeSize π input m ell short unitCost raw geometry actual
  prices pricePos buy groupsFit metadata kept lanesFit
local notation "printed" => FundedCutRows.printed v x tapeSize π input m ell short unitCost raw geometry actual
  prices pricePos buy groupsFit metadata kept lanesFit
local notation "port" => FundedCutRows.port v x tapeSize π input unitCost raw geometry actual

theorem FundedCutRows.shelf_port : ∀t,(real t).port=port :=
  Leaf.PrintedStage.transport v.W positive raw printed (fun _ family=>∀t,(family t).port=port) (fun _=>rfl)

include actual in
theorem FundedCutRows.shelf_injective :
    Function.Injective fun i=>(atScale positive (fun _=>v.W) v.W raw i).link := by
  intro i j eq
  exact Fin.ext ((actual.originalId i).symm.trans (eq.trans (actual.originalId j)))

include actual lanesFit in
theorem FundedCutRows.shelf_lanes (i : Fin (b).rows) :
    ProtocolRAMReportedPorts.pieces (atScale positive (fun _=>v.W) v.W raw) x.w i≤2^ell := by
  apply pieces_of_bit_bound _ _ _ x.formats.2.1 _ i
  intro j
  change (if _ then (raw j).width else 0)≤_
  split
  · exact (actual.widthBound j).trans (Nat.mul_le_mul_right x.w lanesFit)
  · exact Nat.zero_le _

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open ProbeStage CoreBoard AdaptiveProbe ReportSockets Tagged Tagged.WideStack
open ProtocolRAMEmit ProtocolRAMReportedPorts TaggedShorterBudget TaggedShorterSupergroups
open scoped Classical
variable {h W k attempts M H : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marked→Fin b.boughtRows)
    (raw : Fin b.rows→ProtocolRAMEmit.Row)
local notation "name" => b.original S π depth marked order acquired
variable (receipt : Alignment b S π depth marked M raw (fun i=>(raw i).width) name)
    (w : ℕ) (hw : 0<w) (dir : Directory (reserved h W (copies k attempts)) H) (port : Bool→Fin b.rows→Fin H)
local notation "lines" level => atScale (b.transport order) (fun _=>level) level raw
local notation "active" level => {i : Fin b.rows // 0<pieces (lines level) w i}
local notation "anchor" level => (location S π depth marked unique b order acquired raw receipt (fun _=>level)
  level w hw).trans (ReportSockets.packed dir)

/-- The old printed stage and the actual public stage use the same physical
socket for each live row. Their constant stage labels match in both masks. -/
theorem shelf_stage_anchor (level : ℕ)
    (printed : ∀(j:active 0) side,((anchor 0) (j,side)).1.val=(raw j.val).group ∧
      ((anchor 0) (j,side)).2=port side j.val) :
    ∀(j:active level) side,((anchor level) (j,side)).1.val=(raw j.val).group ∧
      ((anchor level) (j,side)).2=port side j.val := by
  intro j side
  obtain ⟨selected,_,wide⟩ := (atScale_iff b order raw (fun _ => level) level w hw j.val).mp j.property
  let z : active 0 := ⟨j.val,(atScale_iff b order raw (fun _ => 0) 0 w hw j.val).mpr ⟨selected,rfl,wide⟩⟩
  exact printed z side

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment

namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
open Tagged.WideStack
variable {E H T : Type} [Fintype H] (key : T ↪ ℕ×ℕ) (cap : E→ℕ) (roles : H→ℕ)
    (groups ports lanes dates view w : ℕ)
theorem privateWorkspace_refl :
    privateWorkspace key (Equiv.refl E) cap roles groups ports lanes dates view w=Equiv.refl _ := by
  ext i
  rcases i with j | (⟨b,⟨e,n⟩⟩ | r)
  all_goals rfl

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
end

end OAI
