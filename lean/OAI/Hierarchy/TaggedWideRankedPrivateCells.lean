import OAI.Hierarchy.TaggedWideRankedRows
import OAI.Hierarchy.TaggedWideFundedPrivateCells
import OAI.Hierarchy.TaggedWideFundedHardware

namespace OAI
/-! # The private and decoded observations at the selected signed-site rank -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows CatalystArchive
open Tagged Tagged.WideStack TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMEmit
open ProtocolRAMReportedPorts PurchaseFrozen
open scoped Classical BigOperators
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

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
open CoreBoard.PhysicalTerm Tagged.WideControlJoin WideCalendarSites HistoryRoles
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune

local notation "real" => FundedCutRows.installed v x tapeSize π input m ell short unitCost raw geometry actual
  prices pricePos buy groupsFit metadata kept lanesFit
local notation "days" => events v.mesh
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "dst" => TerminalLayout.destination (v.wideSignedPage x.h x.w
  (v.fixedTerminalStock (v.widePlacement x.h x.w) x.h x.w))
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (room : cpu.SiteRoom)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
variable (a : SignedSites v m ell short δ ξ unitCost cpu)
local notation "Z" => a.schedule
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "Ex" => OpenPins x.h x.w ((Z).nativeRouting D).catalyst
local notation "Se" => Fin ((Z).nativeRouting D).selectors
local notation "Priv" => (b).Private order
local notation "cap" => v.widePrivateUnit unitCost*x.w
local notation "lim" => fun _:Priv=>cap
local notation "view" => v.wideHistoryUnit unitCost*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) («W»:=v.W) (k:=k) (attempts:=jobs)
  v.mesh unitCost v.keepLimit (fuel v.mesh) x.w
local notation "history" => Fin (((days).length+1)*Fintype.card
  ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r)))
local notation "outputBits" => ((Fin (dir).groups×Fin ports)×Fin view)
local notation "num" => CalendarTerms.privateWorkspace (geom).index (Equiv.refl Priv) lim roles
  (dir).groups ports (2^ell) ((days).length+1) view x.w
local notation "freeNet" => v.widePrivateGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.privateBits
local notation "planeNet" => v.widePlane («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room

local notation "n" => ((days).length+1)*Fintype.card ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r))
local notation "Board" => (⟨(b).rows,raw⟩ : CalendarTerms.RowBoard)
local notation "dataAt" => CalendarTerms.RankedRows (F:=F) (geom).index D (dir).groups ports (2^ell) x.w m n view

/-- Purchase, stage labels and private ordinals at the native funded report.
The pin numbering is the fixed calendar numbering used by the physical parent. -/
def FundedCutRows.rowData : dataAt Board where
  «positive» := positive
  stage := fun _=>v.W
  installed := real
  «cap» := lim
  numbering := num

local notation "purchase" => FundedCutRows.rowData v x tapeSize π input m ell short unitCost raw geometry actual
  prices pricePos buy groupsFit metadata kept lanesFit
variable (perm : Equiv.Perm (Tagged.Row x.h)) (i : Fin (((Z).nativeRouting D).count perm))
local notation "branch" => (Fintype.equivFin (Path slot days ((v.wideOrigin x.h x.w size seed) perm))).symm i
local notation "original" => (Z).reported perm branch
variable (reported : (⟨(original).edges,(original).rows⟩ : CalendarTerms.RowBoard)=Board)
local notation "atRank" => CalendarTerms.RankedRows.onBranch Z perm i reported purchase

/-- The positive apertures and the private width rooms at the selected cursor
come from the same reported purchase as the four observed gate factors. -/
theorem FundedCutRows.ranked_bounds (widths : ∀j,(raw j).width≤cap) :
    CalendarTerms.RankedRows.Bounds atRank := by
  apply CalendarTerms.RankedRows.onBranch_property Z perm i reported purchase
    (fun _ r=>CalendarTerms.RankedRows.Bounds r)
  constructor
  · exact fun e=>widths e.val
  · exact FundedCutRows.cover v x tapeSize π input m ell short unitCost raw geometry actual

/-- The two actual paid cells at the same branch rank, with all five row-dependent
fields shared by its cuts, masks and remaining chronological observations. -/
theorem FundedCutRows.ranked_private_plane (initial before out : Memory W)
    (emitted : ∀j,dst≤j→j<dst+9*(b).rows→before j=ProtocolRAMEmit.emitted dst raw initial j)
    (retained : ∀j<(lay).floor,out j=before j)
    (widths : ∀j,(raw j).width≤cap) (fits : cap<2^W) (ex : Ex→Bool) (sel : Se→Bool) :
    CalendarTerms.RankedRows.PrivatePlane G atRank freeNet planeNet ex sel ((G).terminal out) := by
  apply CalendarTerms.RankedRows.onBranch_property Z perm i reported purchase
    (fun _ r=>CalendarTerms.RankedRows.PrivatePlane G r freeNet planeNet ex sel ((G).terminal out))
  exact ⟨FundedCutRows.free v x tapeSize π input m ell short unitCost raw geometry actual
      prices pricePos buy groupsFit metadata kept lanesFit cpu room Z initial before out emitted retained
      widths fits ex sel,
    FundedCutRows.output v x tapeSize π input m ell short unitCost raw geometry actual
      prices pricePos buy groupsFit metadata kept lanesFit cpu Z out ex sel⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
