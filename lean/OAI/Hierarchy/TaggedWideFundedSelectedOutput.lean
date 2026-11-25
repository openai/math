import OAI.Hierarchy.TaggedWideSignedRun
import OAI.Hierarchy.TaggedWideCursorReportRows
import OAI.Hierarchy.TaggedWireActiveRouting

namespace OAI
/-! # The selected paid output from an original funded window and four site readings -/
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
set_option cleanup.letToHave false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (tapeSize : ℕ)
    (π : Equiv.Perm (Fin (2^x.h))) (input : Boot.Tape x.h (2^v.W)) (m ell short unitCost : ℕ)
local notation "b" => (v.widePlacement x.h x.w).catalogue
local notation "jobs" => v.wideJobs
local notation "geom" => typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
local notation "slots" => purchaseSlots x.h v.W k jobs ell
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
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
open CoreBoard.PhysicalTerm Tagged.WideControlJoin WideCalendarSites HistoryRoles
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune

local notation "days" => events v.mesh
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (room : cpu.SiteRoom)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
variable (a : SignedSites v m ell short δ ξ unitCost cpu)
local notation "Z" => a.schedule
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "Ex" => OpenPins x.h x.w ((Z).nativeRouting D).catalyst
local notation "Se" => Fin ((Z).nativeRouting D).selectors
local notation "cap" => v.widePrivateUnit unitCost*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) («W»:=v.W) (k:=k) (attempts:=jobs)
  v.mesh unitCost v.keepLimit (fuel v.mesh) x.w
local notation "n" => ((days).length+1)*Fintype.card ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r))

variable (perm : Equiv.Perm (Tagged.Row x.h)) (i : Fin (((Z).nativeRouting D).count perm))
local notation "branch" => (Fintype.equivFin (Path slot days ((v.wideOrigin x.h x.w size seed) perm))).symm i
local notation "original" => (Z).reported perm branch
local notation "time" => v.wideHistoryGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.history
local notation "rout" => (Z).nativeRouting D
local notation "accept" => ((rout).links ⟨perm,i⟩).Keep (2^x.h)
local notation "flagAt" => (lay).pruneScratch+(lay).pruneRows
local notation "cursor" => CalendarTape.Prefix.cursorSlot («slot»:=slot) (events:=days) (x₀:=(v.wideOrigin x.h x.w size seed) perm)
local notation "hs" => CalendarTape.Prefix.atCursor (CalendarTape.Prefix.start : CalendarTape.Prefix slot days ((v.wideOrigin x.h x.w size seed) perm)
  days ((v.wideOrigin x.h x.w size seed) perm))
local notation "ws" => CalendarTape.Prefix.atWidth ((Z).width perm)
local notation "branchAt" => CalendarTape.Prefix.histories (CalendarTape.Prefix.start : CalendarTape.Prefix slot days ((v.wideOrigin x.h x.w size seed) perm)
  days ((v.wideOrigin x.h x.w size seed) perm)) branch

variable {v x tapeSize π input m ell short unitCost raw geometry actual prices pricePos buy
  groupsFit metadata lanesFit cpu room a perm i}
variable {mem before initial out : Memory W}
local notation "signedBoard" => RowGeometry x.h (2^v.W) k x.w reserve v.radius 1
variable (same : reportGeometry perm original = (⟨(b).rows,raw,geometry⟩ : signedBoard))
local notation "sameRows" => congrArg
  (fun r : signedBoard => (⟨r.1,r.2.1⟩ : CalendarTerms.RowBoard)) same
local notation "imageType" => FundedCutRows.WindowReceipt v x tapeSize π input m ell short unitCost
  raw geometry actual prices pricePos buy groupsFit metadata lanesFit cpu.room room.purchase mem before initial out
local notation "sourceAt" ok:arg => FundedCutRows.rowData v x tapeSize π input m ell short unitCost
  raw geometry actual prices pricePos buy groupsFit metadata ok lanesFit
local notation "rankAt" ok:arg => CalendarTerms.RankedRows.onBranch Z perm i sameRows (sourceAt ok)
local notation "rankFacts" ex:arg sel:arg ok:arg place:arg => CalendarTerms.RankedRows.Endpoints Z (geom).index G time
  a.enter a.finish a.step perm i ex sel ((G).terminal out) (rankAt ok) place

/-- The four local readings on this very paid output are required precisely on
the retained report. The same party numbering is used for every reading. -/
def FundedCutRows.EndpointFacts (_image : imageType) (ex : Ex → Bool) (sel : Se → Bool) : Prop :=
  ∀ok : geometry.links.Keep (2^x.h),
    ∃place : PartyBit cursor ws days hs branchAt ↪ Fin n, rankFacts ex sel ok place

/-- Convert the paid return, including its native flag on rejected inputs,
to the selected output consumed by the signed calendar. -/
theorem FundedCutRows.selected_output (image : imageType)
    (ex : Ex → Bool) (sel : Se → Bool)
    (ran : (G).Ran (cpu.header (rout).catalyst ex sel) out)
    (nativeFlag : out flagAt = if geometry.links.Keep (2^x.h) then 1 else 0)
    (low : ∀j < (lay).floor,out j=before j)
    (widths : ∀j,(raw j).width ≤ cap) (wordFit : cap < 2^W)
    (site : FundedCutRows.EndpointFacts (a:=a) (room:=room) (perm:=perm) (i:=i) same image ex sel) :
    SignedSites.SelectedOutput (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unitCost)
      (cpu:=cpu) (a:=a) (room:=room) (items:=buy) ex sel ⟨perm,i⟩ out := by
  have links : accept ↔ geometry.links.Keep (2^x.h) := by
    rw [CalendarTerms.retained_links]
    exact Iff.of_eq (congrArg (fun r : signedBoard => r.2.2.links.Keep (2^x.h)) same)
  have flag : out flagAt = if accept then 1 else 0 := by
    rw [propext links]
    exact nativeFlag
  refine ⟨ran,flag,?_⟩
  intro allowed
  have ok := links.mp allowed
  obtain ⟨place,fields⟩ := site ok
  exact ⟨FundedCutRows.branch_from_window v x tapeSize π input m ell short unitCost raw geometry
    actual prices pricePos buy groupsFit metadata ok lanesFit cpu room a perm i sameRows
    mem before initial out image low widths wordFit flag ex sel place fields⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
