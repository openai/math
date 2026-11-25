import OAI.Hierarchy.TaggedWideSelectedPreclipStrict
import OAI.Hierarchy.TaggedWideRoleShelfBounds

namespace OAI
/-! # Published middle lanes of the selected signed attempt, on its terminal memory -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
-- These acquired-role types contain the complete selected execution.
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unitCost g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
    (v.wide_dated_sites h width ell unitCost) (v.wide_dated_edges h width ell unitCost) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
variable (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
variable {b : Fin k→ℕ} (e : TaggedPrune.OpenPins x.h x.w b→Bool) (perm : Equiv.Perm (Tagged.Row x.h))
    (tag : (perm : Tagged.Row x.h→Tagged.Row x.h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
variable (routeAge : v.routingHeight≤h) (height : v.BranchRoleHeight h width) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "chosen" => Prefix.pathVisitAt j t onDate
local notation "date" => v.wide_funded_date_with h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior (chosen).choice (chosen).future

local notation "inputs" => v.selectedPreclipInputs m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j


open CoreBoard.HistoryRoles LinearAlgebra.SpectralBooks ChordGraph SiteTensor
local notation "old" => v.wide_funded_date h width S extent perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  (chosen).prior (chosen).choice
local notation "scheduleAge" => (max_le_iff.mp routeAge).1
local notation "scheduleTail" => (max_le_iff.mp scheduleAge).2
local notation "feeAge" => (max_le_iff.mp ((max_le_iff.mp scheduleTail).2)).1
local notation "vroom" => v.wideHistoryUnit unitCost*x.w
local notation "cap" => v.wideNeighborCap width unitCost
local notation "fixed" => fun _ : Public v.sampler h v.W k v.wideJobs=>vroom
local notation "native" => v.wide_selected_local_return m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j
local notation "out" => (native).2.2.2.choose
local notation "sector" => v.wideSpillDates h width ell unitCost v.maxBits first
local notation "startRole" => (g).roleStart ((sector).roleRoot (v.wideSpillRankEnd h width v.maxBits first) 0) t.succ
local notation "degree" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "arch" => v.selectedPreclipArchived m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j t a onDate
local notation "bound" => (v.wide_selected_preclip_strict m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j height t a onDate).1
local notation "realField" => v.selectedPreclipRole m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j t a onDate height
local notation "within" => fun _ : Public v.sampler h v.W k v.wideJobs=>v.selectedPreclipWithin unitCost x
local notation "wordFits" => fun _ : Public v.sampler h v.W k v.wideJobs=>
    v.selectedPreclipWord m ell short u δ ξ unitCost x rate support

/-- The local bit injection on the actual preclip width of the fixed operator.
Its padded physical lane space is shared by both sides of the contraction. -/
def selected_preclip_layout :=
  (old).preclip_indexed_layout date Sfit height.measure height.report feeAge height.wordRoom first inputs arch
    (date).preclipUnique fixed bound within

local notation "layout" => v.selected_preclip_layout m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j routeAge height t a onDate

/-- Every intermediate bit is assigned a lane at its original site. -/
abbrev selected_preclip_site :=
  (old).preclip_indexed_site date Sfit height.measure height.report feeAge height.wordRoom first inputs arch
    (date).preclipUnique fixed bound within

/-- Exactly the active middle cells of this injection carry a positive
remaining digit on the returned original width sheet. -/
theorem selected_preclip_published {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
    (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
    {b : Fin k→ℕ} (e : TaggedPrune.OpenPins x.h x.w b→Bool) (perm : Equiv.Perm (Tagged.Row x.h))
    (tag : (perm : Tagged.Row x.h→Tagged.Row x.h)=Tagged.tag (fun i=>e (.inl i)))
    (j : Path sl es base)
    (routeAge : v.routingHeight≤h) (height : v.BranchRoleHeight h width) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)
    (site : Fin (siteLast h d k+1)) (cell : Fin (degree*cap)) :
    (site,cell)∈Set.range layout ↔
      (finProdFinEquiv.symm cell).2.val<
        ((out) (startRole+1+(finProdFinEquiv (site,(finProdFinEquiv.symm cell).1)).val)).val :=
  (old).preclip_published date Sfit height.measure height.report feeAge height.wordRoom first inputs arch
    (date).preclipUnique fixed bound within wordFits _ startRole out _ realField site cell

/-- The returned width word also fits the comparator at every unoccupied
socket of each site. -/
theorem selected_preclip_strict {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
    (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F menu x t slots
      (purchaseCandidates h v.W k v.wideJobs slots ((menu).height t x) (purchaseModules v.W u δ ξ menu x t))
      (purchaseModules v.W u δ ξ menu x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
    {b : Fin k→ℕ} (e : TaggedPrune.OpenPins x.h x.w b→Bool) (perm : Equiv.Perm (Tagged.Row x.h))
    (tag : (perm : Tagged.Row x.h→Tagged.Row x.h)=Tagged.tag (fun i=>e (.inl i)))
    (j : Path sl es base)
    (_routeAge : v.routingHeight≤h) (height : v.BranchRoleHeight h width) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)
    (site : Fin (siteLast h d k+1)) (socket : Fin degree) :
    ((out) (startRole+1+(finProdFinEquiv (site,socket)).val)).val<2^(v.wideNeighborDigits width unitCost+1) := by
  have socketBound : ((out) (startRole+1+(finProdFinEquiv (site,socket)).val)).val≤vroom :=
    DatedRoleSheets.roleFact.socket_le _ _ _ _ _ _ _ _ vroom (fun i=>bound i false)
      (fun i=>(bound i false).trans_lt (v.selectedPreclipWord m ell short u δ ξ unitCost x rate support)) _ startRole out realField (finProdFinEquiv (site,socket))
  have bit : 2^(v.wideNeighborDigits width unitCost)<2^(v.wideNeighborDigits width unitCost+1) := by
    rw [Nat.pow_succ]
    have positive:=Nat.two_pow_pos (v.wideNeighborDigits width unitCost)
    omega
  exact socketBound.trans_lt ((v.selectedPreclipWithin unitCost x).trans_lt bit)

-- Skip optional premise indexing for the two fully specialized physical readouts.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry (Lean.LibrarySuggestions.nameDenyListExt.addEntry env "selected_preclip_published") "selected_preclip_strict"

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
