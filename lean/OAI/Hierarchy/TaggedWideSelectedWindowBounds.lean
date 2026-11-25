import OAI.Hierarchy.TaggedWideFundedSelectedReturn
import OAI.Hierarchy.TaggedWideFundedPathKeep

namespace OAI
/-! # The actual selected return and its original row geometry -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192

private theorem same_packed_geometry {h d k w R M den : ℕ} (π : Equiv.Perm (Tagged.Row h))
    {a b : (U : _) × CoreBoard.Report π d k w R M den U} (same : a = b) :
    reportGeometry π a.2 = reportGeometry π b.2 :=
  congrArg (fun data : (U : _) × CoreBoard.Report π d k w R M den U => reportGeometry π data.2) same

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
variable {b : Fin k→ℕ} (e : TaggedPrune.OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)
local notation "report" => v.wide_reported_path h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le
    Sfit support.size.late support.size.words j
local notation "bought" => v.wide_selected_local_return m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j
local notation "packed" => (U : _) × CoreBoard.Report perm d k width (fuel v.mesh*width) v.radius 1 U

/-- Geometry projection of exactly the dependent native returned by the selected
CPU, including all original row indices, geometry and public link scores. -/
abbrev wide_selected_geometry :=
  same_packed_geometry perm (bought).1

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
