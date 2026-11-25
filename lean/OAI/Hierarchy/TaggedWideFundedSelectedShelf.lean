import OAI.Hierarchy.TaggedWideFundedSelectedReturn

namespace OAI
/-! # The five terminal shelf words after the selected funded return -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open TaggedPrune Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
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
variable {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)
local notation "bought" => v.wide_selected_local_return m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j

local notation "layout" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "rom" => (g).romEnd (v.wideInstalledRoot x)
local notation "work" => (g).workEnd S
local notation "terminal" => v.wideTerminal h width v.maxBits rom work
local notation "panel" => v.wideTurnWindow h width v.maxBits work
local notation "gates" => v.wideFullGates x m ell short u δ ξ unitCost cpu.room

/-- The allocated shelf ends below the first window write, and its entire
physical interval is exposed by the dense output of the selected gate. -/
theorem wide_selected_shelf_bounds :
    (terminal).base+5*((siteLast h d k+1)*(terminal).seats) ≤ (layout).floor ∧
    (terminal).base+5*((siteLast h d k+1)*(terminal).seats) ≤ (gates).2.u := by
  have shelf : (panel).base+5*((panel).sites*(panel).seats) ≤ (panel).scratch :=
    (panel).bounds.2.2.2.1
  have scratch : (panel).scratch ≤ (panel).stop := by
    have bound := (panel).bounds.2.2.2.2
    omega
  have floor : (terminal).base+5*((siteLast h d k+1)*(terminal).seats) ≤ (layout).floor :=
    shelf.trans scratch
  have prune : (layout).floor ≤ (layout).pruneScratch := Nat.le_add_right _ _
  have space := v.wide_full_end x m ell short u δ ξ unitCost cpu.room
  have cut : (layout).pruneScratch ≤ (layout).pruneScratch+(layout).pruneRows+1 := by omega
  exact ⟨floor,floor.trans (prune.trans (cut.trans space))⟩

open LinearAlgebra.SpectralBooks ChordGraph SiteTensor in
private theorem frameMeasuredShelf {hh dd dim width₀ reserve rank den W : ℕ}
    {pi₀ : Equiv.Perm (Fin (2^hh))} {U : Widths (siteLast hh dd dim+1)}
    (Z : Report pi₀ dd dim width₀ reserve rank den U) {seats turns page : ℕ}
    {before : Memory W} {codeA codeB}
    (contents : Z.ShelfContents seats turns page before codeA codeB) (after : Memory W)
    (floor limit : ℕ) (keep : ∀ i, i < floor → after i = before i)
    (bounds : page+5*((siteLast hh dd dim+1)*seats) ≤ floor ∧ page+5*((siteLast hh dd dim+1)*seats) ≤ limit) :
    Z.ShelfContents seats turns page after codeA codeB ∧
      page+5*((siteLast hh dd dim+1)*seats) ≤ floor ∧ page+5*((siteLast hh dd dim+1)*seats) ≤ limit :=
  ⟨Report.ShelfContents.frame Z contents (fun i _ hi => keep i (hi.trans_le bounds.1)), bounds⟩

attribute [local irreducible] Report.ShelfContents

open Lean Elab Term in
local elab "preservedSelectedShelf " startId:ident " at " laterId:ident " by " frameId:ident " within " boundId:ident : term => do
  let original ← Meta.getFVarFromUserName startId.getId
  let finalMem ← Meta.getFVarFromUserName laterId.getId
  let preservation ← Meta.getFVarFromUserName frameId.getId
  let limits ← Meta.getFVarFromUserName boundId.getId
  let fields ← Meta.whnf (← Meta.inferType original)
  unless fields.getAppFn.isConstOf ``Report.ShelfContents do throwError "expected the selected shelf fields"
  let boundType ← Meta.whnf (← Meta.inferType limits)
  unless boundType.getAppFn.isConstOf ``And do throwError "expected the two allocated shelf bounds"
  let pair := boundType.getAppArgs
  let localBound := pair[0]!.getAppArgs.back!
  let paidBound := pair[1]!.getAppArgs.back!
  return mkAppN (mkConst ``frameMeasuredShelf) (fields.getAppArgs ++ #[original, finalMem, localBound, paidBound, preservation, limits])

/-- The five original fields, including inactive defaults, in the actual last
memory chosen by the signed local return. The two bounds give its exact
allocation in the local program and its paid gate. -/
abbrev wide_selected_shelf_contents :=
  let selectedReceipt := bought
  let _start := selectedReceipt.2.2.1.2.2.2.2.2.2.1
  let _out := selectedReceipt.2.2.2.choose
  let _frame := selectedReceipt.2.2.2.choose_spec.2.2.2.1
  let _bounds := v.wide_selected_shelf_bounds m ell short u δ ξ unitCost x cpu
  preservedSelectedShelf _start at _out by _frame within _bounds

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_selected_shelf_contents"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
