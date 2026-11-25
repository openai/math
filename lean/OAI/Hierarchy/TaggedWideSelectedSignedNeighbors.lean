import OAI.Hierarchy.TaggedWideFundedBallotSnapshots
import OAI.Hierarchy.TaggedWideSignedEndpointReads
import OAI.Hierarchy.ProbeFixedWideSpillBallotObservation

namespace OAI
/-! # Native neighbor reads on the two signed before/preclip processors -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 550000
set_option cleanup.letToHave false
attribute [local irreducible] Nat.pow
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

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "rootROM" => v.wideInstalledRoot x
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
local notation "rankEnd" => v.wideSpillRankEnd h width v.maxBits first
variable (side : Bool) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "processed" => v.wide_selected_role_images m ell short u δ ξ unitCost x cpu rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag j side t a onDate

open CoreBoard.HistoryRoles in
open Lean Meta Elab Term in
private def readDatedRoleSheet (sheetReader fields mounted : Lean.Expr) : MetaM Lean.Expr := do
  let table := (← inferType mounted).consumeMData
  unless table.isAppOfArity ``RoleROM.Mounted 5 do throwError "expected the mounted stride table"
  forallBoundedTelescope (← inferType fields) (some 1) fun binders _ => do
    let sheet := (← inferType (mkAppN fields binders)).consumeMData
    unless sheet.isAppOfArity ``DatedRoleSheets.roleFact 18 do throwError "expected the three dated role fields"
    let r := sheet.getAppArgs
    -- The sheet supplies the geometric indices and the mounted table supplies its address.
    let inputs := r.extract 1 7 ++ #[r[0]!, r[13]!, r[9]!, table.getAppArgs[2]!, r[7]!, r[8]!,
      r[10]!, r[11]!, r[12]!, r[14]!, r[15]!, r[16]!, fields, mounted]
    return mkAppN sheetReader inputs

open Lean Meta Elab Term in
local elab "readSelectedSheets% " routine:term:arg " from " selected:term:arg " at " date:ident : term => do
  let sheetReader ← elabTerm routine none
  let seen ← withSynthesize (postpone := .no) <| elabTerm selected none
  let seen ← instantiateMVars seen
  let t ← getFVarFromUserName date.getId
  let prior ← mkAppM ``Fin.castSucc #[t]
  let later ← mkAppM ``Fin.succ #[t]
  let zero ← elabTerm (← `((0 : Fin 3))) none
  let left := fun (v : Lean.Expr) => Lean.Expr.proj ``And 0 v
  let right := fun (v : Lean.Expr) => Lean.Expr.proj ``And 1 v
  let pair := fun (a b : Lean.Expr) => do
    pure <| mkAppN (mkConst ``And.intro) #[← inferType a, ← inferType b, a, b]
  let onProcessor := fun (processor : Lean.Expr) => do
    let before := mkApp (left (right processor)) prior
    let corrected := mkAppN (right (right processor)) #[zero, later]
    pair (← readDatedRoleSheet sheetReader before (left processor))
      (← readDatedRoleSheet sheetReader corrected (left processor))
  pair (← onProcessor (left seen)) (← onProcessor (right seen))

/-- Read the original-before and corrected-preclip participants in the
ballot processor, then at the control processor which consumes that ballot.
Both pairs use the same paid date and the same chronological row numbering. -/
abbrev wide_selected_signed_neighbors :=
  readSelectedSheets% (@SiteControls.ports_of_sheet) from (processed) at t

/-- The same retained pages supply compactor offsets and overlap operands,
including speculative vacancies on both sides of a signed step. -/
abbrev wide_selected_signed_endpoints :=
  readSelectedSheets% (@SiteControls.endpoints_of_sheet) from (processed) at t

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
