import OAI.Hierarchy.TaggedWideSelectedSignedApertures
import OAI.Hierarchy.TaggedWireFundedInputNumbered
import OAI.Hierarchy.TaggedWireActualRoutedSchedule

namespace OAI
/-! # Both source and offered tensor widths on the authentic selected date -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open TaggedPrune CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
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
variable {b : Fin k→ℕ} (e : OpenPins h width b→Bool) (perm : Equiv.Perm (Tagged.Row h))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path sl es base)

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "top" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
variable (height : v.BranchRoleHeight h width) (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "chosen" => WireTelescope.CalendarTape.Prefix.pathVisitAt j t onDate
local notation "date" => v.wide_funded_date_with h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior (chosen).choice (chosen).future

open Lean Elab Term in
local elab "paidCoordinate% " selectedName:ident " through " lastName:ident : term => do
  let actualFormat ← Meta.getFVarFromUserName `v
  let formatArgs := (← Meta.inferType actualFormat).consumeMData.getAppArgs
  let headName ← resolveGlobalConstNoOverload selectedName
  let decl ← getConstInfo headName
  let mut arguments := #[]
  let mut typ := decl.type
  let mut complete := false
  while typ.isForall do
    let binder := typ.bindingName!.eraseMacroScopes
    let localName := if binder == `external then `e else if binder == `π then `perm else binder
    let arg ← if typ.bindingInfo! == .instImplicit then pure formatArgs[1]! else Meta.getFVarFromUserName localName
    arguments := arguments.push arg
    if binder == lastName.getId then
      complete := true
      break
    typ := typ.bindingBody!
  unless complete do throwError "the issued physical operand has no binder {lastName.getId}"
  return mkAppN (mkConst headName (decl.levelParams.map Level.param)) arguments

open Lean Elab Term in
local elab "applyArchive% " initial:term:max " to " certificate:term:max : term => do
  let function ← elabTerm initial none
  let evidence ← elabTerm certificate none
  return mkApp function evidence

local notation "inputs" => paidCoordinate% selectedPreclipInputs through j

local notation "archived" => paidCoordinate% selectedPreclipArchived through onDate

variable (routeAge : v.routingHeight≤h)
local notation "old" => v.wide_funded_date h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior (chosen).choice
local notation "step" => v.routed_shapes h width S extent perm seed cpu.age cpu.ready.credit cpu.ready.size_le
  (chosen).prior (chosen).choice Sfit routeAge height.floor
local notation "scheduleAge" => (max_le_iff.mp routeAge).1
local notation "feeAge" => (max_le_iff.mp ((max_le_iff.mp (max_le_iff.mp scheduleAge).2).2)).1

/- Join two original width equalities at their common cursor width. -/
open Lean Elab Term in
local elab "selectedWidthEq " firstProof:term:max " from " other:term:max : term => do
  let sourceEq ← elabTerm firstProof none
  let knownEq ← elabTerm other none
  let leftType ← Meta.whnf (← Meta.inferType sourceEq)
  let rightType ← Meta.whnf (← Meta.inferType knownEq)
  unless leftType.isAppOf ``Eq && rightType.isAppOf ``Eq do throwError "expected equalities of signed widths"
  let a := leftType.getAppArgs
  let b := rightType.getAppArgs
  let r := mkAppN (mkConst ``Eq.symm rightType.getAppFn.constLevels!) #[b[0]!,b[1]!,b[2]!,knownEq]
  return mkAppN (mkConst ``Eq.trans leftType.getAppFn.constLevels!) #[a[0]!,a[1]!,a[2]!,b[1]!,sourceEq,r]

/-- The chronological input roles on the chosen visit form exactly the passive
bits and all the candidate input bits on the unpatched physical strip geometry. -/
abbrev selected_signed_input_width := selectedWidthEq ((date).signed_input_numbered Sfit height) from ((step).1)

/-- The corrected successor page of the original tape forms exactly the
passive bits and the offered pieces of those same candidates. -/
abbrev selected_signed_offer_width :=
  selectedWidthEq (applyArchive% ((old).indexed_middle_width date Sfit height.measure height.report feeAge height.wordRoom first inputs) to (archived)) from ((step).2)

/-- After clipping, the native successor rows contain precisely the paid spill
along its original core walk and the retained stock and passive rows. -/
abbrev selected_spill_output_width :=
  selectedWidthEq ((date).signed_output_numbered Sfit height) from
    (v.routed_output_width h width S extent perm seed cpu.age cpu.ready.credit cpu.ready.size_le
      (chosen).prior (chosen).choice Sfit routeAge height.floor)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
