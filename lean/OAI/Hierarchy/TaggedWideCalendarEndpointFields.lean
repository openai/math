import OAI.Hierarchy.TaggedWideCalendarEvaluates
import OAI.Hierarchy.TaggedWideRankedChecks
import OAI.Hierarchy.TaggedWideFundedHistoryMask
import OAI.Hierarchy.TaggedWidePathFirstNetwork

namespace OAI
/-! # All four selected native observations use the same fixed party placement -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option cleanup.letToHave false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A C : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    {N : ℕ} (x : WideParent κ A)
local notation "unit" => v.calendarUnit
variable (cpu : v.ParentFullCPUs m ell short u δ ξ unit N x) (room : cpu.SiteRoom)
    (control : SignedSites.CalendarControlRoom (cpu:=cpu))
    (support : v.SelectedReturnSupport m ell short u δ ξ unit v.calendarUnit_rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unit
local notation "S" => v.wideInstalledSize x m ell unit g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unit g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unit g
    (v.wide_dated_sites h width ell unit) (v.wide_dated_edges h width ell unit) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "D" => v.parentShared x m ell short unit ((es).length+1)
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
local notation "base" => v.wideOrigin h width S seed
variable (Z : CalendarTerms F h d k width (fuel v.mesh*width) v.radius 1 sl es base)
local notation "rout" => Z.nativeRouting D
local notation "sites" => SignedSites.ofCalendar (cpu:=cpu) Z control v.calendarTerminalWidth
  (v.calendarTerminalPins x m ell short)
local notation "source" => fun _ : Fin (m+1)=>slots
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates h v.W k v.wideJobs slots ((menu).height i x) (count i)
local notation "Buy" => PurchaseList (F:=F) (C:=C) menu x source target count
local notation "Ex" => OpenPins h width (rout).catalyst
local notation "report" π:arg j:arg => v.wide_reported_path h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words j
variable (sourceRows : ∀π j,reportGeometry π (Z.reported π j)=reportGeometry π (report π j))
    (prices : v.PhysicalCounts u A δ ξ m) (pricePos : 0≤κ)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ menu x)
    (metadata : ∀t:Fin (m+1),1+(menu).height t x+(menu).height t x≤(menu).payload t x)
    (lanesFit : v.wideInstalledCap unit≤2^ell)
variable (buy : Buy) (e : Ex→Bool) (perm : Equiv.Perm (Tagged.Row h)) (i : Fin ((rout).count perm))
    (tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)))
local notation "path" => (Fintype.equivFin (Path sl es (base perm))).symm i
local notation "record" => CalendarTape.encode sl es (base perm) path
local notation "runAt" => v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag path
local notation "finishAt" => (runAt).2.2.2
local notation "windowAt" => (finishAt).choose_spec.2.2.2.2
local notation "joinedRows" => (sourceRows perm path).trans
  (v.wide_selected_geometry m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag path)


open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.BranchRoles Tagged.WideCalendarSites
local notation "tree" p:arg => WireTelescope.CalendarTape.Prefix.cursorSlot («slot»:=sl) (events:=es) (x₀:=base p)
local notation "fundedWidth" p:arg => WireTelescope.CalendarTape.Prefix.atWidth («slot»:=sl) (events:=es) (x₀:=base p) («S»:=siteLast h (2^v.W) k+1)
  (fun {_ _} c => v.wideCursorWidth h width S p seed cpu.age cpu.ready.credit cpu.ready.size_le c)
variable (height : v.BranchRoleHeight h width)
    (widthSource : ∀p, WireTelescope.CalendarTape.Prefix.atWidth (Z.width p) = fundedWidth p)
local notation "root" => (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix sl es (base perm) es (base perm))
local notation "top" => WireTelescope.CalendarTape.Prefix.atCursor root
local notation "branch" => WireTelescope.CalendarTape.Prefix.histories root path
local notation "public" => CoreBoard.HistoryRoles.Public v.sampler h v.W k v.wideJobs
local notation "roles" => HistoryRoles.ceiling v.sampler («h»:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unit v.keepLimit (fuel v.mesh) width
local notation "n" => ((es).length+1)*Fintype.card ((r:public)×Fin (roles r))
local notation "rows" => v.widePathCells h width S perm seed cpu.age cpu.ready.credit cpu.ready.size_le Sfit
  height.report height.wordRoom path unit height.replay height.measure (height.funded_aperture S unit Sfit v.calendarUnit_rate)

private def placeAtWidth {I : Type*} (A : I→Type*) {a b:I} {J:Type*}
    (eqn : a=b) (f:A b ↪ J) : A a ↪ J := eqn.symm ▸ f

private theorem placeAtWidth_range {I : Type*} (A : I→Type*) {a b:I} {J:Type*}
    (eqn : a=b) (f:A b ↪ J) :
    Set.range (placeAtWidth A eqn f)=Set.range f := by
  cases eqn
  rfl

/-- The participant-bit injection on the actual history. Its only cast updates
the spelling of the cursor width vector of the signed calendar. -/
def wideCalendarPartyPlace : PartyBit (tree perm) (WireTelescope.CalendarTape.Prefix.atWidth (Z.width perm)) es top branch ↪ Fin n :=
  placeAtWidth (fun w=>PartyBit (tree perm) w es top branch) (widthSource perm)
    (timelineFin (tree perm) (fundedWidth perm) rows es top branch)

local notation "fixedPlace" => v.wideCalendarPartyPlace m ell short u δ ξ x cpu Z perm i height widthSource
theorem wideCalendarPartyPlace_range :
    Set.range fixedPlace=Set.range (timelineFin (tree perm) (fundedWidth perm) rows es top branch) :=
  placeAtWidth_range _ _ _

local notation "endpoint" => v.wideCalendarEndpointReads (C:=C) m ell short u δ ξ x cpu room control support
  Z sourceRows prices pricePos groupsFit metadata lanesFit

attribute [local irreducible] FundedCutRows.EndpointFacts

private theorem endpointCases {P : CalendarTerms.EndpointField → Prop}
    (hm : P .historyMask) (h₁ : P .first) (h₂ : P .finish) (stepCase : P .steps) (op : CalendarTerms.EndpointField) :
    P op := by
  cases op with
  | historyMask => exact hm
  | first => exact h₁
  | finish => exact h₂
  | steps => exact stepCase

-- Retain the exact arguments used by the original endpoint's funded window.
open Lean Elab Term in
local elab "checkOnEndpoint " endpointArg:term " using " injection:term " forField " op:ident : term => do
  let endpointExpr ← elabTerm endpointArg none
  let endpointType ← Meta.whnf endpointExpr
  unless endpointType.isAppOf ``FundedCutRows.EndpointFacts do throwError "expected the selected funded endpoint"
  let embedding ← elabTerm injection none
  let fieldId ← Meta.getFVarFromUserName op.getId
  return mkAppN (← Meta.mkConstWithFreshMVarLevels ``FundedCutRows.EndpointCheck)
    ((endpointType.getAppArgs.push embedding).push fieldId)

open Lean Elab Term in
local elab "fundedEndpointCases " maskId:ident firstId:ident finishId:ident stepsId:ident : term => do
  let maskProof ← Meta.getFVarFromUserName maskId.getId
  let firstProof ← Meta.getFVarFromUserName firstId.getId
  let finishProof ← Meta.getFVarFromUserName finishId.getId
  let stepsProof ← Meta.getFVarFromUserName stepsId.getId
  let checked ← Meta.whnf (← Meta.inferType maskProof)
  unless checked.isAppOf ``FundedCutRows.EndpointCheck do throwError "expected the funded history-mask check"
  let inputs := checked.getAppArgs.pop
  let family := mkAppN checked.getAppFn inputs
  let proofCases := mkAppN (mkConst ``endpointCases) #[family, maskProof, firstProof, finishProof, stepsProof]
  return mkAppN (← Meta.mkConstWithFreshMVarLevels ``FundedCutRows.endpointFacts_of_checks)
    (inputs.push proofCases)

open Lean Elab Command Term Meta in
local elab "defineSelectedEndpointField " body:term : command => do
  let checkedDefinitionName :=  (← getCurrNamespace) ++ `wideCalendarEndpointField
  runTermElabM fun context => do
    let result ← withoutErrToSorry <| elabTerm body none
    synthesizeSyntheticMVarsNoPostponing
    let closed ← mkLambdaFVars context (← instantiateMVars result) (usedOnly := true)
    let value ← Term.levelMVarToParam closed
    let type ← instantiateMVars (← inferType value)
    if value.hasFVar || value.hasMVar || value.hasSorry || type.hasFVar || type.hasMVar || type.hasSorry then
      throwError "the selected endpoint has unbound operands"
    let levels := (collectLevelParams {} type).params.toList
    addDecl (.defnDecl {
      name := checkedDefinitionName
      levelParams := levels
      type := type
      value := value
      hints := .regular 1
      safety := .safe
    })
    addDocStringCore checkedDefinitionName "The specified endpoint observation on the selected paid window at its fixed party placement."

defineSelectedEndpointField (fun (_op : CalendarTerms.EndpointField) =>
  checkOnEndpoint (endpoint buy e perm i tag) using fixedPlace forField _op)

attribute [local irreducible] FundedCutRows.EndpointCheck

local notation "field" => v.wideCalendarEndpointField (C:=C) m ell short u δ ξ x cpu room control support
  Z sourceRows prices pricePos groupsFit metadata lanesFit buy e perm i tag height widthSource

theorem wide_calendar_endpoint_reads (mask : field .historyMask) (first : field .first)
    (finish : field .finish) (steps : field .steps) : endpoint buy e perm i tag :=
  fundedEndpointCases mask first finish steps

run_cmd Lean.modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wideCalendarEndpointField"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_calendar_endpoint_reads"

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
