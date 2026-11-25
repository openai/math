import OAI.Hierarchy.TaggedWideSelectedWindowBounds
import OAI.Hierarchy.TaggedWideFundedSelectedOutput
import OAI.Hierarchy.TaggedWideCalendarTerminalPins
import OAI.Hierarchy.TaggedWideOriginalCalendarPrice

namespace OAI
/-! # The actual selected signed-site CPU yields the compiler run -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open TaggedPrune Tagged.WideControlJoin
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option cleanup.letToHave false
set_option pp.maxSteps 200
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "wide_calendar_evaluates"
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
local notation "pathReportOf" π:arg j:arg => v.wide_reported_path h width S π seed cpu.age cpu.ready.credit cpu.ready.size_le
  Sfit support.size.late support.size.words j
variable (sourceRows : ∀π j,reportGeometry π (Z.reported π j)=reportGeometry π (pathReportOf π j))
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

open Lean Meta in
private def calendarRegisteredApp (declaration registeredHead registeredBinder : Lean.Name)
    (proof : Lean.Expr) (fixed : Array (Lean.Name × Lean.Expr)) : Lean.Meta.MetaM Lean.Expr := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let body ← inferType proof
  let some exposed ← whnfUntil body registeredHead | throwError "expected {registeredHead} in {body.getAppFn}"
  forallTelescope (← inferType constant) fun args _ => do
    let some binder ← args.findM? (fun x => do return (← x.fvarId!.getUserName) == registeredBinder) |
      throwError "missing registration binder {registeredBinder}"
    let type ← inferType binder
    let some pattern ← whnfUntil type registeredHead | throwError "registration pattern has head {type.getAppFn}"
    let alignedArgs := pattern.getAppArgs.zip exposed.getAppArgs
    let values ← args.mapM fun a => do
      let name ← a.fvarId!.getUserName
      if name == registeredBinder then return proof
      if let some (_,x) := fixed.find? (fun (n,_) => n == name) then return x
      if let some (_,x) := alignedArgs.find? (fun (f,_) => f == a) then return x
      throwError "missing {declaration} input {name}"
    return mkAppN constant values

open Lean Elab Command Term Meta in
local elab "defineCalendarEndpointReads " body:term : command => do
  let publicName := (← getCurrNamespace) ++ `wideCalendarEndpointReads
  runTermElabM fun context => do
    let result ← withoutErrToSorry <| elabTerm body none
    synthesizeSyntheticMVarsNoPostponing
    let closed ← mkLambdaFVars context (← instantiateMVars result) (usedOnly := true)
    let value ← Term.levelMVarToParam closed
    let type ← instantiateMVars (← inferType value)
    if value.hasFVar || value.hasMVar || value.hasSorry || type.hasFVar || type.hasMVar || type.hasSorry then
      throwError "the selected endpoint predicate is not closed"
    let levels := (collectLevelParams {} type).params.toList
    addDecl (.defnDecl {
      name := publicName
      levelParams := levels
      type := type
      value := value
      hints := .regular 1
      safety := .safe
    })
    addDocStringCore publicName "The four endpoint readings at the selected paid return."

defineCalendarEndpointReads (show Prop from by
    let window := windowAt
    let agreed := joinedRows
    let activeSites := sites
    let bits := record
    run_tac Lean.Elab.Tactic.withMainContext do
      let win ← Lean.Meta.getFVarFromUserName `window
      let inputs ← #[ (`a, `activeSites), (`room, `room), (`cpu, `cpu), (`N, `N),
        (`perm, `perm), (`i, `i), (`same, `agreed), (`ex, `e), (`sel, `bits) ].mapM
        fun (n,vname) => do return (n, ← Lean.Meta.getFVarFromUserName vname)
      let out ← calendarRegisteredApp ``FundedCutRows.EndpointFacts ``FundedCutRows.WindowReceipt `_image win inputs
      (← Lean.Elab.Tactic.getMainGoal).assign out
      Lean.Elab.Tactic.replaceMainGoal [])


local notation "endpoint" => v.wideCalendarEndpointReads (C:=C) m ell short u δ ξ x cpu room control support
  Z sourceRows prices pricePos groupsFit metadata lanesFit

theorem wide_calendar_evaluates
    (read : ∀(items : Buy) (ext : Ex→Bool) (p : Equiv.Perm (Tagged.Row h)) (rank : Fin ((rout).count p)) tagAt,
      endpoint items ext p rank tagAt) :
    (sites).Evaluates room C := by
  apply SignedSites.evaluates_from_selected (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short)
    (unitCost:=unit) (cpu:=cpu) (a:=sites) (room:=room) (C:=C)
  intro buy e s choice
  rcases choice with ⟨perm,i⟩
  intro matched
  let j := (Fintype.equivFin (Path sl es (base perm))).symm i
  have selector : s=CalendarTape.encode sl es (base perm) j := matched.2
  have tag : (perm : Tagged.Row h→Tagged.Row h)=Tagged.tag (fun n=>e (.inl n)) := matched.1
  subst s
  let returned := v.wide_selected_local_return m ell short u δ ξ unit x cpu v.calendarUnit_rate support
    prices pricePos buy groupsFit metadata lanesFit e perm tag j
  let ending:=returned.2.2.2
  let bound := v.wide_selected_private_bounds m ell short u δ ξ unit x cpu v.calendarUnit_rate support perm j
  let siteReceipt := read buy e perm i tag
  refine ⟨ending.choose, ?_⟩
  let didRun := ending.choose_spec.2.1
  let flagRead := ending.choose_spec.2.2.1
  let lowRead := ending.choose_spec.2.2.2.1
  let widths := bound.1
  let wordFit := bound.2
  run_tac Lean.Elab.Tactic.withMainContext do
    let rc ← Lean.Meta.getFVarFromUserName `siteReceipt
    let given ← #[ (`ran, `didRun), (`nativeFlag, `flagRead), (`low, `lowRead),
      (`widths, `widths), (`wordFit, `wordFit), (`site, `siteReceipt) ].mapM
      fun (n,localName) => do return (n, ← Lean.Meta.getFVarFromUserName localName)
    let out ← calendarRegisteredApp ``FundedCutRows.selected_output ``FundedCutRows.EndpointFacts `site rc given
    (← Lean.Elab.Tactic.getMainGoal).assign out
    Lean.Elab.Tactic.replaceMainGoal []

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
