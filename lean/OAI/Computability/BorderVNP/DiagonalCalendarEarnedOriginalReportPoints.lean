import OAI.Computability.BorderVNP.DiagonalCalendarStoredReportPoint
import OAI.Computability.BorderVNP.DiagonalStoredReportPacking
import OAI.Computability.BorderVNP.DiagonalAttainedReportOperands
import OAI.Computability.BorderVNP.DiagonalOriginalFundedReportTerm
import OAI.Computability.BorderVNP.DiagonalPretypedFundedInputs
import OAI.Computability.BorderVNP.DiagonalCalendarCandidateOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCheckedFieldNativeWriter
import OAI.Computability.BorderVNP.DiagonalCalendarFundedDispatchOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarFundedDirectoryRoom
import OAI.Computability.BorderVNP.DiagonalCalendarFundedPrefixAt
import OAI.Computability.BorderVNP.DiagonalCalendarFundedCallWords
import OAI.Computability.BorderVNP.DiagonalCalendarFundedReportIntervals
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalCellDirectory
import OAI.Computability.BorderVNP.CellPacketGeometryOriginalReceiver
import OAI.Computability.BorderVNP.DiagonalCalendarLookupOriginalArgumentRanges
import OAI.Computability.BorderVNP.DiagonalCalendarFundedEmissionOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarMarkersOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarFundedGeometryOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalIssuedOpenParameters
import OAI.Computability.BorderVNP.DiagonalIssuedNetworkParameters
import OAI.Computability.BorderVNP.DiagonalIssuedOriginImage
import OAI.Computability.BorderVNP.DiagonalCalendarEmissionRowsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarFundedHostOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarFundedOwnerWordsOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarFundedWriterInputs
import OAI.Computability.BorderVNP.DiagonalCalendarWriterOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCalendarArgumentRoom
import OAI.Computability.BorderVNP.DiagonalCalendarArgumentScalars
import OAI.Computability.BorderVNP.DiagonalCalendarFundedPairCapacity
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedPlacement

/-! # Existence of a complete stored report at each original field and team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales TeamContraction ProcessorSlots
open VPVNP ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open FieldProcessor RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding RoutingISA.Pins VPVNP.BurstRAM RoutingISA.CompactMachine TeamSite
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open Diagonal.ExternalSew GridHosts
open scoped Classical BorderVNP.Epoch.Cube

open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
attribute [local instance] portFintype
attribute [local irreducible] Nat.clog UniversalMachine.programPrefix logWidth prefixCapacity
  FieldProcessor.freeWidth Fintype.equivFin
set_option maxRecDepth 8200
set_option maxHeartbeats 4400000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < «m»} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))

local notation "r₁" => stretch b.ρ (l+1)
local notation "size₁" => stretch b.σ (l+1)
local notation "R₁" => b.physical.teamsPred (l+1)
local notation "w₁" => b.physical.word (l+1)
local notation "ξ₁" => (scales.τ:ℝ)/5
local notation "ℓ₁" => TeamScales.link (ξ₁) (R₁+1) (l+1)
local notation "ec₁" => Wires.sortExponent (block (ξ₁) (l+1))
local notation "budget₁" => adv (adviceScale b.σ b.ρ (l+1))
local notation "pins₁" => (pairedTableParameters (l+1) (size₁)+2)*(budget₁+6)
local notation "d₁" => CoverScale.initialDepth (Cube D) (r₁) (l+1)-1
local notation "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "order₁" => (Fintype.equivFin (Fin axes → Deck (d₁+2))).symm
local notation3 (prettyPrint := false) "geo₁" => cal.sites.choose
local notation3 (prettyPrint := false) "prog₁" => cube.signedSiteProgram paid
local notation "a₁" => FieldProcessor.freeWidth (prog₁) scales.α 32 64 (r₁) (w₁) (l+1)
local notation "extra₁" => setupWidth (w₁+1) (l+1)+(prefixCapacity (r₁) 32 64 (w₁) (l+1)+1+a₁)
local notation3 (prettyPrint := false) "tape₁" => tapeTemplate (R:=R₁) (r:=r₁) (link:=ℓ₁) (regs:=64) (w:=w₁)
  (e:=ec₁) (width:=w₁+1) (k:=l) (a:=extra₁) (prog₁) (geo₁).fits (pins₁)

variable [configuredHeader : Fact (8 ≤ header)] (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1))
    (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "copies₁" => TeamScales.width (l+1) scales.α
local notation "tiles" => GridHosts.tileCount axes d₁
local notation "J₁" => (fan S)^T₁*tiles
local notation "description" => seedDescriptionWidth (l+1) (r₁) axes (d₁) (header*logWidth (r₁) (l+1))
  (BottomGridBank.bodyBudget (seedBoxCapacity (l+1) (r₁) axes (d₁) (Fintype.card (Direction axes))))
local notation "cap₁" => SeedPlan.profileReserve (r₁) (l+1)
local notation "ceiling₁" => geometryGateCeiling (8*(11920000+1500000+16008100*coeff+37)) (4*(E+2)) (r₁) (l+1)

variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

local notation3 (prettyPrint := false) "frameEntries(" vs ")" =>
  cal.frozenFrameEntries oper.grid qpos position chart reader chargeFit vs

open RoutingISA.Evaluator.SignedPrep _root_.OAI.Computability.BorderVNP.Cube

local notation3 (prettyPrint := false) "planner" =>
  cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit
open Packing.RoutingOutputs RoutingISA.Evaluator.ScheduleClock

local notation3 (prettyPrint := false) "layout₁" => cal.frozenLayout chart reader chargeFit
local notation3 (prettyPrint := false) "initial₁" => reader.startupArenaWith (n:=l+1) (reg:=64)
  prog₁ a₁ ℓ₁ (layout₁).header
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable oper.grid qpos position initial₁
local notation3 (prettyPrint := false) "issueDir" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest ((initial₁).next+7*(issueDir).candidates) cap₁ ((located₁).raw.reserve ceiling₁).size
    (located₁).outputs w₁

open RoutingISA.FragmentRows RoutingISA.SignedTaskArena
open Packing.Directory Packing.BundleDirectory Packing.RoutingOutputs
open RoutingISA.Evaluator.ScheduleClock RoutingISA.Evaluator.SignedPrep
open Lean Meta Elab Term in
/-- Apply the original funded program at the numeric indices of its checked
calendar, retaining the native cable and cell counts. -/
local elab "fundedSourceOfChecks% " count:ident checked:ident : term => do
  let entries := (← getLocalDeclFromUserName count.getId).toExpr
  let checks := (← getLocalDeclFromUserName checked.getId).toExpr
  let native ← nativeWriterOnCheckedRoutes checks
  let parameters := native.getAppArgs
  let plannerMethod := ``SignedCalendarAt.frozenPlannerTask
  let plannerInfo ← getConstInfo plannerMethod
  let planTerm := mkAppN (mkConst plannerMethod (plannerInfo.levelParams.map fun _ => .zero))
    (parameters.extract 0 (parameters.size-3))
  let cube ← mkProjection planTerm `cube
  let shape ← mkAppM ``Prod.mk #[← mkProjection cube `cables,← mkProjection cube `cells]
  let method := ``SignedCalendarAt.frozenFundedPrefixAt
  let signature ← getConstInfo method
  return mkAppN (mkConst method (signature.levelParams.map fun _ => .zero))
    ((parameters.extract 0 (parameters.size-1)) ++ #[entries,checks,shape])

open Lean Meta in
private def originalReportArgument (application : Expr) (name : Name) : MetaM Expr := do
  let mut signature ← inferType application.getAppFn
  for argument in application.getAppArgs do
    let .forallE field _ rest _ := signature | throwError "incomplete recorded report at {name}"
    if field == name then return argument
    signature := rest
  throwError "the recorded report has no {name} argument"

open Lean Meta Elab Term in
/-- Read the supply or private widths from the cells in the emitter's own
prepared input. Both functions read its recorded publication RAM. -/
local elab "capturedReportWidth% " prepared:ident column:ident : term => do
  let record := (← getLocalDeclFromUserName prepared.getId).toExpr
  let original := mkProj ``And 0 record
  let some input ← whnfUntil (← inferType original) ``DiagonalTallyCellReports.PreparedReportInput
    | throwError "expected the original prepared report input"
  let rows ← originalReportArgument input `cs
  let some selected ← whnfUntil rows ``DiagonalTallyCellReports.ReportDirectory.sourceCells
    | throwError "expected the original selected report cells"
  originalReportArgument selected column.getId

open Lean Meta in
private def originalFundedImage (packet : Expr) : MetaM Expr := do
  let some image ← whnfUntil (← inferType packet) ``SignedCalendarAt.frozenPacketImage
    | throwError "expected the packet image of this funded source"
  return image

open Lean Elab Term Meta in
/-- Read the source RAM from the actual packet or allocation already held by this
field's writer. Both memories precede publication and the sparse report. -/
local elab "fundedSiteMemory% " data:term:max key:ident : term => do
  let source ← elabTerm data none
  let left := fun (v : Expr) => mkProj ``And 0 v
  let right := fun (v : Expr) => mkProj ``And 1 v
  let held := left source
  match key.getId.eraseMacroScopes with
  | `profile =>
    let packet := left (right (right held))
    let image ← originalFundedImage packet
    let some raw ← whnfUntil image.getAppArgs.back! ``RoutingISA.readings
      | throwErrorAt data "expected the registered original geometry RAM readings"
    return raw.getAppArgs.back!
  | `middle =>
    let resident := right (right (right (left held)))
    let some evidence ← whnfUntil (←inferType resident) ``Nonempty
      | throwErrorAt data "expected the reached native writer"
    let some slot ← whnfUntil evidence.getAppArgs[0]! ``RoutingISA.Evaluator.SlottedWriter
      | throwErrorAt data "expected the original slotted writer"
    originalReportArgument slot `slotted
  | _ => throwErrorAt key "expected profile or middle"


open Lean Elab Meta Term in
/-- Read the native funded writer directly on a packet that retains the complete
calendar, history and reached RAM. -/
local elab "fundedInputsAtPacket% " input:term:max : term => do
  let packet ← elabTerm input none
  let image ← originalFundedImage packet
  let constructor := Lean.mkConst ``SignedCalendarAt.frozenFundedWriterInputs image.getAppFn.constLevels!
  return mkProj ``PLift 0 (mkAppN constructor (image.getAppArgs.push packet))


open Lean Meta Elab Term in
private def atOriginalReportEmission (service : Ident) (input : Array Ident) : TermElabM Expr := do
  let fn := (← getLocalDeclFromUserName service.getId).toExpr
  let operandsAt ← input.mapM fun x => do
    return (← getLocalDeclFromUserName x.getId).toExpr
  return mkAppN fn operandsAt

open Lean Meta Elab Term in
/-- Apply the six native dispatch observations at their actual fit, cell count
and sparse emission. The final pointer belongs to this same geometry. -/
local elab "paidOriginalPrepared% " family:ident f:ident u:ident fit:ident cells:ident e:ident geometry:ident : term => do
  let atEmission ← atOriginalReportEmission family #[f,u,fit,cells,e]
  let geo := (← getLocalDeclFromUserName geometry.getId).toExpr
  let some original ← whnfUntil (← inferType geo) ``RoutingISA.Evaluator.SignedPrep.IssuedGeometry
    | throwError "expected the original issued geometry"
  let pointer := mkAppN (Lean.mkConst ``RoutingISA.Evaluator.SignedPrep.IssuedGeometry.pointer original.getAppFn.constLevels!)
    (original.getAppArgs.push geo)
  return mkApp atEmission pointer

open Lean Meta Elab Term in
/-- Read the paid row numbers at the same original field, team, fit, cell
count and emission as the prepared source. -/
local elab "paidOriginalRows% " family:ident f:ident u:ident fit:ident cells:ident e:ident : term =>
  atOriginalReportEmission family #[f,u,fit,cells,e]

open Lean Meta Elab Term in
/-- Read the host certified on this same original field and team. -/
local elab "paidOriginalHost% " family:ident f:ident u:ident : term =>
  atOriginalReportEmission family #[f,u]

open Lean Meta Elab Term in

/-- Use the calibrated sources, row count and admitted route already indexed
by the given original funded reader. -/
private def originalSourceIntervals (source oper field team : Expr) : MetaM Expr := do
  let some issuedTerm ← whnfUntil source ``SignedCalendarAt.frozenFundedPrefixAt
    | throwError "expected the original frozen source"
  let parameters := issuedTerm.getAppArgs
  let data ← getConstInfo ``SignedCalendarAt.frozenFundedPrefixAt
  let valueIndex ← forallBoundedTelescope data.type (some parameters.size) fun xs _ => do
    let some i ← xs.findIdxM? (fun x => return (← x.fvarId!.getUserName) == `values)
      | throwError "missing the original matrices"
    return i
  let hist := mkProj ``Sigma 0 (mkProj ``Sigma 1 field)
  let route := mkProj ``Sigma 0 (mkProj ``Sigma 1 (mkProj ``Sigma 1 field))
  let operation ← mkConstWithLevelParams ``SignedCalendarAt.frozenFundedReportIntervals
  return mkAppN operation ((parameters.extract 0 valueIndex) ++ #[
    ← mkProjection oper `funding,parameters[valueIndex]!,hist,route,team])

open Lean Meta Elab Term in
local elab "siteIntervalsAtOriginal%" source:ident oper:ident field:ident team:ident : term => do
  let get (x : Ident) := do return (← getLocalDeclFromUserName x.getId).toExpr
  let src ← getLocalDeclFromUserName source.getId
  originalSourceIntervals (src.value?.getD src.toExpr) (← get oper) (← get field) (← get team)


open Lean Meta Elab Term in
/-- Read each cell’s original private-wire count and the placed directory at
the issued header width on the marker’s own packet. -/
local elab "originalDirectoryRows% " marked:term:max headerSize:term:max : term => do
  let packet ← elabTerm marked none
  let image ← originalFundedImage packet
  let method ← mkConstWithLevelParams ``SignedCalendarAt.frozenOriginalDirectory_returned
  let rows := mkAppN method (image.getAppArgs.push packet)
  let width ← elabTerm headerSize (some (Lean.mkConst ``Nat))
  forallBoundedTelescope (← inferType rows) (some 1) fun cells _ => do
    let row := mkApp rows cells[0]!
    let wires := mkProj ``And 0 row
    let placed := mkApp (mkProj ``And 1 row) width
    let facts := mkAppN (Lean.mkConst ``And.intro) #[← inferType wires,← inferType placed,wires,placed]
    mkLambdaFVars cells facts

open Lean Meta Elab Term in
/-- Take the two explicit arguments of the original funded reader directly
from the recorded field and receiving team. -/
local elab "fundedReaderAt% " source:ident field:ident team:ident : term => do
  let reader := (← getLocalDeclFromUserName source.getId).toExpr
  let recorded := (← getLocalDeclFromUserName field.getId).toExpr
  let receiver := (← getLocalDeclFromUserName team.getId).toExpr
  return mkApp2 (mkProj ``PLift 0 reader) recorded receiver

open Lean in
/-- Use the kernel projection on the original proof. The two proposition
parameters of the projection function can be read from this proof's type. -/
private partial def originalAndProjection (e : Expr) : Expr :=
  if e.isAppOfArity ``And.left 3 then
    mkProj ``And 0 (originalAndProjection e.appArg!)
  else if e.isAppOfArity ``And.right 3 then
    mkProj ``And 1 (originalAndProjection e.appArg!)
  else e

open Lean in
private def compactOriginalProjections (e : Expr) : Expr :=
  e.replace fun part =>
    if part.isAppOfArity ``And.left 3 || part.isAppOfArity ``And.right 3 then
      some (originalAndProjection part)
    else none

open Lean Meta Elab Term in
/-- Read a component of a recorded conjunction without rebuilding either proposition. -/
local elab "sourceConjunct% " data:ident side:ident : term => do
  let term := (← getLocalDeclFromUserName data.getId).toExpr
  match side.getId.eraseMacroScopes with
  | `left => return mkProj ``And 0 term
  | `right => return mkProj ``And 1 term
  | _ => throwError "expected the left or right conjunction field"

open Lean Meta Elab Term in
/-- Keep the physical input expression using kernel projections on conjunctions. -/
local elab "compactIssuedInput% " input:term:max : term =>
  return compactOriginalProjections (← elabTerm input none)

open Lean Meta Elab Term in
/-- Store the actual issued report as the witness of the stated original site. -/
local elab "storedPointWitness% " report:ident : term <= expected => do
  let some inhabited ← whnfUntil expected ``Nonempty
    | throwError "expected existence of a stored report at this point"
  let site := inhabited.appArg!
  let receipt := (← getLocalDeclFromUserName report.getId).toExpr
  let recorded ← SignedCalendarAt.packEarnedOriginalReportAt receipt site
  synthesizeSyntheticMVarsNoPostponing
  let witness ← instantiateMVars <|
    mkApp2 (Lean.mkConst ``Nonempty.intro inhabited.getAppFn.constLevels!) site recorded
  if witness.hasMVar || witness.hasSorry then throwError "incomplete original stored report"
  return ShareCommon.shareCommon witness

set_option maxRecDepth 23000 in
set_option maxHeartbeats 24000000 in
set_option cleanup.letToHave false in
private noncomputable def originalStoredPointRequirement
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed)
    (f : nativeCheckedFieldType% (cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h reports))
    (u : Fin (R₁+1)) : Prop :=
  let _room := configuredHeader
  Nonempty (cal.StoredReportPointOnOriginalInputs oper qpos position chart reader chargeFit values h reports f u)

open Lean Meta Elab Term in
/-- Reconnect the fresh calendar parameters to their section identifiers.
Local notation in the numerical program carries those identifiers from its declaration. -/
private def withOriginalSectionBinders {α : Type} (inputs : Array Expr) (execute : TermElabM α) :
    TermElabM α := do
  let context ← readThe Term.Context
  let mut bound := context.sectionFVars
  for input in inputs do
    let name := (← input.fvarId!.getDecl).userName.eraseMacroScopes
    if let some uid := context.sectionVars.find? name then
      bound := bound.insert uid input
  withReader (fun ctx : Term.Context => {ctx with sectionFVars := bound}) execute

open Lean Meta Elab Term in
/-- Elaborate the physical data under their original local definitions, then close
the actual witness and all its bindings together. -/
private partial def closeOriginalStoredBindings (syntaxTerm : Syntax) (expected : Expr)
    (parameters locals : Array Expr) : TermElabM Expr := do
  match syntaxTerm with
  | `(term| let $id:ident := $rhs; $rest) =>
    let value ← elabTerm rhs none
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    if value.hasMVar || value.hasSorry then throwErrorAt rhs "incomplete original let binding {id.getId}"
    let type ← instantiateMVars (← inferType value)
    let (type,value) := ShareCommon.shareCommon' (type,value)
    withLetDecl id.getId type value fun localExpr =>
      closeOriginalStoredBindings rest expected parameters (locals.push localExpr)
  | _ =>
    let native ← elabTerm syntaxTerm (some expected)
    synthesizeSyntheticMVarsNoPostponing
    let native ← instantiateMVars native
    if native.hasMVar || native.hasSorry then throwErrorAt syntaxTerm "incomplete result after the original bindings"
    let actual ← mkLambdaFVars locals native (generalizeNondepLet := false)
    let fn ← mkLambdaFVars parameters (compactOriginalProjections actual)
    if fn.hasFVar || fn.hasMVar || fn.hasSorry then throwErrorAt syntaxTerm "the closed proof retained an input"
    return ShareCommon.shareCommon fn

open Lean Meta Elab Command Term in
/-- Bind the calibrated parameters and original physical field and team once.
The stock kernel checks the entire original point proof when adding the theorem. -/
local elab "originalStoredPointTheorem " target:ident " from " claim:ident " using " body:term : command => do
  let name := (← getCurrNamespace) ++ target.getId.eraseMacroScopes
  let source ← getRef
  liftTermElabM do
    let predicate ← realizeGlobalConstNoOverloadWithInfo claim
    let info ← getConstInfo predicate
    withLCtx {} {} <| forallTelescope info.type fun inputs _ => do
      let names ← (inputs.extract (inputs.size-5) inputs.size).mapM fun a => do
        return (← a.fvarId!.getDecl).userName.eraseMacroScopes
      unless inputs.size==55 && names==#[`values,`h,`reports,`f,`u] do
        throwError "unexpected original calendar point arguments {inputs.size}, {names}"
      let required := mkAppN (Lean.mkConst predicate (info.levelParams.map Level.param)) inputs
      let some point ← whnfUntil required ``Nonempty | throwError "expected the original native point existence claim"
      let value ← withOriginalSectionBinders inputs <| Term.withoutErrToSorry <|
        closeOriginalStoredBindings body point inputs #[]
      let type ← mkForallFVars inputs point
      let (type,value) := ShareCommon.shareCommon' (type,value)
      unless !type.hasFVar && !value.hasFVar do throwError "an original operand escaped the calendar"
      addDecl (.thmDecl {name, levelParams := info.levelParams, type, value})
  addDeclarationRangesFromSyntax name source target
  addDocStringCore name "The issued report supplies its stored source and all funded facts at this original field and team."

set_option maxRecDepth 23000 in
set_option maxHeartbeats 24000000 in
set_option cleanup.letToHave false in
set_option Elab.async false in
originalStoredPointTheorem SignedCalendarAt.existsStoredPointOnOriginalReports from originalStoredPointRequirement using
  let entries := frameEntries(values)
  let checks := cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let found := cal.reportedCandidateOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let source := fundedSourceOfChecks% entries checks
  let earn := cal.frozenPrivateFunding oper.grid qpos position chart reader chargeFit oper.funding
  let prices := earn.2.2.2
  let clocks := prices.2.2
  let physical := cal.fundedEmissionOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let markers := cal.fundedMarkersOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let sparseRows := cal.fundedEmissionRowsOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let hosts := cal.fundedHostOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let ownerWords := cal.fundedOwnerWordsOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let writer := cal.writerOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let geometry := cal.fundedGeometryOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let openFields := cal.fundedOpensOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let dispatch := cal.fundedDispatchOnOriginalReports oper qpos position chart reader chargeFit values h reports
  let small := cal.frozenArgumentScalars oper.grid qpos position chart reader chargeFit oper.routing
  let size := cal.frozenArgumentPublicationRoom oper.grid qpos position chart reader chargeFit oper.routing
  let directoryRoom := cal.frozenFundedDirectoryRoom oper.grid qpos position chart reader chargeFit oper.routing
  let headerSize := cal.frozenIssuedReportFields oper.grid qpos position chart reader chargeFit
  let returned := found f
  let U := attainedStarts% (returned.2)
  let active := attainedPrefix% (returned.2)
  let issued := physical f u
  let fit := issued.2.choose
  let cellCount := issued.2.choose_spec.choose
  let e := issued.2.choose_spec.choose_spec.choose
  let traced := issued.2.choose_spec.choose_spec.choose_spec
  let pos := returned.1
  let bank := pos.choose u
  let digits := pos.choose_spec.choose u
  let raw := SignedPrep.routeBroadcast (planner).cube _ f.2.2.1.val
  let decl := decodedBroadcast (planner).cube raw.val
  let writerData := writer f u
  let held := sourceConjunct% writerData left
  let slotted := compactIssuedInput% (held.1.2.2.2.some)
  let profileRAM := fundedSiteMemory% writerData profile
  let placedRAM := fundedSiteMemory% writerData middle
  let net := compactIssuedInput% (fundedInputsAtPacket% (held.2.2.1))
  let marked := compactIssuedInput% ((markers f u).1)
  let geom := geometry f u
  let opened := openFields f u
  let prepared := paidOriginalPrepared% dispatch f u fit cellCount e geom
  let positions := paidOriginalRows% sparseRows f u fit cellCount e
  let total := positions.choose
  let rows := positions.choose_spec.choose_spec.choose
  let atRow := positions.choose_spec.choose_spec.choose_spec
  let words := ownerWords f u
  let ownerReturn := sourceConjunct% words right
  let head := ((U u).pub 0).val
  let tabs := bases origin₁ (planner).cube.cables (planner).cube.cells J₁
  let arrived := (R₁+1)*tiles
  let rank := cal.frozenPlannerReportRankInputs oper.grid qpos position chart reader chargeFit values f.2.1
    marked u.val head tabs.ends tabs.livePairs arrived
  let ranges := size.2.2
  let packetLabel := cal.frozenFundedPacketLabel oper.grid qpos position chart reader chargeFit values f.2.1
  let ownedSlots := cal.frozenFundedPairCapacity oper.grid qpos position chart reader chargeFit values f.2.1
  let g := cal.frozenOriginalGeometry oper.grid qpos position chart reader chargeFit values f.2.1
  let pub := cal.frozenFundedCallWords oper.grid qpos position chart reader chargeFit values f.2.1 marked
  let bounded := siteIntervalsAtOriginal% source oper f u
  let sourceBounds := cal.frozenFundedBoxBounds oper.grid qpos position chart reader chargeFit values f.2.1
  let hosted := cal.frozenOriginalGeometry_hosts oper.grid qpos position chart reader chargeFit values f.2.1
  let paidHost := paidOriginalHost% hosts f u
  let nativeRow := originalDirectoryRows% (marked.1) (header*logWidth r₁ (l+1))
  let readerAtTeam := fundedReaderAt% source f u
  let packet := compactIssuedInput% (originalFundedTypedInputs% (readerAtTeam (readings profileRAM)
    (issuedNetworkField% (net.1) edgeID) (issuedNetworkField% (net.1) portID)
    (issuedNetworkField% (net.1) F) (issuedNetworkField% (net.1) x)
    (issuedNetworkField% (net.1) aux) small.1 (initial₁).next
    profileRAM placedRAM packetLabel decl
    bank (fun c => (planner).cube.cellBank+c*(planner).cube.cellStride)
    (capturedReportWidth% prepared supply) (capturedReportWidth% prepared privateWidth) digits
    (bound:=issuedOpenBits% opened) (args:=pub.words) (out:=pub.published) (addresses:=pub.addresses) (intervals:=bounded.1)
    (numeric:=fun i => (sourceBounds i).1) (boxRoom:=fun i => (sourceBounds i).2.1)
    (widths:=fun i => (sourceBounds i).2.2) (hw:=clocks.1) (hW:=clocks.2.1)
    (scratch:=clocks.2.2.1) (burst:=clocks.2.2.2) (hm:=hm) (hr:=stretch_one ..)
    (short:=earn.1.short) (gpos:=earn.1.gadgets) («ids»:=earn.2.1)
    (occupied:=fun x => _root_.OAI.Computability.BorderVNP.Cube.Physical.NativeAssignments.CoreDirectory.owner_site _ x)
    (scale:=by simpa only [one_mul] using earn.1.scale) (scheduled:=prices.1) («digits»:=prices.2.1)
    (returned:=nativeRow)
    (grammarOrder:=ord) (originalHost:=hosted)
    (originals:=fun c j hmem => (hosted j).symm.trans ((g.original_receiver c j).mp hmem))
    (fragmentFit:=fit) (pointer:=geom.pointer) (place:=geom.placement) (sparseGeometry:=traced.2.2.1)
    (cc:=cellCount.symm) (limit:=opened.limit) (geometry:=geom.geometry) (fromControls:=geom.body)
    (frameEq:=opened.frameEq) (sorted:=rank.1) (padded:=rank.2.1) (stops:=cal.frozenFundedOriginalStops oper.grid qpos position chart reader chargeFit values f.2.1
      marked u.val head tabs.ends tabs.livePairs arrived)
    (tableRoom:=rank.2.2.2.1) (ranks:=rank.2.2.2.2.1) (ordered:=rank.2.2.2.2.2)
    (controls:=opened.scanRoom) (image:=geom.grouped) (emission:=e) (size:=total) (ordinal:=atRow.2.2.2.2)
    (beforeHeader:=opened.beforeHeader) (headerWidth:=opened.headerWidth) (fromHost:=paidHost)
    (rows:=rows) (rowOrder:=atRow.1) (rowScheduled:=atRow.2.1) (incomingWidth:=atRow.2.2.1)
    (atBank:=traced.1) (atMemory:=traced.2.1) (outer:=geom.fields) (word:=geom.wordWidth) (callLimit:=geom.callLimit)
    (taskAt:=geom.tasks) (controlWords:=traced.2.2.2)
    (fieldHeader:=issuedOpenHeader% opened) (openRoom:=opened.openRoom)
    (openPlace:=opened.openPlace) (openReady:=opened.openReady) (ownedWord:=words.1) (restored:=atRow.2.2.2.1)
    (assignment₀:=ownerReturn.choose) (observed₀:=ownerReturn.choose_spec.2.1)
    (ownerWord₀:=ownerReturn.choose_spec.2.2) (writer:=slotted)
    (wordTeams:=ranges.1) (wordProcs:=ranges.2.1) (wordFields:=ranges.2.2.1) (wordLiteral:=ranges.2.2.2.1)
    (wordCells:=directoryRoom.wordCells) (wordStride:=directoryRoom.wordStride) (portWidth:=fun _ => rfl)
    (repNet:=net.1) (idsNet:=net.2.1) (fieldFitNet:=net.2.2.1)
    (routingImage:=(net.2.2.2).atIssuedOrigin
      (cal.frozenIssuedPlacement oper.grid qpos position chart reader chargeFit).2.2.1)
    (placement:=held.1.2.2.1) (privateFits:=held.1.2.1) (headerAt:=held.2.1)
    (reserved:=directoryRoom.reserved) (low:=directoryRoom.low) (originFit:=directoryRoom.originFit) (keep:=writerData.2)
    (literalPos:=directoryRoom.literalPos) (shortDescription:=directoryRoom.shortDescription) (pairBound:=ownedSlots)
    prepared.1 prepared.2.1 prepared.2.2.1 prepared.2.2.2.1 prepared.2.2.2.2.1 prepared.2.2.2.2.2))
  let report := originalFundedReport% source f.2.1 planner U u (active u) e packet rows prepared.1
    traced.1 headerSize.1.symm g.directory
  storedPointWitness% report

set_option maxRecDepth 23000 in
set_option maxHeartbeats 24000000 in
include configuredHeader in
/-- Choose the complete family of earned reports supplied by the original lookup service. -/
noncomputable def SignedCalendarAt.earnedStoreOnOriginalReports
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    cal.StoredReportsAtOriginalInputs oper qpos position chart reader chargeFit values h reports :=
  cal.storedReportsFromOriginalPoints oper qpos position chart reader chargeFit values h reports
    (cal.existsStoredPointOnOriginalReports oper qpos position chart reader chargeFit values h reports)

end Diagonal

end BorderVNP
end Computability
end OAI
