import OAI.Computability.BorderVNP.DiagonalCalendarLookupReportTests
import OAI.Computability.BorderVNP.DiagonalCalendarLookupFragmentRoom
import OAI.Computability.BorderVNP.DiagonalCalendarLookupReportTaskImage
import OAI.Computability.BorderVNP.DiagonalCalendarLookupSiteMarkers
import OAI.Computability.BorderVNP.DiagonalCalendarMarkedArgumentInput
import OAI.Computability.BorderVNP.DiagonalReportedEndAddressTerm
import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations
import OAI.Computability.BorderVNP.DiagonalOriginalIssuedGeometryTerm
import OAI.Computability.BorderVNP.DiagonalOriginalReportFrameTerm
import OAI.Computability.BorderVNP.DiagonalSelectedCalendarObservation
import OAI.Computability.BorderVNP.DiagonalSelectedLookupFrameFields
import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections

/-! # The native argument scanner before the returning report emission -/

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
local notation "tiles" => GridHosts.tileCount axes (d₁)
local notation3 (prettyPrint := false) "order₁" => (Fintype.equivFin (Fin axes → Deck (d₁+2))).symm
local notation3 (prettyPrint := false) "geo₁" => cal.sites.choose
local notation3 (prettyPrint := false) "prog₁" => cube.signedSiteProgram paid
local notation "a₁" => FieldProcessor.freeWidth (prog₁) scales.α 32 64 (r₁) (w₁) (l+1)
local notation "extra₁" => setupWidth (w₁+1) (l+1)+(prefixCapacity (r₁) 32 64 (w₁) (l+1)+1+a₁)
local notation3 (prettyPrint := false) "tape₁" => tapeTemplate (R:=R₁) (r:=r₁) (link:=ℓ₁) (regs:=64) (w:=w₁)
  (e:=ec₁) (width:=w₁+1) (k:=l) (a:=extra₁) (prog₁) (geo₁).fits (pins₁)

variable (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "copies₁" => TeamScales.width (l+1) scales.α
local notation "J₁" => (fan S)^T₁*tiles
local notation "description" => seedDescriptionWidth (l+1) (r₁) axes (d₁) (header*logWidth (r₁) (l+1))
  (BottomGridBank.bodyBudget (seedBoxCapacity (l+1) (r₁) axes (d₁) (Fintype.card (Direction axes))))
local notation "cap₁" => SeedPlan.profileReserve (r₁) (l+1)
local notation "ceiling₁" => geometryGateCeiling (8*(11920000+1500000+16008100*coeff+37)) (4*(E+2)) (r₁) (l+1)
local notation3 (prettyPrint := false) "dir₁" => freeDirectory (R₁) (r₁)
  ((tape₁).program.length+(cutWidth (l+1)+extra₁)) (ℓ₁) tiles (GridHosts.inputBlockWidth (r₁) (l+1) axes (d₁)) J₁ description

variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)


local notation3 (prettyPrint := false) "layout₁" => cal.frozenLayout chart reader chargeFit
local notation3 (prettyPrint := false) "initial₁" => reader.startupArenaWith (n:=l+1) (reg:=64)
  (prog₁) (a₁) (ℓ₁) (layout₁).header
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable oper.grid qpos position (initial₁)
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "number₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "free₁" => (selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute tape₁ order₁ position Unit).choose
local notation3 (prettyPrint := false) "arenaBase" =>
  Allocation.stop ((initial₁).next+7*(dir₁).candidates) cap₁ ceiling₁ (located₁).outputs w₁ w₁
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit

local notation3 (prettyPrint := false) "bounds₁" => cal.frozenSpliceBounds oper.grid
local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation "qdim" => pairedTableParameters (l+1) size₁+Fintype.card identifiers

open JointHeader Routing RoutingISA.Evaluator.SignedPrep CellEntries
local notation3 (prettyPrint := false) "planner₁" => cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "elig(" vs "," hist ")" =>
  (plan₁).signedBroadcastAllowed prog₁ (geo₁).fits W₁ position tag₁ sites₁ edges₁ ports₁ vs
    ((geoSeed).eval x₁) (leaf(vs)).property free₁ oper.grid.count (bounds₁).2.1 hist cube scales.α ξ₁
    (bounds₁).1 (geo₁).literalSize (bounds₁).2.2 number₁ (selectedTask).p arenaBase cap₁

open CellPacketGeometry CellPacketGeometry.History CellPacketGeometry.History.Native
open Packing.RoutingOutputs DiagonalTallyCellReports DiagonalTallyAllocation ReportDirectory

open Lean Meta Elab Term in
/-- Use the report layout and cell banks recorded by this exact seed and allocation. -/
local elab "nativeReturnedReportFrame% " family:term:max seed:term:max alloc:term:max : term => do
  let applyRoom ← elabTerm family none
  let prepared ← elabTerm seed none
  let allocation ← elabTerm alloc none
  let some tape ← whnfUntil (← inferType prepared) ``PreparedReportInput | throwError "expected prepared report RAM"
  let some report ← whnfUntil (← inferType allocation) ``ReportAllocation | throwError "expected the original report layout"
  let indices := report.getAppArgs
  unless indices.size == 6 do throwError "unexpected layout arity {indices.size}"
  let bank := indices[2]!
  let bankPointer ← mkProjection bank `bankStart
  let complete := mkAppN applyRoom #[indices[3]!, indices[4]!, indices[5]!, bank, tape.getAppArgs.back!,
    prepared, allocation, ← mkEqRefl bankPointer]
  return .proj ``And 0 complete

open Lean Meta Elab Term in
/-- Apply the native argument scanner to the reported machine, the issued geometry
and the exact three end-address parameters already measured at that return. -/
local elab "startAtOriginalReport%" initializer:ident "with" "[" terms:term,* "]" : term => do
  let init ← elabTerm (← `(@$initializer)) none
  let arguments ← terms.getElems.mapM fun t => elabTerm t none
  let #[team, marked, report, seed, allocation, geometry, fragment, bounded, cells, cables, rows, limit] := arguments
    | throwError "expected twelve returned report and scanner operands"
  let some ret ← whnfUntil (← inferType report) ``BorderVNP.RoutingISA.Evaluator.Returns | throwError "expected the actual report return"
  let #[_, _, pub, mac, bank, mem] := ret.getAppArgs | throwError "expected the original RAM configuration"
  let some allocatedRows ← whnfUntil (← inferType allocation) ``ReportAllocation
    | throwError "expected the allocated native report"
  let #[_, _, banks, layout, reports, cursor] := allocatedRows.getAppArgs | throwError "expected six report indices"
  let some issued ← whnfUntil (← inferType geometry) ``SignedPrep.IssuedGeometry
    | throwError "expected the actual issued geometry"
  let #[_, _, _, _, _, _, _, _, profileRam, nativeSourceRam, _, _] := issued.getAppArgs
    | throwError "expected the source and reported RAM in the issued geometry"
  let #[_, _, addressOne, addressTwo, addressThree] ← reportedEndAddressOperands limit
    | throwError "expected three end-address parameters"
  let pointer ← mkProjection banks `bankStart
  return mkAppN init #[team, profileRam, marked, pub, mac, bank, mem, report, banks, layout, reports, cursor,
    nativeSourceRam, addressOne, addressTwo, addressThree, seed, allocation, ← mkEqRefl pointer,
    geometry, fragment, bounded, cells, cables, rows, limit]

private def retainReportedArgument (target required : Prop) (onEmission : required → target) :
    PSigma (fun paid : Prop => paid → target) :=
  ⟨required, onEmission⟩

open Lean Meta Elab Term Tactic in
/-- Abstract the final row-emission proof over the state of the original returning report. -/
local elab "retainOriginalReport% " goalType:term " using " steps:tacticSeq : term => do
  let claim ← elabTerm goalType (some (mkSort .zero))
  let initial ← getLCtx
  let assumptionType ← mkFreshExprMVar (mkSort .zero)
  withLocalDeclD `providedInput assumptionType fun provider => do
    let probe ← mkFreshExprSyntheticOpaqueMVar claim
    let [remaining] ← Tactic.run probe.mvarId! (evalTactic steps) | throwError "expected one remaining input"
    remaining.withContext do
      let lctx ← getLCtx
      let mut locals := #[]
      let mut parameters := #[]
      for declaration in lctx do
        if declaration.fvarId == provider.fvarId! || initial.contains declaration.fvarId then continue
        locals := locals.push declaration.toExpr
        if !declaration.isLet then parameters := parameters.push declaration.toExpr
      let target ← instantiateMVars (← remaining.getType)
      let some actual ← whnfUntil target ``CellPacketGeometry.History.Native.ReportArgumentEmission
        | throwError "expected the native report emission"
      let run := (← getLocalDeclFromUserName `run).toExpr
      let emission := (← getLocalDeclFromUserName `emission).toExpr
      unless actual.getAppArgs.contains run && actual.getAppArgs.contains emission do
        throwError "expected the original return and its sparse emission"
      let abstracted ← mkForallFVars locals target (usedOnly := false) (usedLetOnly := false)
      assumptionType.mvarId!.assign abstracted
      remaining.assign (mkAppN provider parameters)
    let proof ← instantiateMVars probe
    let result ← mkLambdaFVars #[provider] proof
    let result ← instantiateMVars result
    if result.hasMVar then throwError "native obligation still contains unresolved metavariables"
    let required ← instantiateMVars assumptionType
    return mkApp3 (Lean.mkConst ``retainReportedArgument) claim required result

set_option cleanup.letToHave false in
set_option maxRecDepth 18000 in
set_option maxHeartbeats 14000000 in
/-- The reached packet and the original header initialize the native argument scanner once
the private evaluator has paid its emitted rows on that same return. -/
noncomputable def SignedCalendarAt.frozenLookupBeforeEmission [Fact (8≤header)]
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) (allowed : (elig(values,hist)) raw.val)
    (publication : cal.LookupReportPublicationAt oper qpos position chart reader chargeFit values h i hist claim raw allowed)
    (capacity : cal.LookupReportCapacityAt oper qpos position chart reader chargeFit values h i hist claim raw allowed)
    (opening : cal.LookupReportOpeningAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    PSigma (fun paid : Prop => paid → cal.LookupReportArgumentsAt oper qpos position chart reader chargeFit
      values h i hist claim raw allowed) := by
  classical
  exact retainOriginalReport%
    (cal.LookupReportArgumentsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) using
    let lookup := cal.frozenLookupAt oper qpos position chart reader chargeFit values h i hist claim raw allowed
    let sites := originalLookupSites% lookup
    let frame := originalLookupFrame% lookup
    refine fun operands => ?_
    let z := frame.replay (cal.frozenRouteBlock chart reader chargeFit) operands
    let exterior := z.1
    refine fun histories delivery table records writer states substitution words route result handoff observed => ?_
    let routeState := route.val
    let published := originalReportEvidence% publication at [exterior]
    let budget := originalReportEvidence% capacity at [exterior, routeState]
    have entered := opening operands histories delivery table records writer states substitution words route result handoff observed
    refine fun guard u same advance run seed alloc => ?_
    let site := sites exterior u
    have taskImage := onReturnedCalendar% lookup for SignedCalendarAt.frozenLookupReportTaskImage
      at [operands, u]
    have geom := originalIssuedGeometry% published, entered, u, advance, run, alloc, seed, taskImage
    obtain ⟨fr,_,count,_,cells,cables,_,_,sg⟩ := nativeReturnedReportFrame%
      (onReturnedCalendar% lookup for SignedCalendarAt.frozenLookupReportFragmentRoom
        at [publication, capacity, opening, operands, histories, delivery, table, records, writer, states,
          substitution, words, route, result, handoff, observed, u, advance, run]) seed alloc
    have bounded : fr.layout.count≤(planner₁).cube.maxRows :=
      count.le.trans ((Nat.le_add_right ..).trans (issuedField% records (issuedField% input site)))
    have marked := (onReturnedCalendar% lookup for SignedCalendarAt.frozenLookupReturnedSiteMarkers
      at [operands, u]).1
    have first : readings (result.pub u) 0=((selectedSites).publicWords u 0).val :=
      issuedField% frame (entered.2 u)
    have setup := ((issuedField% space published) u).controls_fit u.val
    let scanner := cal.frozenMarkedArgumentInput oper.grid qpos position chart reader chargeFit oper.funding values hist
    let atReport := startAtOriginalReport% scanner with
      [u, marked, run, same.source_seed seed, same.source_allocation alloc, geom, fr, bounded,
        cells, cables, sg, issuedField% endFit budget]
    apply atReport (by
      rw [first]
      exact setup)
    intro emission firstRun firstBank firstMem
end Diagonal

end BorderVNP
end Computability
end OAI
