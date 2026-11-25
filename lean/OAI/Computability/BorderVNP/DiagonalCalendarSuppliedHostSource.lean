import OAI.Computability.BorderVNP.DiagonalCalendarRosterHostWords
import OAI.Computability.BorderVNP.DiagonalOriginalHostDataTerm
import OAI.Computability.BorderVNP.DiagonalNativeHostGeometryTerm
import OAI.Computability.BorderVNP.DiagonalOriginalHostLedgerTerm
import OAI.Computability.BorderVNP.DiagonalReturnedReportStage
import OAI.Computability.BorderVNP.DiagonalReturnedEntryPlacement
import OAI.Computability.BorderVNP.DiagonalOriginalMatchedHostScanTerm
import OAI.Computability.BorderVNP.DiagonalOriginalOwnerReplayTerm
import OAI.Computability.BorderVNP.DiagonalRegisteredHostScan
import OAI.Computability.BorderVNP.DiagonalCalendarRegisteredResidentOwner
import OAI.Computability.BorderVNP.DiagonalCalendarFrozenReportK
import OAI.Computability.BorderVNP.DiagonalReportOpeningDomainTerm
import OAI.Computability.BorderVNP.DiagonalOriginalLookupHostTableTerm
import OAI.Computability.BorderVNP.DiagonalSelectedHostFrameTerm
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedHostInstaller
import OAI.Computability.BorderVNP.DiagonalCalendarOwnedHostWordsType
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerFrameInputs
import OAI.Computability.BorderVNP.DiagonalSelectedCandidateWriterResult
import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections
import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations
import OAI.Computability.BorderVNP.DiagonalSelectedHostFrame
import OAI.Computability.BorderVNP.DiagonalSelectedHistoryHostTables
import OAI.Computability.BorderVNP.DiagonalCalendarLookupHostBounds
import OAI.Computability.BorderVNP.DiagonalCandidateBankReportTests
import OAI.Computability.BorderVNP.DiagonalProjectedOwnedReplay
import OAI.Computability.BorderVNP.DiagonalHostReportRectangles
import OAI.Computability.BorderVNP.DiagonalBootedRawPin
import OAI.Computability.BorderVNP.DiagonalCalendarNativeEligibility
import OAI.Computability.BorderVNP.DiagonalCalendarBuilderRoom
import OAI.Computability.BorderVNP.DiagonalCalendarRoutedAt

/-! # Original host words on a supplied family of issued calendar sites -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

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
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "free₁" => (selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute tape₁ order₁ position Unit).choose
local notation3 (prettyPrint := false) "arenaBase" =>
  Allocation.stop ((initial₁).next+7*(dir₁).candidates) cap₁ ceiling₁ (located₁).outputs w₁ w₁
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit

local notation3 (prettyPrint := false) "hold₁" => cal.frozenRouteBlock chart reader chargeFit
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


open Packing.RoutingOutputs RoutingISA.SignedTaskArena GeometryFrameEncoding
open VPVNP.VerifierNetwork BorderVNP.PackedHistoryCircuit

set_option cleanup.letToHave false
set_option maxRecDepth 15000
set_option maxHeartbeats 12000000

variable [Fact (8≤header)]
local notation3 (prettyPrint := false) "G₁" => CellEntries.SewnTape.wiring prog₁ (geo₁).fits free₁ pins₁
open Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs

/-- Recover the local value type of an existing report predicate without
requiring that predicate at any other exterior or owner return. -/
private abbrev LocalReportValue {P : Sort*} {Q : Sort*} (_ : P → Q) := Q

local notation3 (prettyPrint := false) "widths₁" => fun i =>
  Fintype.card (Machine.Guess S (d₁+1) (fun _ _ => 60*logWidth r₁ (l+1)) i)
local notation3 (prettyPrint := false) "slots₁" => fun i =>
  Fintype.equivFin (Machine.Guess S (d₁+1) (fun _ _ => 60*logWidth r₁ (l+1)) i)
local notation3 (prettyPrint := false) "fit₁" => (plan₁).profile_order_fits widths₁ slots₁
local notation3 (prettyPrint := false) "codec(" v ")" => ((plan₁).compiled.machine.nativeCode (leaf(v))
   geoSeed x₁ rfl widths₁ slots₁ fit₁).toEmbedding.trans (Function.Embedding.subtype _)
local notation3 (prettyPrint := false) "fullPin" h => (boxPinCodec (pairedTableParameters (l+1) size₁)
  reader.rankFits reader.boxFits).encode h


/-- The received team's private placement uses its recorded public frame and returned middle RAM. -/
private theorem returnedPrivatePlacement {w head originalHead base links cells entries descSize gap : ℕ}
    {before actual registered : Memory w} (frame : head=originalHead) (after : actual=registered)
    (pass : (privateLayout originalHead base links cells entries descSize gap).Image
      (readings before) entries (readings registered)) :
    (privateLayout head base links cells entries descSize gap).Image
      (readings before) entries (readings actual) := by
  cases frame
  cases after
  exact pass

open Lean Meta Elab Term in
local elab "originalOwnerIndex% " source:term:max index:ident : term => do
  let sites ← elabTerm source none
  let head := ``PreparationFrame.SelectedLookupSites
  let some call ← whnfUntil (← inferType sites) head | throwError "expected the selected lookup family"
  let info ← getConstInfo head
  forallTelescope info.type fun parameters _ => do
    for parameter in parameters, value in call.getAppArgs do
      if (← parameter.fvarId!.getUserName) == index.getId then return value
    throwError "missing original address function"

open Lean Meta Elab Term in
/-- Read a per-team argument of the checked original input family. -/
local elab "nativeHostSourceOperand%" field:ident proof:term:max : term => do
  let source ← elabTerm proof none
  forallBoundedTelescope (← inferType source) (some 1) fun teams slot => do
    unless teams.size==1 do throwError "expected a physical input on each team"
    let some native ← whnfUntil slot ``ProfileRouteInputs | throwError "expected the native source-bank inputs"
    let info ← getConstInfo ``ProfileRouteInputs
    forallTelescope info.type fun params _ => do
      for param in params, actual in native.getAppArgs do
        if (← param.fvarId!.getUserName)==field.getId then return ← mkLambdaFVars teams actual
      throwError "unknown native input parameter {field.getId}"


private abbrev SitePredicate {A : Sort*} {P : A → Sort*} (_ : (a : A) → P a) := A
private def suppliedHostClaim {p : Prop} (proof : p) : PSigma (fun q : Prop => q) := ⟨p,proof⟩

set_option cleanup.letToHave false in
set_option maxRecDepth 18000 in
set_option maxHeartbeats 16000000 in
/-- At an arbitrary genuine site family for this issued calendar, the observed writer and its
native report buffers determine the original W host words on the same returned ownership scan. -/
noncomputable def SignedCalendarAt.frozenHostSourceOfSites
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) :=
  let p : PositiveFields cap₁ (selectedTask).cube.n (selectedTask).cube.header.d (selectedTask).cube.header.cap
    (R₁+1) (selectedTask).dim (b.physical.tally (l+1)) := ⟨(codec(values)) hist,raw.val,claim⟩
  let trace := cal.frozenPlannerFrameOfSites oper.grid qpos position chart reader chargeFit oper.routing
    (oper.startup.2 rfl cal chart reader chargeFit) values hist p hold₁ (fullPin h) i
  let numbers := cal.frozenLookupHostBounds oper qpos position chart reader chargeFit values hist
  let eqCable := cal.frozenHostCableCount oper.grid qpos position chart reader chargeFit values hist
  let model := cal.frozenReportGeometry oper.grid qpos position chart reader chargeFit values hist
  suppliedHostClaim <| fun (evidence : SitePredicate trace) per =>
    let proof := trace evidence per raw.property
    let prototype := namedPhysicalLookup% (selectedCandidateWriterLookup% (planner₁) (p.cube) (physicalWriterLabel% evidence) evidence proof)
    fun {wire : WireLayout (R₁+1) r₁ ℓ₁} {extent : wire.header=(layout₁).header}
      {selected : (originalHostFrameAt% prototype) wire extent} (s : (originalHostSitesAt% prototype) wire extent selected)
      =>
    let inventories := originalHostInventories% s
    letI := inventories.1
    letI := inventories.2
    let originalSites := originalLookupSites% s
    let activeProjection := issuedField% projection s
    let reports := frozenReportKAtLookup% (cal.frozenReportK oper.grid qpos position chart reader chargeFit values hist)
      hold₁ raw.val s
    let test := fun stage : TeamContraction.CandidateReportStage => originalReportStage% reports stage
    atReportOpening% (test .opening) with operands H delivery eqTab eqRow writer runs pins recv q endRows handoff observed as AtReturn =>
    let z := selected.replay (cal.frozenRouteBlock chart reader chargeFit) operands
    fun (published : LocalReportValue (fun k : test .publication => Classical.choice (k z.1)))
        (limits : LocalReportValue (fun c : test .capacity => Classical.choice (c z.1 q.val)))
        (opens : AtReturn)
        {old : Fin (R₁+1) → Fin 81 → Word w₁} {first gates outputs width off ell ctl : ℕ}
        {profile : Fin (R₁+1) → List Bool} {claims : Fin (R₁+1) → List (List Bool)}
        {pad used charged : Fin (R₁+1) → ℕ} {regs : Fin (R₁+1) → Bank w₁} {mem : Fin (R₁+1) → Memory w₁}
        (returned : ∀ t, (originalHostReturn% (originalSites z.1 t)) (old t) first gates outputs width off ell ctl
          (profile t) (claims t) (pad t) (regs t) (mem t) (used t) (charged t))
        (fits : ∀ t, (privateLayout (initial₁).frame origin₁ (planner₁).cube.cables (planner₁).cube.cells
          (dir₁).entries (dir₁).description (planner₁).p.privateGap).Fits w₁ (readings (issuedField% geometry (originalSites z.1 t))))
        (heads : ∀ t, Header (initial₁).frame origin₁ (planner₁).cube.cables (planner₁).cube.cells (dir₁).entries
          (readings (issuedField% geometry (originalSites z.1 t)))) =>
    let original := reachedSharedOwner% activeProjection z.1 H delivery eqTab eqRow writer pins handoff observed
    let data := original.choose_spec
    let site := (originalOnHistorySites% s) z.1 H runs
    let hw := fun t => (originalLookupHostTables% s) z.1 H runs t (returned t)
    let stages := (originalOnHistoryStages% s) z.1 H runs
    let actual := data.2.2.1
    let agree := data.2.2.2.1
    let handed := data.2.2.2.2.1
    let seen := data.2.2.2.2.2.1
    let pinned := data.2.2.2.2.2.2.2.1
    let symbols := data.2.2.2.2.2.2.2.2
    let held := fun t => (hw t).2.2.2.2.2.2.2
    let inputs := fun (t : Fin (R₁+1)) => (hw t).1
    let teamFrames := nativeHostSourceOperand% f inputs
    let procFields := nativeHostSourceOperand% F inputs
    let actualGuess := nativeHostSourceOperand% guess inputs
    let names := (cal.frozenRegisteredResidentCoordinates oper.grid qpos position chart reader chargeFit values hist).1
    (actualRegisteredHostScan% names q agree seen) (claim:=fun route =>
      cal.OwnedHostWords oper.grid qpos position chart reader chargeFit values hist route i endRows) <| fun mat seenMat =>
      let native := originalHostLedger%
        (cal.frozenIssuedHostSource oper.grid qpos position chart reader chargeFit values hist)
        s endRows actual symbols handed mat seenMat
      let afterCapacity := exactHostGeometry% native fields model.1 arguments [
        (fun _ : Fin (R₁+1) => model.2),
        (fun t => Packing.CellAddressPhysical.Represents.of_castCables eqCable ((issuedField% net limits) t)),
        (fun c => (congrArg (fun e => (e c).val) (Fields.castRect_cells (F:=model.1) eqCable)).symm.trans
          ((issuedField% codes limits) c)), issuedField% widths limits, numbers.ownerWidth, numbers.wordFit,
        (initial₁).next, origin₁, (fun t => issuedField% geometry (originalSites z.1 t)),
        (fun t => issuedField% middle (site t)),
        (fun t => Image.of_castCables eqCable ((issuedField% image published) t)),
        (fun t => returnedPrivatePlacement (congrArg (fun words : Arg → Word w₁ => (words 0).val) (runs t).1)
          (stages t).2.1 ((issuedField% place published) t)),
        (fun t => (congrArg (fun head => (privateLayout head origin₁ (planner₁).cube.cables (planner₁).cube.cells
          (dir₁).entries (dir₁).description (planner₁).p.privateGap).Fits w₁
            (readings (issuedField% geometry (originalSites z.1 t)))) (issuedField% origin (site t))).mpr (fits t)),
        (fun t => (congrArg (fun head => Header head origin₁ (planner₁).cube.cables (planner₁).cube.cells (dir₁).entries
          (readings (issuedField% geometry (originalSites z.1 t)))) (issuedField% origin (site t))).mpr (heads t)),
        numbers.reserve, numbers.endGeo, numbers.geoFit, numbers.teamsFit, numbers.processorFit, numbers.fieldsFit,
        numbers.literalFit, numbers.cellsFit, numbers.strideFit, numbers.capacity]
      let issued := nativeHostData% afterCapacity
        from [teamFrames, procFields, actualGuess, inputs, (fun t => (hw t).2.1),
          (fun t => Classical.choice (hw t).2.2.1)]
        buffer [old,first,gates,outputs,width,off,ell,ctl,profile,claims,pad,raw.val]
        opening (fun t => (hw t).2.2.2.1)
        reports (fun t => (issuedField% published (site t)).val.2.1) (fun t => (held t).choose)
        reads (fun t => ((issuedField% image activeProjection) z.1 t).symm.trans (held t).choose_spec)
      let onRoster := issued
        i (fun t => ((G₁).substitution_jointGuess (originalOwnerIndex% s ib) (originalOwnerIndex% s hb)
          (originalOwnerIndex% s sb) i t (H t).initial).mp (pinned t))
        _ (fun t => originalPaidPlacement% (opens.2 t))

      cal.frozenHostWordsOnRoster oper.grid qpos position chart reader chargeFit values hist
        mat.val i endRows onRoster

end Diagonal

end BorderVNP
end Computability
end OAI
