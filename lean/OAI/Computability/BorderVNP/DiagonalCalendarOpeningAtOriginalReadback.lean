import OAI.Computability.BorderVNP.DiagonalSelectedOpeningReadback
import OAI.Computability.BorderVNP.DiagonalCalendarLookupReportTests

/-! # Opening the recorded report at its original calendar site -/

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

local notation "n₁" => l+1
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

local notation3 (prettyPrint := false) "bounds₁" => cal.frozenSpliceBounds oper.grid
local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "numberIDs" => (Fintype.equivFin identifiers).toEmbedding.trans Fin.valEmbedding

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
set_option cleanup.letToHave false in
/-- The issued report-opening rule on the actual program, field assignment and
history, together with its startup geometry address. The inventory universe
is determined by the selected site's physical declaration. -/
noncomputable def SignedCalendarAt.openingPlanAtHistory.{v}
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (hist : history(values)) : PSigma (fun p : Prop => p) × ℕ :=
  let seedIDs := fun t i z => ((ExternalSew.RowTrace.seedNumber S (d₁+1) t i) z).val
  (PSigma.mk _ <|
    @SeedPlan.issuedReportOpeningOfReadback.{v} D «m» _ F identifiers _ paid S R₁ r₁ pins₁ ℓ₁ l d₁ extra₁ 64 w₁ ec₁
      (w₁+1) size₁ copies₁ T₁ header Q plan₁ prog₁ (geo₁).fits order₁ W₁ position tag₁ _ _ _ sites₁ edges₁
      ports₁ values ((geoSeed).eval x₁) (leaf(values)).property seedIDs free₁ oper.grid.count
      (Sum.inl : paid.Entry → identifiers) numberIDs (bounds₁).2.1 hist K _ cube scales.α ξ₁ (bounds₁).1
      (geo₁).literalSize (bounds₁).2.2 _ number₁ (selectedTask).p arenaBase cap₁, origin₁)

open Lean Meta Elab Term Tactic
open RoutingISA.Evaluator.SignedPrep

private partial def openingBinderNames (ty : Expr) : Array Name :=
  match ty with
  | .forallE name _ body _ => #[name.eraseMacroScopes] ++ openingBinderNames body
  | _ => #[]

/-- Apply the numerical plan to the actual runtime operands in the rebanked opener.
Its only remaining argument is the conjunction of native controls and readbacks. -/
private def originalRebankOpeningRule (plan target originalOrigin : Expr) : MetaM Expr := do
  let some goal ← whnfUntil target ``CandidateReportOpening
    | throwError "expected the rebanked CandidateReportOpening"
  let names := openingBinderNames (← getConstInfo ``CandidateReportOpening).type
  let values := goal.getAppArgs
  let arg (id : Name) : MetaM Expr := do
    let some i := names.idxOf? id | throwError "missing CandidateReportOpening parameter {id}"
    return values[i]!
  let mut proof ← mkProjection plan `snd
  let mut ty ← inferType proof
  while let .forallE name _ body info ← whnf ty do
    let id := name.eraseMacroScopes
    let val ← if info.isInstImplicit then do
        let some i := names.idxOf? `I | throwError "missing original inventory type"
        pure values[i+1]!
      else if id == `origin then pure originalOrigin
      else arg <| match id with
        | `mw => `w
        | `dictionary => `b
        | `representative => `owner
        | `pinSites => `pins
        | `inputFields => `fields
        | `broadcastFrame => `f
        | `sample => `q
        | other => other
    proof := mkApp proof val
    ty := body.instantiate1 val
    if id == `sample then
      let .forallE _ _ conclusion _ ← whnf ty | throwError "missing control/readback evidence"
      let some closed ← whnfUntil conclusion ``CandidateReportOpening
        | throwError "plan produced a different final predicate"
      unless closed.getAppNumArgs == values.size do throwError "incomplete rebanked report goal"
      for source in closed.getAppArgs, destination in values, label in names do
        unless ← isDefEq source destination do
          throwError "the issued plan's {label} differs from the original CandidateReportOpening"
      return proof
  throwError "missing original routed sample"

/-- Reduce the reached opening on the original site to its physical control
family and its per-team report readbacks. Read the inventory universe and
all native return operands from the current rebanked goal. -/
elab "applyIssuedOpeningReadback " plan:term:max : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let some site ← whnfUntil (← goal.getType) ``CandidateReportOpening
      | throwError "expected the opening of the reached report"
    let term ← Term.elabTerm plan none
    let some selected ← whnfUntil term ``SignedCalendarAt.openingPlanAtHistory
      | throwError "expected the opening plan at the original calendar history"
    let scale := Lean.mkConst ``SignedCalendarAt.openingPlanAtHistory site.getAppFn.constLevels!
    let actualPlan := mkAppN scale selected.getAppArgs
    let rule ← originalRebankOpeningRule (← mkProjection actualPlan `fst) site
      (← mkProjection actualPlan `snd)
    let .forallE _ tests _ _ ← whnf (← inferType rule)
      | throwError "missing the native control and readback conjunction"
    let evidence ← mkFreshExprSyntheticOpaqueMVar tests
    goal.assign (mkApp rule evidence)
    replaceMainGoal [evidence.mvarId!]

end Diagonal

end BorderVNP
end Computability
end OAI
