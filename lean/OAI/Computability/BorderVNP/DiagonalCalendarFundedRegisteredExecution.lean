import OAI.Computability.BorderVNP.DiagonalCalendarMeasuredFundedIssue
import OAI.Computability.BorderVNP.DiagonalFrozenExecutionRange
import OAI.Computability.BorderVNP.DiagonalCalendarNativeNext
import OAI.Computability.BorderVNP.DiagonalCalendarCandidatePackets
import OAI.Computability.BorderVNP.DiagonalCalendarCandidateReader
import OAI.Computability.BorderVNP.DiagonalCalendarGuardedRegisteredPacket
import OAI.Computability.BorderVNP.DiagonalCalendarSuppliedAtRoutes
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedGeometry
import OAI.Computability.BorderVNP.DiagonalCalendarFeasiblePost

/-! # Native execution on the original funded calendar reports

After the measured cells have been issued, the original registered signed reports
and the retained reader complete every assignment of the same native pin. -/

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

variable (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1))
    (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "copies₁" => TeamScales.width (l+1) scales.α
variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)


local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation "qdim" => pairedTableParameters (l+1) size₁+Fintype.card identifiers
local notation3 (prettyPrint := false) "fullPin" h => (boxPinCodec (pairedTableParameters (l+1) size₁) reader.rankFits reader.boxFits).encode h

local notation3 (prettyPrint := false) "frameEntries(" vs ")" =>
  cal.frozenFrameEntries oper.grid qpos position chart reader chargeFit vs

local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
open RoutingISA.Evaluator.ScheduleClock TeamContraction.JointHeader
local notation "public₁" => ⌈publicWork (cube.pred+1) scales.α (r₁) (l+1) (R₁+1)⌉₊
local notation "local₁" => ⌈localWork (cube.pred+1) (E+2) scales.α (ξ₁) (r₁) (l+1) (R₁+1)⌉₊
local notation "route₁" => 512*(cube.pred+1+BorderVNP.Cube.Tally.selectorWidth cube.pred cube.copies cube.h+1)
local notation3 (prettyPrint := false) "fixed₁" => (CubeConstants.install (cube.cubeID paid)).slots
local notation "argWidth" => BorderVNP.Cube.Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width
local notation "finish₁" => ScheduleClock.cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width argWidth
local notation "read₁" => BorderVNP.Cube.TeamRowClock.physicalCoefficient cube.pred cube.b cube.h cube.copies cube.width

local notation "selectedCost" => uniformWindows r₁ (R₁+1) outside₁ public₁ local₁ route₁ fixed₁ finish₁ read₁



private structure PhysicalPrices where
  calls : Nat
  coordinate : Nat
  word : Nat
  publicWork : Nat
  localWork : Nat
  finish : Nat
  read : Nat

set_option cleanup.letToHave false in
private noncomputable def originalWindowPrices
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (_valid : ∀ (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*qdim*w₁) → Bool),
      cal.FrozenRouteChecks oper.grid qpos position chart reader chargeFit values h (frameEntries(values)) i hist claim) :
    PhysicalPrices := ⟨(selectedCost).argumentsCalls,qdim,w₁,public₁,local₁,finish₁,read₁⟩

-- The native source operations above determine the physical prices.
open Lean Meta Elab Term

/-- Read the actual native call term used by the returned cell. -/
private def retainedFieldCalls (evidence pair measured : Expr) : MetaM Expr :=
  lambdaTelescope evidence fun field body => do
    unless field.size==1 do throwError "expected a single native issued field"
    let calls ← match body.find? (fun term => term.isAppOf ``SignedCalendarAt.frozenNativeCalls && term.getAppNumArgs>2) with
      | some found => pure found
      | none =>
        let .app issued _ := body.consumeMData | throwError "missing original issued call term"
        let some result ← withTransparency .all <| whnfUntil (← inferType issued)
            ``BootedPinStart.PreparedHistoryDecoder.IssuedOnCalls
          | throwError "the physical field has no original calls"
        pure result.getAppArgs.back!
    unless !calls.containsFVar field[0]!.fvarId! do throwError "native call family depends on a single issued field"
    let some actual ← withTransparency .all <| whnfUntil calls ``SignedCalendarAt.frozenNativeCalls
      | throwError "expected the calendar's original native calls"
    let parameters := actual.getAppArgs
    unless ← isDefEq parameters[parameters.size-2]! measured do throwError "different physical clock"
    unless ← isDefEq parameters.back! (mkProj ``Prod 1 pair) do throwError "different funded source"
    return actual

private def realProgram : MetaM (Expr × Expr) := do
  let firstName := ``SignedCalendarAt.measuredFundedIssuedColumn
  let .defnInfo first ← getConstInfo firstName | throwError "expected the measured issued field operation"
  lambdaTelescope first.value fun inputs code => do
    let count := inputs.size
    let last := inputs.extract (count-2) count
    let lastNames ← last.mapM fun x => do pure (← x.fvarId!.getDecl).userName.eraseMacroScopes
    unless lastNames == #[`measured,`funded] do throwError "unexpected field coordinates {lastNames}"
    let originalInputs := inputs.extract 0 (count-2)
    let firstFive := mkAppN (← mkConstWithLevelParams firstName) inputs
    let some owned ← withTransparency .all <| whnfUntil code ``SignedCalendarAt.measuredOwnedColumn
      | throwError "the issued field no longer uses the measured owner column"
    let valid := originalInputs.back!
    let calibrated ← forallTelescope (← inferType valid) fun _ clause => do
      let some checked ← withTransparency .all <| whnfUntil clause ``SignedCalendarAt.FrozenRouteChecks
        | throwError "expected the original checked route"
      let parameters := checked.getAppArgs
      pure ((parameters.extract 0 (parameters.size-3)).push valid)
    let supplied := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.frozenSuppliedAtRoutes) (calibrated.push last[1]!)
    let acquire := mkProj ``Prod 0 supplied
    let calls ← retainedFieldCalls owned.getAppArgs.back! supplied last[0]!
    let hrule := mkAppN (← mkConstWithLevelParams ``SignedCalendarAt.guardedRegisteredPacket) (calibrated ++ #[acquire,calls])
    let price := mkAppN (← mkConstWithLevelParams ``originalWindowPrices) originalInputs
    unless (← inferType price).isAppOf ``PhysicalPrices do throwError "expected the actual seven prices of this original calendar"
    let prices := (List.range 7).toArray.map (fun i => mkProj ``PhysicalPrices i price)
    let some oi ← originalInputs.findIdxM? (fun v => do pure ((← v.fvarId!.getDecl).userName.eraseMacroScopes == `oper))
      | throwError "missing actual operational calendar"
    let rateProof ← mkAppM ``FrozenExecutionAt.post #[originalInputs[oi]!]
    let .forallE _ guarded _ _ ← whnf (← inferType firstFive) | throwError "the fifth native field did not request the guarded returns"
    let reports ← forallBoundedTelescope guarded (some 4) (whnfType:=true) fun xs _ => do
      let .forallE _ registration _ _ ← whnf (← inferType (mkAppN hrule xs))
        | throwError "the original native packet did not request its registered run"
      if registration.containsFVar xs[3]!.fvarId! then throwError "site registration depends on an already chosen guard"
      mkForallFVars (xs.extract 0 3) registration
    withLocalDeclD `registered reports fun registered => do
      let atPoint := fun (xs : Array Expr) => do
        let rr := mkAppN registered (xs.extract 0 3)
        pure (mkAppN hrule (xs ++ #[rr,rateProof] ++ prices))
      let chargeType ← forallBoundedTelescope guarded (some 4) (whnfType:=true) fun xs _ => do
        let point ← atPoint xs
        let .forallE _ paid _ _ ← whnf (← inferType point) | throwError "the native source has no charged post"
        if xs.any (fun x => paid.containsFVar x.fvarId!) then throwError "the writer depends on a private proposed route"
        pure paid
      withLocalDeclD `charged chargeType fun charged => do
        let returned ← forallBoundedTelescope guarded (some 4) (whnfType:=true) fun xs _ => do
          let point ← atPoint xs
          mkLambdaFVars xs (mkApp point charged)
        let program := mkApp firstFive returned
        let result ← inferType program
        unless (← withTransparency .all <| whnfUntil result ``ChosenReader.WiredPinExecution).isSome do
          throwError "the actual selected calendar did not finish with its wired pin evaluation"
        let all := inputs ++ #[registered,charged]
        return ShareCommon.shareCommon' (← mkForallFVars all result, ← mkLambdaFVars all program)

local elab "trueRegisteredExecution%" : term => do
  let (result, program) ← realProgram
  let level ← getLevel result
  let resultSort := mkSort level
  let id := mkLambda `Result .default resultSort (.bvar 0)
  return mkAppN (mkConst ``PSigma.mk [level.succ,level]) #[resultSort,id,result,program]

set_option maxHeartbeats 9000000 in
set_option maxRecDepth 16000 in
set_option Elab.async false in
private noncomputable def completedProgram : (Result : Type 1) ×' Result := trueRegisteredExecution%

/-- Execute the selected native column using the physical registration at each guarded input
and the reader state returned by the charged original program. -/
noncomputable def SignedCalendarAt.fundedRegisteredExecution : completedProgram.1 := completedProgram.2
end Diagonal

end BorderVNP
end Computability
end OAI
