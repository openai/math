import OAI.Computability.BorderVNP.DiagonalCalendarCandidateOnOriginalReports
import OAI.Computability.BorderVNP.DiagonalCheckedFieldNativeWriter
import OAI.Computability.BorderVNP.DiagonalAttainedReportOperands
import OAI.Computability.BorderVNP.DiagonalCandidateIssuedEmission
import OAI.Computability.BorderVNP.DiagonalFundedRawOwner
import OAI.Computability.BorderVNP.DiagonalCalendarOwnerReadTransport

/-! # The funded owner words on the original report family -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

universe u

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


open RoutingISA.Evaluator.SignedPrep _root_.OAI.Computability.BorderVNP.Cube

local notation3 (prettyPrint := false) "planner" =>
  cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit

open Lean Meta Elab Term
open private originalOwner atAttainedOwner from OAI.Computability.BorderVNP.DiagonalAttainedReportOperands
open private argument atHead argumentsOf from OAI.Computability.BorderVNP.DiagonalCalendarOriginalOwnership

private def allOwnerReadbacks {ι : Sort u} (value : ι → PSigma fun p : Prop => p) :
    PSigma fun p : Prop => p :=
  ⟨∀ i, (value i).1,fun i => (value i).2⟩

private def reportWitness (observed : Expr) : MetaM Expr := do
  let existential ← atHead (← inferType observed) ``Exists
  return mkAppN (mkConst ``Exists.choose_spec existential.getAppFn.constLevels!) (existential.getAppArgs.push observed)

private def ownerOperand (app : Expr) (wanted : Name) : MetaM (Expr × Expr) := do
  let mut type ← inferType app.getAppFn
  for value in app.getAppArgs do
    let .forallE field domain body _ := type | throwError "expected an indexed owner operand"
    if field==wanted then return (value,domain)
    type := body.instantiate1 value
  throwError "no operand {wanted} in {app.getAppFn}"

/-- Apply the checked declaration at precisely the receiver and incoming widths of the attained candidate. -/
private def declaredCellRead (candidate route declared cell cells : Expr) : MetaM Expr := do
  let (_,routed) ← ownerOperand candidate `q
  let descriptor ← atHead routed ``Cube.Physical.NativeAssignments.Routed
  let (owner,_) ← ownerOperand descriptor `owners
  let greedy ← atHead owner ``Cube.Physical.greedyOwner
  let coords ← argumentsOf greedy
  let advert ← atHead (← inferType declared) ``Eq
  let replacements := #[(`R,←argument coords `r),(`cells,cells),(`amount,←argument coords `dataWidth),
    (`decl,advert.getAppArgs[2]!),(`q,route),(`matched,declared),(`c,cell)]
  let info ← getConstInfo ``fundedOwnerOfRoute
  forallTelescope info.type fun fields _ => do
    let mut operands := #[]
    for x in fields do
      let d ← x.fvarId!.getDecl
      let name := d.userName
      let value ← if let some (_,v) := replacements.find? (fun p => p.1==name) then pure v
        else if d.binderInfo.isInstImplicit then do
          let mut found : Option Expr := none
          for (_,v) in coords do
            let vty ← inferType v
            if vty.isAppOf ``Fintype then found := some v
          let some inst := found | throwError "no finite row enumeration"
          pure inst
        else argument coords name
      operands := operands.push value
    return mkAppN (mkConst info.name (info.levelParams.map fun _ => .zero)) operands

/-- Recover both owner reads on one and the same original field and physical team. -/
local elab "originalFundedCells% " reports:term:max writers:term:max : term => do
  let found ← elabTerm reports none
  let native ← elabTerm writers none
  let some atChecks ← whnfUntil native ``SignedCalendarAt.frozenNativeWriterOnOriginal | throwError "expected the native checked roster"
  let receive := mkAppN (←mkConstWithLevelParams ``SignedCalendarAt.frozenOwnerReadsOnOriginal) atChecks.getAppArgs
  let .forallE _ fieldType _ _ ← whnf (← inferType native) | throwError "missing original field"
  withLocalDeclD `f fieldType fun field => do
    let report := mkApp found field
    let attained := mkProj ``And 1 report
    let returned ← reportWitness (← reportWitness (mkProj ``And 0 report))
    let nonempty ← atHead (← inferType returned) ``Nonempty
    let C := mkAppN (mkConst ``Classical.choice nonempty.getAppFn.constLevels!) (nonempty.getAppArgs.push returned)
    let candidate ← atHead (← inferType C) ``ReturnedCandidateReports
    let (out,_) ← ownerOperand candidate `out
    let (routedPayload,_) ← ownerOperand candidate `q
    let fields := getStructureFields (← getEnv) ``ReturnedCandidateReports
    let some idx := fields.idxOf? `declared | throwError "missing the original broadcast equality"
    let declared := mkProj ``ReturnedCandidateReports idx C
    let (starts,_,_) ← originalOwner attained
    let .forallE _ teamType _ _ ← whnf (← inferType starts) | throwError "expected team starts"
    withLocalDeclD `u teamType fun team => do
      let (_,cellAt) ← ownerOperand candidate `cell
      let .forallE _ _ cellType _ ← whnf cellAt | throwError "expected the native cell map"
      let fin ← atHead cellType ``Fin
      let (word,read) ← withLocalDeclD `c cellType fun cell => do
        let value ← atAttainedOwner ``ReturnedCandidateReports.fundedOwnerWord (← exprToSyntax C)
          (← exprToSyntax attained) (← exprToSyntax team)
          [(`owned,←exprToSyntax (←mkEqRefl (mkApp out team))),(`c,←exprToSyntax cell)]
        let left ← atHead (←inferType value) ``Eq
        let numbered ← declaredCellRead candidate routedPayload declared cell fin.getAppArgs[0]!
        let right ← atHead (←inferType numbered) ``Eq
        let e := left.getAppArgs
        let proof := mkAppN (mkConst ``Eq.trans left.getAppFn.constLevels!) #[e[0]!,e[1]!,e[2]!,
          right.getAppArgs[2]!,value,numbered]
        return (←mkLambdaFVars #[cell] e[1]!,←mkLambdaFVars #[cell] proof)
      let result := mkAppN receive #[field,word,read]
      let proposition := mkSort .zero
      let family := mkLambda `p .default proposition (.bvar 0)
      let point := mkAppN (mkConst ``PSigma.mk [.ofNat 1,.zero]) #[proposition,family,←inferType result,result]
      let allTeams ← mkAppM ``allOwnerReadbacks #[←mkLambdaFVars #[team] point]
      mkAppM ``allOwnerReadbacks #[←mkLambdaFVars #[field] allTeams]

set_option maxRecDepth 19000 in
set_option maxHeartbeats 16000000 in
set_option cleanup.letToHave false in
private noncomputable def fundedOwnersOnReports
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) : PSigma fun P : Prop => P :=
  let checks := cal.routeInputsOnOriginalReports oper qpos position chart reader chargeFit values h reports
  originalFundedCells% (cal.reportedCandidateOnOriginalReports oper qpos position chart reader chargeFit values h reports)
    (nativeWritersForChecked% checks)

set_option maxRecDepth 19000 in
set_option maxHeartbeats 16000000 in
set_option cleanup.letToHave false in
/-- Both ownership checks read this same host-table word of the
registered team. The returned candidate and its declared route come from
the actual original pin, history and unfiltered report. -/
theorem SignedCalendarAt.fundedOwnerWordsOnOriginalReports
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (reports : ∀ i hist claim raw allowed,
      cal.LookupReportsAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    (fundedOwnersOnReports cal oper qpos position chart reader chargeFit values h reports).1 :=
  (fundedOwnersOnReports cal oper qpos position chart reader chargeFit values h reports).2

end Diagonal

end BorderVNP
end Computability
end OAI
