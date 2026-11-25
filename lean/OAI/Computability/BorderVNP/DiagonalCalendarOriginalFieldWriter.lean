import OAI.Computability.BorderVNP.DiagonalCalendarOriginalFieldGeometry
import OAI.Computability.BorderVNP.DiagonalCalendarBootChecks
import OAI.Computability.BorderVNP.DiagonalCalendarFrozenBoots
import OAI.Computability.BorderVNP.DiagonalCalendarCommonFrame
import OAI.Computability.BorderVNP.DiagonalCalendarFundedDirectoryRoom
import OAI.Computability.BorderVNP.DiagonalIssuedWriterOperand

/-! # Native publication and host retention on original issued fields -/

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

local notation "grid" => oper.grid

open Lean Meta Elab Term in
/-- Apply the native readback using the circuits, sites and fields carried by
this returned pin. This keeps elaboration from recomputing their indices from
the full network and the candidate's independently measured layout. -/
local elab "registeredOperandWriter%" proof:term:max candidate:term:max operand:term:max
    same:term:max frame:term:max : term => do
  let publication ← elabTerm proof none
  let site ← elabTerm candidate none
  let publicOperand ← elabTerm operand none
  let operandEq ← elabTerm same none
  let frameEq ← elabTerm frame none
  let some pinType ← whnfUntil (← inferType publication) ``PublishedPin
    | throwError "expected the registered native publication"
  let epoch ← mkProjection site `epoch
  let published ← mkProjection site `published
  let middle ← mkProjection site `middle
  let middleEq ← mkProjection site `epochMemory
  return mkAppN (Lean.mkConst ``PublishedPin.writer_at_frame_of_returns pinType.getAppFn.constLevels!)
    (pinType.getAppArgs ++ #[publication, epoch, published, publicOperand, middle, operandEq, frameEq, middleEq])

open Lean Meta Elab Term in
local elab "registeredDomain%" service:term:max : term => do
  let actual ← elabTerm service none
  let .forallE _ domain _ _ ← whnf (← inferType actual)
    | throwError "expected the original registered fields or selected frames"
  return domain

open Lean Meta Elab Term in
private def checkedOperands (application : Expr) : MetaM (NameMap Expr) := do
  let info ← getConstInfo application.getAppFn.constName!
  forallTelescope info.type fun binders _ => do
    let mut table : NameMap Expr := {}
    for binder in binders, originalArg in application.getAppArgs do
      let name ← binder.fvarId!.getUserName
      table := table.insert name originalArg
    return table

open Lean Meta Elab Term in
local elab "returnedHostAt%" starts:term:max active:term:max team:term:max receipt:term:max
    writers:term:max source:term:max : term => do
  let U ← elabTerm starts none
  let activeTrace ← elabTerm active none
  let u ← elabTerm team none
  let owned ← elabTerm receipt none
  let done ← elabTerm writers none
  let readers ← elabTerm source none
  let some observed ← whnfUntil (← inferType owned) ``PreparationFrame.ReturnedOwnershipAt
    | throwError "expected the original returned ownership proof"
  let some written ← whnfUntil (← inferType done) ``RoutingISA.Evaluator.ReturnedWriters
    | throwError "expected the completed writer of this frame"
  let fromOwnership ← checkedOperands observed
  let fromWriter ← checkedOperands written
  let mut table := fromOwnership
  for (formal, original) in [(`a,`sa),(`sites,`t),(`pins,`d),(`livePin,`pin),(`wire,`L),
      (`common,`header),(`publicAt,`pub),(`macroAt,`mac),(`regsAt,`reg),(`memoryAt,`mem),
      (`seen,`origin),(`ext,`exterior),(`template,`template₀),(`rows,`count),(`route,`v)] do
    let some value := fromOwnership.find? original | throwError "missing returned ownership index {original}"
    table := table.insert formal value
  for (formal, original) in [(`writerReg,`r),(`writerEnd,`t),(`entered,`m),(`after,`mt),(`events,`es),(`W,`H)] do
    let some value := fromWriter.find? original | throwError "missing actual native writer index {original}"
    table := table.insert formal value
  for (key, value) in [(`U,U),(`active,activeTrace),(`teamSlot,u),(`atOwned,owned),(`done,done),(`source,readers)] do
    table := table.insert key value
  let lemmaName := ``RoutingISA.Evaluator.PinStart.issued_writer_host
  let info ← getConstInfo lemmaName
  forallTelescope info.type fun binders _ => do
    let mut arguments := #[]
    for binder in binders do
      let key ← binder.fvarId!.getUserName
      let some value := table.find? key | throwError "missing original writer operand {key}"
      arguments := arguments.push value
    return mkAppN (← mkConstWithLevelParams lemmaName) arguments

set_option cleanup.letToHave false in
set_option maxRecDepth 22000 in
set_option maxHeartbeats 25000000 in
private noncomputable def writerOnOriginal
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁)) (entries : history(values) → ℕ)
    (valid : ∀ (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*qdim*w₁) → Bool),
      cal.FrozenRouteChecks grid qpos position chart reader chargeFit values h entries i hist claim) : PSigma (fun q : Prop => q) :=
  let originalTuple := cal.issuedBareTupleAtOfCandidates grid qpos position chart reader chargeFit values h entries valid
  let ownerAt := cal.frozenIssuedOwnershipAtOriginalOfCandidates grid qpos position chart reader chargeFit values h entries valid
  let physicalAt := cal.registeredPhysicalOnOriginalSelection oper qpos position chart reader chargeFit values h entries valid
  let boots := cal.frozenSites_boots grid qpos position chart reader chargeFit (cal.frozenRouteBlock chart reader chargeFit)
  let pin := (boxPinCodec (pairedTableParameters (l+1) size₁) reader.rankFits reader.boxFits).encode h
  let nodes := boots.2.choose pin
  let room := cal.frozenFundedDirectoryRoom grid qpos position chart reader chargeFit oper.routing
  ⟨_, fun (f : registeredDomain% physicalAt) =>
    let cut := ownerAt f
    let nativeAt := physicalAt f
    let z := originalTuple f
    let U := fun v => (nodes z.1 v).start
    fun (selected : registeredDomain% nativeAt) (u : Fin (R₁+1)) =>
      let physical := nativeAt selected u
      let banked := physical.1
      let site := (originalLookupSites% selected) cut.sourceExterior u
      let boot := nodes z.1 u
      let frameAt := boot.start_frame_of_public (cal.frozenSites_frame grid qpos position chart reader chargeFit u)
      let emitted := registeredOperandWriter% (banked.2.2) site ((U u).pub)
        (boot.start_public_words) frameAt
      let hdr := boot.start_routing_header banked.1
      let done := (recordedWriters% selected) cut.sourceExterior u
      let readers := ((originalLookupStages% selected) cut.sourceExterior u).2.2.2.2
      let bundle := And.intro emitted (And.intro hdr (And.intro banked.2.1 (And.intro physical.2
        (And.intro banked.2.2 (And.intro done (And.intro readers (And.intro room.reserved
          (And.intro room.originFit room.low))))))))
      let actual := returnedHostAt% U (z.2) u cut done readers
      let kept := FiniteEvaluator.CubeAllocation.HostRetention.at_written_memory emitted.1 actual
      And.intro bundle kept⟩

set_option maxRecDepth 22000 in
set_option maxHeartbeats 25000000 in
/-- For every original positive field, the selected site on its admitted frame
provides the physical header, published packet, network, and native slotted
writer at the original team's public operand. The field's actual owned return
retains the RAM published by that same writer. -/
theorem SignedCalendarAt.writerOnOriginalSelection
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁)) (entries : history(values) → ℕ)
    (valid : ∀ (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*qdim*w₁) → Bool),
      cal.FrozenRouteChecks grid qpos position chart reader chargeFit values h entries i hist claim) :
    (writerOnOriginal cal oper qpos position chart reader chargeFit values h entries valid).1 :=
  (writerOnOriginal cal oper qpos position chart reader chargeFit values h entries valid).2

end Diagonal

end BorderVNP
end Computability
end OAI
