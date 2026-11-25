import OAI.Computability.BorderVNP.DiagonalCalendarPhysicalLookup
import OAI.Computability.BorderVNP.DiagonalCalendarRoutedInputs
import OAI.Computability.BorderVNP.DiagonalCalendarOwnerAdmission
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalOwnership
import OAI.Computability.BorderVNP.DiagonalReturnedSourceExterior
import OAI.Computability.BorderVNP.DiagonalPublishedWriterApplication

import OAI.Computability.BorderVNP.DiagonalSelectedLookupProjections
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedBareAt
import OAI.Computability.BorderVNP.DiagonalRecordedGeometryTerm
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerNetwork

/-! # The physical geometry and network at an enrolled original field -/

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

open Lean Meta Elab Term

private def serviceAt (valid : Expr) (op : Name) : TermElabM Expr := do
  forallBoundedTelescope (← inferType valid) (some 3) fun _ result => do
    let some check ← whnfUntil result ``SignedCalendarAt.FrozenRouteChecks
      | throwError "expected the physical route checks on all pins"
    let args := check.getAppArgs
    let params := (args.extract 0 (args.size-3)).push valid
    return mkAppN (← mkConstWithLevelParams op) params

local elab "ownerServiceOn%" checked:term:max : term => do
  let valid ← elabTerm checked none
  serviceAt valid ``SignedCalendarAt.frozenIssuedOwnershipAtOriginalOfCandidates

local elab "fieldOfChecks%" checked:term:max : term => do
  let valid ← elabTerm checked none
  let service ← serviceAt valid ``SignedCalendarAt.issuedBareTupleAtOfCandidates
  let .forallE _ domain _ _ ← whnf (← inferType service)
    | throwError "expected a registered field as the input of the original tuple"
  return domain

/-- Supply the actual retained wire and frame from this owner's native receipt. -/
local elab "forReturnedOwner%" writers:term:max owner:term:max aligned:term:max : term => do
  let physical ← Lean.Elab.Term.elabTerm owner none
  let some info ← Lean.Meta.whnfUntil (← Lean.Meta.inferType physical) ``PreparationFrame.ReturnedOwnershipAt
    | throwError "expected a returned native owner"
  let mut signature := (← Lean.getConstInfo ``PreparationFrame.ReturnedOwnershipAt).type
  let mut wire := none
  let mut frame := none
  for x in info.getAppArgs do
    if signature.bindingName! == `L then wire := some x
    if signature.bindingName! == `F then frame := some x
    signature := signature.bindingBody!
  let some L := wire | throwError "missing the original native wire"
  let some F := frame | throwError "missing the original registered frame"
  let service ← Lean.Elab.Term.elabTerm writers none
  let same ← Lean.Elab.Term.elabTerm aligned none
  return Lean.mkAppN service #[L,same,F]

set_option cleanup.letToHave false in
set_option maxRecDepth 18000 in
set_option maxHeartbeats 18000000 in
private noncomputable def physicalOnOriginal
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁)) (entries : history(values) → ℕ)
    (valid : ∀ (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*qdim*w₁) → Bool),
      cal.FrozenRouteChecks grid qpos position chart reader chargeFit values h entries i hist claim) : PSigma (fun q : Prop => q) :=
  let network := (cal.plannerNetworkOnPacket oper.grid qpos position chart reader chargeFit values).down
  ⟨_, fun (f : fieldOfChecks% valid) =>
    let owner := (ownerServiceOn% valid) f
    let checked := valid f.1 f.2.1 f.2.2.2.1
    let route := f.2.2.1.val
    let declared := SignedPrep.routeBroadcast (cal.frozenPlannerTask grid qpos position chart reader chargeFit).cube _ route
    let ok := cal.frozenRouteAllowedForOwner grid qpos position chart reader chargeFit values f.2.1 route
    let shape := frameSelectionLike% (cal.frozenLookupAt oper qpos position chart reader chargeFit values h
      f.1 f.2.1 f.2.2.2.1 declared ok)
    let atFrame := forReturnedOwner% shape ((ownerServiceOn% valid) f) (checked.sites.extent declared.val)
    fun (selected : atFrame) (u : Fin (R₁+1)) =>
      let reached := originalLookupStages% selected
      let evidence := (reached owner.sourceExterior u).1.choose_spec
      let native := evidence.2
      let measured := geometryFromNative% (cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit)
        oper.routing values f.2.1 u native.2.2.1 native.2.2.2.1 native.2.2.2.2.1 evidence.1
      let physical := measured.down
      let live := network f.2.1 _ physical.2.1
      And.intro physical live⟩

set_option maxHeartbeats 18000000 in
set_option maxRecDepth 18000 in
/-- Every enrolled original field and team have compatible physical geometry
and writer network on their own admitted site. -/
theorem SignedCalendarAt.registeredPhysicalOnOriginalSelection
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁)) (entries : history(values) → ℕ)
    (valid : ∀ (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*qdim*w₁) → Bool),
      cal.FrozenRouteChecks grid qpos position chart reader chargeFit values h entries i hist claim) :
    (physicalOnOriginal cal oper qpos position chart reader chargeFit values h entries valid).1 :=
  (physicalOnOriginal cal oper qpos position chart reader chargeFit values h entries valid).2

end Diagonal

end BorderVNP
end Computability
end OAI
