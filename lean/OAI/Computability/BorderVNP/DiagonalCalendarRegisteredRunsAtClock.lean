import OAI.Computability.BorderVNP.DiagonalCalendarRegistrationAtNativeNext
import OAI.Computability.BorderVNP.DiagonalCalendarNativeNextSelection

/-! # Original registered returns on the measured calendar and its selected sparse calls -/

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
set_option maxRecDepth 14000
set_option maxHeartbeats 13000000
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

variable (grid : LocatedSignedGridAt cube b header (l+1)) (qpos : 1 ≤ Q)
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

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit

local notation3 (prettyPrint := false) "hold₁" => cal.frozenRouteBlock chart reader chargeFit
local notation3 (prettyPrint := false) "boots₁" => cal.frozenSites_boots grid qpos position chart reader chargeFit hold₁

local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index

local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width

local notation "qdim" => pairedTableParameters (l+1) size₁+Fintype.card identifiers
local notation3 (prettyPrint := false) "fullPin" h => (boxPinCodec (pairedTableParameters (l+1) size₁) reader.rankFits reader.boxFits).encode h

open Lean Meta Elab Term in
/-- Apply the native selection theorem to the actual calendar arguments.
Its ordinary congruence proof preserves the registered run at this route. -/
private def nativeRunEquality (fam selected : Syntax) : TermElabM Expr := do
  let next ← instantiateMVars (← elabTerm selected none)
  let predicate ← instantiateMVars (← elabTerm fam none)
  unless next.isAppOf ``SignedCalendarAt.frozenNativeNext do
    throwError "expected the selected physical continuation"
  let proof := mkAppN (mkConst `OAI.Computability.BorderVNP.Diagonal.SignedCalendarAt.frozenNativeNext_selection) next.getAppArgs
  let statement ← whnf (← inferType proof)
  unless statement.isAppOfArity ``Eq 3 do
    throwError "expected the equality of the physical continuations"
  let arguments := statement.getAppArgs
  let u ← getLevel arguments[0]!
  return mkAppN (mkConst ``congrArg [u, .succ .zero])
    #[arguments[0]!,mkSort .zero,arguments[1]!,arguments[2]!,predicate,proof]

open Lean Elab Term in
/-- Build the registration congruence at the selected native continuation. -/
local elab "nativeRunEquality% " fam:term:arg selected:term:arg : term =>
  nativeRunEquality fam selected

set_option cleanup.letToHave false in
private noncomputable def measuredRegisteredAgreement
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (j : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (entries : history(values) → ℕ)
    (valid : ∀ (i : Fin pins₁ → Bool) (hist : history(values)) (cc : Fin ((R₁+1)*qdim*w₁) → Bool),
      cal.FrozenRouteChecks grid qpos position chart reader chargeFit values j entries i hist cc) : (P : Prop) ×' P :=
  let register := cal.frozenRegistrationAtNativeNext grid qpos position chart reader chargeFit values j entries
    (fun i hist claim => by
      have received := valid i hist claim
      unfold SignedCalendarAt.FrozenRouteChecks at received
      exact received)
  let native := cal.frozenNativeNext grid qpos position chart reader chargeFit (fullPin j)
  let agreement := fun measured source raw hist v =>
    let actual := native measured source
    let family (n : type_of% actual) : Prop := (register n raw hist v).runs
    nativeRunEquality% family (cal.frozenNativeNext grid qpos position chart reader chargeFit (fullPin j) measured source)
  ⟨_,agreement⟩

/-- For each original raw pin, history and routed input, the registration
condition agrees on the measured continuation and its selected sparse calls. -/
theorem SignedCalendarAt.frozenRegisteredRunsAtMeasuredSelection
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (j : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (entries : history(values) → ℕ)
    (valid : ∀ (i : Fin pins₁ → Bool) (hist : history(values)) (cc : Fin ((R₁+1)*qdim*w₁) → Bool),
      cal.FrozenRouteChecks grid qpos position chart reader chargeFit values j entries i hist cc) :
    (measuredRegisteredAgreement cal grid qpos position chart reader chargeFit values j entries valid).1 :=
  (measuredRegisteredAgreement cal grid qpos position chart reader chargeFit values j entries valid).2

end Diagonal

end BorderVNP
end Computability
end OAI
