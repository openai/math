import OAI.Computability.BorderVNP.DiagonalCalendarPhysicalLookup
import OAI.Computability.BorderVNP.DiagonalCalendarSuppliedHostSource
import OAI.Computability.BorderVNP.DiagonalSelectedLookupFrameFields
import OAI.Computability.BorderVNP.DiagonalCalendarCommonFrame
import OAI.Computability.BorderVNP.DiagonalRecordedOriginalHostSourceTerm
import OAI.Computability.BorderVNP.DiagonalHostPublicationAtSiteTerm
import OAI.Computability.BorderVNP.DiagonalHostHeaderAtFrameTerm
import Lean.Util.ShareCommon

/-! # Host words on each returned original report frame

The selected lookup fixes the original native exterior, returned team history
and report-frame coordinates. The packaged family retains the original
sixteen operands of the host read and the resulting proof at those operands. -/

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

set_option cleanup.letToHave false

variable [Fact (8≤header)]

open Lean Meta Elab Term

private def packHostResult {P : Prop} (proof : P) : (p : Prop) ×' p := ⟨P,proof⟩
private def packHostFamily {T : Type} (family : T) : (t : Type) ×' t := ⟨T,family⟩

private def closeHostFamily (xs : Array Expr) (proof : Expr) : MetaM Expr := do
  let p ← instantiateMVars proof
  if p.hasMVar then throwError "cannot retain a host proof with unresolved arguments"
  let paired := mkAppN (Lean.mkConst ``packHostResult) #[← inferType p,p]
  let family ← mkLambdaFVars xs paired (generalizeNondepLet:=false)
  return ShareCommon.shareCommon (mkAppN (Lean.mkConst ``packHostFamily) #[← inferType family,family])

local elab "callableBareHost%" source:term:max worker:term:max fixed:term:max plan:term:max routing:term:max values:term:max hist:term:max frame:term:max : term => do
  let ctx ← getLCtx
  let letIDs := ctx.getFVarIds
  let concrete (piece : Syntax) := do instantiateMVars (← zetaDeltaFVars (← elabTerm piece none) letIDs)
  let sibling ← concrete source
  let reader ← concrete worker
  let held ← concrete fixed
  let sc ← exprToSyntax sibling
  let rc ← exprToSyntax reader
  let fc ← exprToSyntax held
  let pc ← exprToSyntax (← concrete plan)
  let oc ← exprToSyntax (← concrete routing)
  let vc ← exprToSyntax (← concrete values)
  let hc ← exprToSyntax (← concrete hist)
  let frames ← concrete frame
  let take ← elabTerm (← `(originalHostAtSibling% $rc $sc)) none
  let frame ← elabTerm (← `(originalLookupFrame% $sc)) none
  let fr ← exprToSyntax frame
  forallBoundedTelescope (← inferType take) (some 16) fun history _ => do
    unless history.size==16 do throwError "the genuine source has a different original report arity"
    let args ← history.mapM exprToSyntax
    let x ← elabTerm (← `((($fr).replay $fc $(args[0]!)).1)) none
    let out ← exprToSyntax x
    let result ← elabTerm (← `(applyOriginalHostOnReplay% $rc $sc $out at [$args,*])) none
    let .forallE fitsName fitsDomain _ _ ← whnf (← inferType result) | throwError "missing physical fits family"
    unless fitsName == `fits do throwError "expected the original fits family, got {fitsName}"
    let (fits,heads) ← forallBoundedTelescope fitsDomain (some 1) fun team _ => do
      unless team.size == 1 do throwError "the original fit is not indexed by its team"
      let t ← exprToSyntax team[0]!
      let place ← elabTerm (← `(nativeHostPublicationAt% $pc $oc $vc $hc $sc $out $t)) none
      let address ← exprToSyntax (mkApp frames team[0]!)
      let observed ← exprToSyntax place
      let setup ← elabTerm (← `(hostSetupAtFrame% $address $observed)) none
      let first := mkProj ``And 0 setup
      let next := mkProj ``And 1 setup
      return (← mkLambdaFVars team first, ← mkLambdaFVars team next)
    let allFits := mkApp result fits
    let .forallE headsName _ _ _ ← whnf (← inferType allFits) | throwError "missing genuine frame heads"
    unless headsName == `heads do throwError "expected the original header family, got {headsName}"
    let physical := mkApp allFits heads
    closeHostFamily history physical

set_option maxRecDepth 18000 in
set_option maxHeartbeats 12000000 in
/-- The before-report host words on the original returned ownership and raw
query, using both measured frame fields, for every input to that host source. -/
noncomputable def SignedCalendarAt.originalBareOwnedHostFamily
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) (allowed : (elig(values,hist)) raw.val) : (T : Type) ×' T :=
  let selected := cal.frozenLookupAt oper qpos position chart reader chargeFit values h i hist claim raw allowed
  let worker := (cal.frozenHostSourceOfSites oper qpos position chart reader chargeFit values h i hist claim raw).2
  let frames := cal.frozenSites_frame oper.grid qpos position chart reader chargeFit
  callableBareHost% selected worker hold₁ (planner₁) oper.routing values hist frames

/-- Apply a packaged family at its native arguments and return its proof. -/
elab "applyBareFamily% " family:term:max " at " "[" args:term,* "]" : term => do
  let bundle ← elabTerm family none
  let xs ← args.getElems.mapM (fun arg => elabTerm arg none)
  return mkProj ``PSigma 1 (mkAppN (mkProj ``PSigma 1 bundle) xs)

end Diagonal

end BorderVNP
end Computability
end OAI
