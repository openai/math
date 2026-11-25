import OAI.Computability.BorderVNP.DiagonalCalendarPhysicalPostOperands
import OAI.Computability.BorderVNP.DiagonalCalendarArgumentBudget
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedArgumentAddresses
import OAI.Computability.BorderVNP.DiagonalCalendarSourceRoom
import OAI.Computability.BorderVNP.DiagonalWriterPostLayout

/-! # The planner post request at the actual startup, prefix and observed header -/

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

variable (grid : LocatedSignedGridAt cube b header (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
local notation "T₁" => epochs scales.τ (l+1)
local notation "copies₁" => TeamScales.width (l+1) scales.α
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

local notation3 (prettyPrint := false) "layout₁" => cal.frozenLayout chart reader chargeFit
local notation3 (prettyPrint := false) "initial₁" => reader.startupArenaWith (n:=l+1) (reg:=64)
  (prog₁) (a₁) (ℓ₁) (layout₁).header
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable grid qpos position (initial₁)
local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "free₁" => (selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit

local notation3 (prettyPrint := false) "hold₁" => cal.frozenRouteBlock chart reader chargeFit
local notation3 (prettyPrint := false) "boots₁" => cal.frozenSites_boots grid qpos position chart reader chargeFit hold₁
open RoutingISA.Evaluator.ScheduleClock TeamContraction.JointHeader
local notation "public₁" => ⌈publicWork (cube.pred+1) scales.α (r₁) (l+1) (R₁+1)⌉₊
local notation "local₁" => ⌈localWork (cube.pred+1) (E+2) scales.α (ξ₁) (r₁) (l+1) (R₁+1)⌉₊
local notation "route₁" => 512*(cube.pred+1+BorderVNP.Cube.Tally.selectorWidth cube.pred cube.copies cube.h+1)
local notation3 (prettyPrint := false) "fixed₁" => (CubeConstants.install (cube.cubeID paid)).slots
local notation "argWidth" => BorderVNP.Cube.Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width
local notation "finish₁" => ScheduleClock.cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width argWidth
local notation "read₁" => BorderVNP.Cube.TeamRowClock.physicalCoefficient cube.pred cube.b cube.h cube.copies cube.width

local notation "selectedCost" => uniformWindows r₁ (R₁+1) outside₁ public₁ local₁ route₁ fixed₁ finish₁ read₁


local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "ctl₁" => RoutingOutputs.controlsBase origin₁
  (selectedTask).cube.cables (selectedTask).cube.cells (directory₁).entries ((directory₁).teams*(directory₁).sites)
local notation3 (prettyPrint := false) "seedDir" => freeDirectory R₁ r₁
  ((tape₁).program.length+(cutWidth (l+1)+extra₁)) ℓ₁ tiles (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "cellsₚ" => CoverScale.sites (Cube D) (EnrichedOuter.depth S (d₁+1) T₁)
local notation3 (prettyPrint := false) "cablesₚ" => (boundaryShape S (d₁+1) T₁).edges+4*(R₁+1)*tiles
local notation3 (prettyPrint := false) "portsₚ" => (R₁+1)*tiles
local notation3 (prettyPrint := false) "routedₚ" => RoutingOutputs.bases origin₁ cablesₚ cellsₚ (directory₁).entries
local notation3 (prettyPrint := false) "controlₚ" => RoutingOutputs.controlsBase origin₁ cablesₚ cellsₚ (directory₁).entries portsₚ

set_option cleanup.letToHave false in
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6500000 in
private noncomputable def nativePlannerRequests
    (rate : CalendarPostRateAt cube b φ q adv c charge (l+1)) (live : Fin pins₁ → Bool) :
    PSigma fun family : Type => family :=
  let B := (boots₁).2.choose live
  let actual := cal.frozenPostWriterAt grid qpos position chart reader chargeFit rate live
  let plan := cal.frozenPlannerTask grid qpos position chart reader chargeFit
  let layoutEq := (cal.frozenEarlyTask grid qpos position chart reader chargeFit).symm.trans
    (cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit)
  have dirEq : directory₁=seedDir := (cal.frozenSourceRoom grid qpos position chart reader chargeFit).1
  have ctlEq : ctl₁=controlₚ := (cal.issuedArgumentAddresses grid qpos position chart reader chargeFit).2.1.symm
  ⟨_,fun x active (u : Fin (R₁+1)) fields seen =>
    let orig := actual x active u fields seen
    let landed : PinStart.JointPrefix plan.id (fun i => (B x i).start) := active
    let req := orig.atLayout layoutEq landed HEq.rfl seedDir dirEq (routedₚ).ends controlₚ
      (routedₚ).livePairs portsₚ ctlEq
    have budgetAt : (scales.chosenSignedWindows cube E (l+1) r₁).argumentsCalls=req.budget := by
      change (scales.chosenSignedWindows cube E (l+1) r₁).argumentsCalls=(selectedCost).argumentsCalls
      exact JointSchedule.normalizedArgumentBudget (b:=b) (cube:=cube) (l:=l)
    show {p : FragmentRows.WriterPostRequest plan (B x) landed u //
      p.fields.bits=fields.bits ∧ (p.Charge → orig.Charge) ∧
        (scales.chosenSignedWindows cube E (l+1) r₁).argumentsCalls=p.budget} from
    ⟨req,orig.atLayout_header layoutEq landed HEq.rfl seedDir dirEq _ _ _ _ ctlEq,
      orig.chargedOfLayout layoutEq landed HEq.rfl seedDir dirEq _ _ _ _ ctlEq,budgetAt⟩⟩

set_option cleanup.letToHave false in
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6500000 in
/-- The planner runs on this original returning startup and its actual
observed header. Its native charge pays the deployed request on the same
team, with precisely the chosen argument-call budget. -/
noncomputable def SignedCalendarAt.frozenPlannerPostAt
    (rate : CalendarPostRateAt cube b φ q adv c charge (l+1)) (live : Fin pins₁ → Bool) :
    (nativePlannerRequests cal grid qpos position chart reader chargeFit rate live).1 :=
  (nativePlannerRequests cal grid qpos position chart reader chargeFit rate live).2

end Diagonal

end BorderVNP
end Computability
end OAI
