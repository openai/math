import OAI.Computability.BorderVNP.DiagonalCalendarIssuedAllocation
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedFinishAddresses
import OAI.Computability.BorderVNP.DiagonalCalendarBuilderRoom
import OAI.Computability.BorderVNP.DiagonalFrozenExecutionRange

/-! # Calendar operands for issuing the original registered prefix -/

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
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable grid qpos position (initial₁)
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "number₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit
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

open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyCellReports CellMacro.Generator
open Shortening.PublicCapacity Diagonal.CellEntries

local notation3 (prettyPrint := false) "frame₁" => fun u : Fin (R₁+1) => ((selectedSites).publicWords u 0).val
local notation3 (prettyPrint := false) "scalarIDs" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "ids" => (Fintype.equivFin (scalarIDs)).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "labelIDs" => (ParseTable.numberedLabelEquiv ord l size₁).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "bounds" => cal.frozenSpliceBounds grid
local notation3 (prettyPrint := false) "seeds" => fun t i z => ((ExternalSew.RowTrace.seedNumber S (d₁+1) t i) z).val
local notation3 (prettyPrint := false) "words" => (geoSeed).eval x₁
local notation3 (prettyPrint := false) "matrices" => (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F
local notation3 (prettyPrint := false) "leafAt(" vs ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ vs x₁
local notation3 (prettyPrint := false) "histAt(" vs ")" => (packHistory (leafAt(vs)) (plan₁).compiled.machine.epoch T₁).Index
local notation3 (prettyPrint := false) "coreAt(" vs "," h ")" =>
  (plan₁).signedCoreDirectory prog₁ (geo₁).fits W₁ position labelIDs sites₁ edges₁ ports₁ vs
    words (leafAt(vs)).property seeds free₁ grid.count (Sum.inl : paid.Entry → scalarIDs) ids
    (bounds).2.1 h cube scales.α ξ₁ (bounds).1 (geo₁).literalSize (bounds).2.2 number₁ (selectedTask).p.privateGap
local notation3 (prettyPrint := false) "calcOrigin" =>
  Allocation.dest ((initial₁).next+7*(dir₁).candidates) cap₁ ceiling₁ (located₁).outputs w₁
local notation3 (prettyPrint := false) "cells₁" => Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "arena₁" => (RoutingISA.CubeArena.selectedSizes arenaBase
  (BorderVNP.Cube.alphabet scales.α (l+1)) ((R₁+1)*TeamScales.exterior ξ₁ r₁ (l+1))
  cells₁ ((boundary S (d₁+1) T₁).edges+4*((R₁+1)*CoverScale.sites (Cube D) (d₁+1)))
  (dir₁).candidates (R₁+1) r₁ (l+1) cap₁).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "task₁" => SignedTaskArena.Layout.mk arena₁ (cube.cubeID paid) (selectedTask).p
local notation3 (prettyPrint := false) "ctl(" o ")" => Packing.RoutingOutputs.controlsBase o (arena₁).cables cells₁
  (dir₁).entries ((R₁+1)*tiles)
local notation3 (prettyPrint := false) "report(" fr "," o ")" =>
  DiagonalTallyAllocation.reportLayout (task₁).before (task₁).after fr (ctl(o))
    (task₁).p.parameters (task₁).p.siteWidth (task₁).p.bodyCap (arena₁).stop
local notation3 (prettyPrint := false) "rowsAt(" vs "," h "," rt "," o ")" =>
  (plan₁).signedReceivedRows prog₁ (geo₁).fits W₁ position labelIDs sites₁ edges₁ ports₁ vs
    words (leafAt(vs)).property seeds free₁ grid.count (Sum.inl : paid.Entry → scalarIDs) ids
    (bounds).2.1 h cube scales.α ξ₁ (bounds).1 (geo₁).literalSize (bounds).2.2 number₁
    (selectedTask).p arenaBase cap₁ (fun _ => (initial₁).frame) (fun _ => o) (Subtype.val rt)
local notation3 (prettyPrint := false) "frameAt(" u ")" => ((selectedSites).publicWords u 0).val

open DiagonalTallyAllocation
local notation3 (prettyPrint := false) "queryCount" => Fintype.card (Board.Physical (pairedTableParameters (l+1) size₁) (budget₁+6) w₁ scalarIDs)
local notation3 (prettyPrint := false) "guessCount" => Fintype.card (Guess (Fin (pairedTableParameters (l+1) size₁))
  reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))

set_option cleanup.letToHave false in
/-- The exact inputs used by the chosen source registration at a team: the
allocated row and each of its marks, all continuation addresses, replay
space, and the scalar IDs and maximum count for the issued directory. -/
theorem SignedCalendarAt.frozenIssuedApplication
    (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1))
    (values : matrices) (hist : histAt(values)) (route : (coreAt(values,hist)).Route cube.width)
    (u : Fin (R₁+1)) (axis : Fin (cube.pred+1)) :
    let fr := frameAt(u)
    let eqF := (cal.frozenSites_frame grid qpos position chart reader chargeFit u).symm
    let castFrame := congrArg (fun j => report(j,origin₁)) eqF
    let r := (rowsAt(values,hist,route,origin₁)).atLayout castFrame
    ReportAllocation (task₁).before (task₁).after ((arena₁).cellWriter fr (ctl(origin₁)) axis)
        (report(fr,origin₁)) (r.cells u) (task₁).after.reportCursor ∧
      (∀ c ∈ r.cells u, ∀ b ∈ c.bundles, ∀ g ∈ b.positions, g.parameter<2^w₁ ∧ g.place<w₁) ∧
      (task₁).FinishAddresses initial₁ (ctl(origin₁)) (task₁).cube.header.profile (task₁).cube.n
        (task₁).cube.header.d (task₁).cube.header.cap w₁ w₁ queryCount guessCount reader.gates ∧
      CubeConstants.valueBound (task₁).id < 2^w₁ ∧ (task₁).cube.ReplayRoom w₁ (initial₁).frame ∧ (directory₁).candidates ≤ (task₁).cube.maxRows ∧
      ∀ e : BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width,
        (task₁).id e = (Fintype.equivFin scalarIDs (Sum.inr e)).val := by
  intro fr eqF castFrame r
  have banks := cal.issuedReportAllocation grid qpos position chart reader chargeFit values hist route u axis
  have placement := cal.frozenIssuedPlacement grid qpos position chart reader chargeFit
  have taskEq : selectedTask = task₁ := by
    rw [cal.frozenTask_eq_selected grid qpos position chart reader chargeFit]
    rfl
  have limits := cal.frozenBuilderRoom grid qpos position chart reader chargeFit oper.routing
  have addresses := cal.frozenIssuedFinishAddresses grid qpos position chart reader chargeFit oper.post
  change (selectedTask).FinishAddresses _ _ _ _ _ _ _ _ _ _ _ at addresses
  rw [taskEq] at addresses limits
  have control : Packing.RoutingOutputs.controlsBase origin₁ (arena₁).cables (arena₁).cells
      (directory₁).entries ((directory₁).teams*(directory₁).sites) = ctl(origin₁) := by
    rw [placement.1]
    rfl
  rw [control] at addresses
  have cap := placement.2.2.2.1
  rw [taskEq] at cap
  have bound : (directory₁).candidates ≤ (task₁).cube.maxRows := by
    rw [placement.1]
    exact cap
  exact ⟨banks.1,banks.2,addresses,oper.dictionary,limits.2.2.1,bound,fun _ => rfl⟩

end Diagonal

end BorderVNP
end Computability
end OAI
