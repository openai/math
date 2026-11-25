import OAI.Computability.BorderVNP.DiagonalCalendarPlannerSourceSlots
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalSavedTransport
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalGeometryHosts

/-! # Published original descriptions at the installed report's actual offset -/

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
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute tape₁ order₁ position Unit).choose

open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyCellReports CellMacro.Generator
open Shortening.PublicCapacity Diagonal.CellEntries

local notation3 (prettyPrint := false) "scalarIDs" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "words" => (geoSeed).eval x₁
local notation3 (prettyPrint := false) "matrices" => (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F
local notation3 (prettyPrint := false) "leafAt(" vs ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ vs x₁
local notation3 (prettyPrint := false) "histAt(" vs ")" => (packHistory (leafAt(vs)) (plan₁).compiled.machine.epoch T₁).Index

open RoutingISA.Evaluator TeamContraction.ProcessorSlots

local notation3 (prettyPrint := false) "fmt₁" => Boundary.seedFormat (tape₁) (order₁) position copies₁
local notation3 (prettyPrint := false) "cells₁" => CoverScale.sites (Cube D) (EnrichedOuter.depth S (d₁+1) T₁)
local notation3 (prettyPrint := false) "num₁" => (fun z : paid.Entry => cube.scalarNumber paid (.inl z))
open Packing.RoutingOutputs Diagonal.ExternalSew CellPacketGeometry TerminalCells
local notation "hooks₁" => Fintype.card scalarIDs
local notation "short₁" => 60*logWidth (r₁) (l+1)
local notation "live₁" => (R₁+1)*tiles
local notation3 (prettyPrint := false) "shape₁" => boundaryShape S (d₁+1) T₁
local notation3 (prettyPrint := false) "cables₁" => (shape₁).edges+4*(R₁+1)*tiles
local notation3 (prettyPrint := false) "sources₁" => (ProgramSchemas.epoch S (d₁+1) short₁ fmt₁ T₁).schema.append
  (Sewn.schema (2*(shape₁).edges+6*(R₁+1)*tiles) short₁)
local notation3 (prettyPrint := false) "last₁" => FinalTies.tieSchema cables₁ live₁ w₁
local notation3 (prettyPrint := false) "tpl₁" =>
  CellPacketGeometry.History.template sources₁ last₁ (scheduledBoxes dir₁ rfl num₁ grid.sites_pos)
    (cal.frozenPacketTags grid position).1 (cal.frozenPacketTags grid position).2
    (FinalReports.Spare.priv (C:=cells₁) (g:=hooks₁) (digits:=w₁) (E:=Fin J₁))
    (FinalReports.Spare.reports (C:=cells₁) (g:=hooks₁) (digits:=w₁) (E:=Fin J₁))

open CellPacketGeometry.History.Native CellSparse.Packet

set_option maxHeartbeats 9500000 in
set_option maxRecDepth 16000 in
set_option cleanup.letToHave false in
/-- Keep the selected planner's argument words while restoring the original
box directory at any name for the same control address. -/
noncomputable def SignedCalendarAt.frozenFundedOriginalPublicationAt
    (values : matrices) (hist : histAt(values)) {ram : ℕ → ℕ}
    (marked : cal.frozenIssuedMarkers grid qpos position chart reader chargeFit values hist ram)
    (ctl : ℕ)
    (named : let task := cal.frozenPlannerTask grid qpos position chart reader chargeFit
      RoutingOutputs.controlsBase origin₁ task.cube.cables task.cube.cells J₁ live₁=ctl) :=
  let src := cal.frozenPlannerPublishedSourceSlots grid qpos position chart reader chargeFit values hist marked
  let ptr := fun j : Fin J₁ => (Sum.inl (Sum.inr j) : (tpl₁).Fields)
  let args := src.choose
  let dir := cal.frozenIssuedDirectory grid qpos position chart reader chargeFit values hist
  let normalized : ∀ {k : ℕ}, SiteWords.Directory (Fin k) (Fin J₁) (cells₁+1) → Prop := fun {_} target =>
    Published target (tpl₁).publicDepth (tpl₁).chunkDepth (ctl+37) (header*logWidth r₁ (l+1)) ptr args ram
  let native := fun addr : ℕ => Published dir (tpl₁).publicDepth (tpl₁).chunkDepth (addr+37)
    (header*logWidth r₁ (l+1)) ptr args ram
  let published := Eq.mp (congrArg native named) src.choose_spec.1
  let transport := cal.frozenOriginalSavedTransport grid qpos position chart reader chargeFit values hist
    (fun {_} target => normalized target)
  PLift.up (And.intro (transport.2.mpr published) src.choose_spec.2)

set_option maxHeartbeats 9500000 in
set_option maxRecDepth 16000 in
set_option cleanup.letToHave false in
/-- Keep the selected planner's argument words while restoring the original
box directory and the stated circuit cable count in the control address. -/
noncomputable def SignedCalendarAt.frozenFundedOriginalPublication
    (values : matrices) (hist : histAt(values)) {ram : ℕ → ℕ}
    (marked : cal.frozenIssuedMarkers grid qpos position chart reader chargeFit values hist ram) :=
  let atOrigin := (cal.frozenIssuedPlacement grid qpos position chart reader chargeFit).2.2.1
  let selected := congrArg (fun dest => RoutingOutputs.controlsBase dest cables₁ cells₁ J₁ live₁) atOrigin
  let same := selected.trans (cal.frozenPlannerReportControl grid qpos position chart reader chargeFit).symm
  cal.frozenFundedOriginalPublicationAt grid qpos position chart reader chargeFit values hist marked
    (RoutingOutputs.controlsBase origin₁ cables₁ cells₁ J₁ live₁) same.symm

set_option maxHeartbeats 9700000 in
set_option maxRecDepth 16000 in
set_option cleanup.letToHave false in
/-- The planner's reached descriptor stop counts exactly the arguments in
the restored original box directory. -/
theorem SignedCalendarAt.frozenFundedOriginalStops
    (values : matrices) (hist : histAt(values)) {ram : ℕ → ℕ}
    (marked : cal.frozenIssuedMarkers grid qpos position chart reader chargeFit values hist ram)
    (team frame offsets live ports : ℕ) :
    let task := cal.frozenPlannerTask grid qpos position chart reader chargeFit
    let ctl := RoutingOutputs.controlsBase origin₁ task.cube.cables task.cube.cells J₁ live₁
    let dir := (cal.frozenOriginalGeometry grid qpos position chart reader chargeFit values hist).directory
    let ptr := fun i : Fin J₁ => (Sum.inl (Sum.inr i) : (tpl₁).Fields)
    (task.controlRows team frame offsets ctl live ports).stops =
      task.cube.cells+1+(Schema.coords (dir.referenceRows ptr).length).length := by
  intro task ctl dir ptr
  let chosen := cal.frozenPlannerReportRankInputs grid qpos position chart reader chargeFit values hist marked
    team frame offsets live ports
  let P : ∀ {k : ℕ}, SiteWords.Directory (Fin k) (Fin J₁) (cells₁+1) → Prop := fun {_} target =>
    (task.controlRows team frame offsets ctl live ports).stops =
      task.cube.cells+1+(Schema.coords (target.referenceRows ptr).length).length
  exact (cal.frozenOriginalSavedTransport grid qpos position chart reader chargeFit values hist
    (fun {_} target => P target)).2.mpr chosen.2.2.1

end Diagonal

end BorderVNP
end Computability
end OAI
