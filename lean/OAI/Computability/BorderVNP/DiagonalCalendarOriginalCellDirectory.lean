import OAI.Computability.BorderVNP.DiagonalCalendarIssuedCellDirectory
import OAI.Computability.BorderVNP.DiagonalCalendarNormalizedIssuedDirectory

/-! # The emitted cell records on the original-input directory -/

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
local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "free₁" => (selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute tape₁ order₁ position Unit).choose
local notation3 (prettyPrint := false) "widths₁" => fun i =>
  Fintype.card (Machine.Guess S (d₁+1) (fun _ _ => 60*logWidth r₁ (l+1)) i)
local notation3 (prettyPrint := false) "slots₁" => fun i =>
  Fintype.equivFin (Machine.Guess S (d₁+1) (fun _ _ => 60*logWidth r₁ (l+1)) i)
local notation3 (prettyPrint := false) "fit₁" => (plan₁).profile_order_fits widths₁ slots₁
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

local notation3 (prettyPrint := false) "wr₁" => cal.seed.choose_spec.choose
local notation3 (prettyPrint := false) "wired₁" => wiringWith prog₁ P₁ selectedSites pins₁ ℓ₁ (l+1) ec₁ (geo₁).fits
local notation3 (prettyPrint := false) "rowCount₁" => CoverScale.sites (Cube D) (EnrichedOuter.depth S (d₁+1) T₁)
local notation3 (prettyPrint := false) "hookCount₁" => Fintype.card (paid.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry
  cube.pred cube.b cube.h cube.copies cube.width)
local notation3 (prettyPrint := false) "num₁" => fun v : paid.Entry => cube.scalarNumber paid (.inl v)
local notation3 (prettyPrint := false) "packetTask₁" => (cal.locatedEmitter grid position initial₁ wired₁).task


local notation3 (prettyPrint := false) "bodies₁" => fun j : Fin J₁ =>
  (W₁).seedStored position tag₁ sites₁ edges₁ ports₁ (ExternalSew.RowTrace.groupedGridRows tape₁ axes d₁ order₁ position copies₁).edge
    (Equiv.toEmbedding (Equiv.refl (Fin tiles))) (order₁ (finProdFinEquiv.symm j).2)
local notation3 (prettyPrint := false) "dest₁" =>
  Allocation.dest ((initial₁).next+7*(dir₁).candidates) cap₁ ceiling₁ (located₁).outputs w₁

set_option maxRecDepth 8500 in
set_option maxHeartbeats 14000000 in
/-- The original-anchor directory reads the actual private and count fields
and all final records of the enriched program. -/
theorem SignedCalendarAt.frozenOriginalDirectory_returned
    (values : matrices) (hist : histAt(values)) (ram : ℕ → ℕ)
    (marked : cal.frozenPacketImage grid qpos position chart reader chargeFit values hist ram) (c : Fin rowCount₁) :
    let N := EnrichedTape.network (pins:=pins₁) prog₁ (geo₁).fits position free₁ grid.count (plan₁).compiled.machine (leafAt(values)) rfl hist
    let core := coreAt(values,hist)
    let dir := (cal.frozenOriginalIssuedDirectory grid qpos position chart reader chargeFit values hist).val
    let state := fun v => (core.programs v).program
    ((dir.privateWires c.castSucc=FinalCell.privateBits N (fun v => (core.cell v).val) state c.val) ∧
      dir.reports c.castSucc=DiagonalTallyCellReports.countFields
        (FinalCell.countBase N (fun v => (core.cell v).val) state c.val) hookCount₁ w₁) ∧
      ∀ headerWidth slot pb db eb scratch burst bytes,
        (dir.placed c.castSucc headerWidth slot bodies₁ pb db eb scratch burst bytes).directory =
          FinalCell.directory core.owner N (fun v => (core.cell v).val) core.siteID core.edgeID core.portID
            state c.val (dir.reports c.castSucc) := by
  intro N core dir state
  have same : cal.frozenIssuedDirectory grid qpos position chart reader chargeFit values hist = dir :=
    (cal.frozenOriginalIssuedDirectory grid qpos position chart reader chargeFit values hist).property
  have actual := cal.frozenIssuedDirectory_returned grid qpos position chart reader chargeFit values hist ram marked c
  rw [← same]
  exact actual

end Diagonal

end BorderVNP
end Computability
end OAI
