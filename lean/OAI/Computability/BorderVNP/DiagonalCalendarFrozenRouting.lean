import OAI.Computability.BorderVNP.DiagonalCalendarLocatedShape
import OAI.Computability.BorderVNP.DiagonalLocatedFrozenRouting

/-! # The routed arena and original crossings of the calendar deployment -/

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
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 7000
set_option maxHeartbeats 1900000

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

/-- The two-field routing directory of the signed program's frozen verifier. -/
noncomputable def SignedCalendarAt.frozenDirectory : Directory.Layout := dir₁

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
local notation "X₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)

open Packing.RoutingOutputs

/-- The actual reserved gate table and its two appended banks occupy this
calendar reader's startup arena. Its route table, controls, destination
directory and private descriptions all fit before placement or pin data. -/
theorem SignedCalendarAt.locatedGateTable_routing
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1)) :
    let ar := (cal.frozenTask grid qpos position chart reader chargeFit).cube
    let dir := cal.frozenDirectory
    let t := located₁
    let base := Allocation.dest ((initial₁).next+7*dir.candidates) cap₁ (t.raw.reserve ceiling₁).size t.outputs (w₁)
    let ptr := bases base ar.cables ar.cells dir.entries
    SelectedRawWriterRoom ar dir (w₁) (X₁) (initial₁).next cap₁ (t.raw.reserve ceiling₁).size t.outputs (w₁) ∧
      RouteTableInputs ar dir scales.α (ξ₁) (l+1) (w₁) (initial₁).frame (ℓ₁) ∧
      controlsBase base ar.cables ar.cells dir.entries (dir.teams*dir.sites)+37≤ar.header.header ∧
      Directory.ISA.wordBound (Directory.ISA.placementBound dir ptr.privatePairs ptr.livePairs ar.cellStride)<2^(w₁) ∧
      dir.entries*dir.description≤dir.teams*dir.processors*(dir.literal/2) := by
  intro ar dir t base ptr
  let sy := _root_.OAI.Computability.BorderVNP.Cube.alphabet scales.α (l+1)
  let blk := _root_.OAI.Computability.BorderVNP.Cube.Physical.blocksFor ((R₁+1)*(X₁) : ℕ) (cube.h*cube.b) (sy^(cube.pred+1))
  let cap := _root_.OAI.Computability.BorderVNP.Cube.Physical.declarationCap cube.pred sy blk cube.b cube.h cube.width
  let dim := pairedTableParameters (l+1) (size₁) +
    Fintype.card (paid.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
  let length := JointHeader.PositiveFields.width cap₁ cube.pred sy cap (R₁+1) dim (b.physical.tally (l+1))
  let init : StartupArena := ⟨R₁+1,r₁,literal scales.α (l+1),b.physical.link (l+1),length,reader.packetBitCount⟩
  have initEq : initial₁ = init := by
    have arena := reader.frozenTask_startupArena (geo₁) (ℓ₁) (layout₁).header
    conv_rhs at arena => rw [(cal.frozenLayout_fields chart reader chargeFit).1,← grid.link_eq]
    exact arena
  have dirEq : dir=b.signedStartupDirectory (l+1) description :=
    (grid.template_directory (pins₁) (geo₁)).2
  have both := routing.table_at chart reader chargeFit header description ceiling₁ factor tiles J₁ t
    (initial₁) dir (ℓ₁) initEq dirEq grid.link_eq.symm
  have guard : SelectedRawWriterRoom ar dir (w₁) (X₁) (initial₁).next cap₁ (t.raw.reserve ceiling₁).size t.outputs (w₁) := both.1
  have literalEq : dir.literal = literal scales.α (l+1) := (grid.template_directory (pins₁) (geo₁)).1
  have short : dir.description≤dir.literal := by
    rw [literalEq]
    exact grid.geometricStorage.2.2.2.1.trans (Nat.div_le_self _ _)
  have tail : dir.entries*dir.description≤dir.teams*dir.processors*(dir.literal/2) := by
    rw [literalEq]
    change J₁*description≤(R₁+1)*(r₁)*(literal scales.α (l+1)/2)
    rw [← grid.count,Nat.mul_comm ((fan S)^T₁) copies₁]
    exact grid.geometricStorage.2.2.2.2
  obtain ⟨pack,shape⟩ := cal.locatedGateTable_shape grid qpos position (initial₁)
  let cells := CoverScale.sites (Cube D) (EnrichedOuter.depth S ((d₁)+1) T₁)
  let cables := (boundaryShape S ((d₁)+1) T₁).edges+4*(R₁+1)*tiles
  let depth := BottomReports.BundleSort.markedDepth cells J₁
  have cellEq : ar.cells=cells := by
    change CoverScale.sites (Cube D) (EnrichedOuter.depth S _ T₁) = _
    dsimp only [cells]
    rw [grid.depth_eq]
  have cableEq : ar.cables=cables := by
    change (boundary S _ T₁).edges+4*((R₁+1)*CoverScale.sites (Cube D) _)=_
    dsimp only [cables]
    rw [grid.depth_eq,grid.tiles_eq,Nat.mul_assoc]
    rfl
  have outs : t.outputs=PackedHistoryCircuit.TerminalCells.signedGridOutputCount ar.cables ar.cells
      dir.entries (dir.teams*dir.sites) 37 pack+(2^depth+2^depth) := by
    rw [cableEq,cellEq]
    exact shape
  exact ⟨guard,both.2,(guard.located_writer_fields pack depth outs short).1,
    (guard.located_writer_fields pack depth outs short).2,tail⟩

end Diagonal

end BorderVNP
end Computability
end OAI
