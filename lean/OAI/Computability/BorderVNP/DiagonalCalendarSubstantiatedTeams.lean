import OAI.Computability.BorderVNP.DiagonalCalendarOriginalHeader
import OAI.Computability.BorderVNP.DiagonalCalendarOriginalSourceFacts
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedAllocation
import OAI.Computability.BorderVNP.DiagonalSelectedSubstantiatedSourceFacts
import OAI.Computability.BorderVNP.DiagonalFrozenReportArena
import OAI.Computability.BorderVNP.DiagonalFrozenSourceParameters
import OAI.Computability.BorderVNP.PackedFrozenSeedInputs

/-! # Guarded completion for the issued teams at a fixed calendar frame -/

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
local notation3 (prettyPrint := false) "params₁" => (selectedTask).p
local notation3 (prettyPrint := false) "seeds₁" => fun t i z => ((ExternalSew.RowTrace.seedNumber S (d₁+1) t i) z).val

open CellMacro.Generator DiagonalTallyCellReports BorderVNP.Cube.Physical.NativeAssignments
attribute [local irreducible] CoreDirectory.preparedRoutedRows SeedPlan.SubstantiatedRequest

/-- Recover the particular candidate indexed by a proof about its issued rows. -/
private abbrev candidateOfRows {na nb nl nsym ncode nin nword nt ndigit outWidth : ℕ}
    {id : BorderVNP.Cube.TableEntry na nb nl nsym ncode → ℕ} {gen : Fragment IO}
    {X : UncheckedCandidate id gen nin nword nt ndigit outWidth} {report : Fin nt → ReportLayout}
    {cells : ∀ u,List (AssignedCell (report u))} (_ : X.UsesRows cells) := X

/-- Replace the parameter component after identifying the concrete arena. -/
private theorem withSourceParameters {arena : CubeArena.Layout}
    {id : BorderVNP.Cube.TableEntry arena.n arena.b arena.h arena.K arena.s → ℕ}
    {installed : SignedTaskArena.Layout} {source stored : SignedTaskArena.Parameters}
    (layout : installed=⟨arena,id,stored⟩) (parameters : source=stored) :
    installed=⟨arena,id,source⟩ := by
  cases parameters
  exact layout

local notation3 (prettyPrint := false) "columns" => (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F
local notation3 (prettyPrint := false) "axisCount" => BorderVNP.Cube.alphabet scales.α (l+1)

set_option cleanup.letToHave false in
private noncomputable def originalTeamsCompletions
    (values : columns) (X₀ : Type)
    (teams : X₀ → Fin (R₁+1) → PositiveTeam (cube.cubeID paid) SparseExterior.driver (l+1) w₁)
    (teamFrame : ∀ x u,((teams x u).pub 0).val=(initial₁).frame) : (statement : Prop) ×' statement :=
  let bounds := cal.frozenSpliceBounds grid
  let leaf := (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ values x₁
  let words := (geoSeed).eval x₁
  let fields := (Boundary.seedBirthPrograms S order₁ position W₁ tag₁ sites₁ edges₁ ports₁ values words).bankFields
  have cover : (CoverScale.sites (Cube D) (d₁+1):ℝ) ≤ r₁*((l+1:ℕ):ℝ)^(9/10:ℝ) := by
    rw [grid.depth_eq]
    exact cal.length.cover.2.2.2.1
  have capBound := (plan₁).frozenLeaf_bankCap tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ values x₁
  let complete := fun (capacity : ℕ) => (plan₁).substantiatedRequestWithSourceFacts (D:=D) (m:=«m») (e:=paid) (S:=S)
    (R:=R₁) (r:=r₁) («pin»:=budget₁+6) (link:=ℓ₁) (k:=l) (d:=d₁) (a:=extra₁) (s:=size₁)
    (regs:=64) (rw:=w₁) (ec:=ec₁) (width:=w₁+1)
    (copies:=copies₁) (T:=T₁) (header:=header) (order:=order₁) (digits:=w₁)
    (gen:=SparseExterior.driver) (reserve:=cap₁) (groups:=axisCount) (capacity:=capacity)
    cube φ ord chart prog₁ (geo₁).fits W₁ position sites₁ edges₁ ports₁ values words leaf.property
    seeds₁ free₁ grid.count bounds.2.1 scales.α ξ₁ bounds.1 (geo₁).literalSize bounds.2.2 number₁
    (selectedTask).cube (params₁).sourceDirectories (params₁).report.bundles (params₁).report.marked
    (Nat.clog 2 (r₁*(2*l+1)+1)) w₁ (params₁).siteWidth (params₁).bodyCap
    scales b cal.tally rfl rfl rfl rfl rfl fields cover cal.seed.choose_spec.choose_spec.2.2.2.2 capBound le_rfl
  have digitsEq : w₁=b.physical.tally (l+1) :=
    (b.sizes (Nat.succ_pos l)).2.2.1.trans (b.sizes (Nat.succ_pos l)).2.2.2.1.symm
  have layoutEq := withSourceParameters (b.frozenSignedTask_reportLayout cube l size₁ header (initial₁) (dir₁) cap₁ ceiling₁
    (located₁).outputs w₁ (located₁).directories rfl grid.depth_eq.symm rfl rfl number₁)
    (b.frozenSignedTask_sourceParameters cube l size₁ header (initial₁) (dir₁) cap₁ ceiling₁
      (located₁).outputs w₁ (located₁).directories)
  have localScale := grid.issuedReportScale (by omega)
  let originalAt := cal.frozenOriginalFactsOnTeams grid qpos position chart reader chargeFit values teams
  let result := fun prep base ownerTable issued raw h v guard =>
      let received := originalAt prep base ownerTable issued raw h v teamFrame
      let assigned := candidateOfRows received.1
      let hdr := cal.frozenOriginalHeader grid qpos position chart reader chargeFit values h v
      complete _ assigned hdr (fun _ => initial₁) arenaBase cap₁ (initial₁).frame origin₁
        digitsEq hm (stretch_one ..) (grid.block_le.trans_eq grid.link_eq) (cube.scalarDictionary_positive paid)
        (fun z => cube.scalarNumber_le_last paid (.inl z)) (cost:=1) (breadth:=breadth) (exponent:=E+2)
        (steps:=sourcePower) (by rw [one_mul]; exact localScale)
        cal.privateCell cal.sourceDigits rfl raw h ⟨v,guard⟩ received selectedTask layoutEq
  ⟨_,result⟩

/-- On each guarded source from the actual issued producer, the original
per-team rows, preservation of every protected operand, and full original
column sum all belong to the same completion of the installed candidate. -/
theorem SignedCalendarAt.frozenSubstantiatedOfTeams
    (values : columns) (X₀ : Type)
    (teams : X₀ → Fin (R₁+1) → PositiveTeam (cube.cubeID paid) SparseExterior.driver (l+1) w₁)
    (teamFrame : ∀ x u,((teams x u).pub 0).val=(initial₁).frame) :
    (originalTeamsCompletions cal grid qpos position chart reader chargeFit values X₀ teams teamFrame).1 :=
  (originalTeamsCompletions cal grid qpos position chart reader chargeFit values X₀ teams teamFrame).2

end Diagonal

end BorderVNP
end Computability
end OAI
