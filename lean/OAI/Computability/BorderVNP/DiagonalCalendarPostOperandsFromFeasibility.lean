import OAI.Computability.BorderVNP.DiagonalSourceReadbackAt
import OAI.Computability.BorderVNP.DiagonalCalendarFeasiblePost
import OAI.Computability.BorderVNP.DiagonalCalendarCommonFrame
import OAI.Computability.BorderVNP.RoutingISAScheduleClockWindows
import OAI.Computability.BorderVNP.DiagonalOriginalPostWriterFamily

/-! # The deployed physical post operands on an original positive processor prefix -/

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
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

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
local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation "qdim" => pairedTableParameters (l+1) size₁+Fintype.card identifiers
local notation3 (prettyPrint := false) "fullPin" h => (boxPinCodec (pairedTableParameters (l+1) size₁) reader.rankFits reader.boxFits).encode h

open RoutingISA.Evaluator.ScheduleClock TeamContraction.JointHeader
local notation3 (prettyPrint := false) "wired₁" => CellEntries.SewnTape.wiring (regs:=64) (w:=w₁) (ec:=ec₁)
  (width:=w₁+1) prog₁ (geo₁).fits free₁ pins₁
local notation "params₁" => pairedTableParameters (l+1) (size₁)
local notation "scalars₁" => Fintype.card (paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
local notation "public₁" => ⌈publicWork (cube.pred+1) scales.α (r₁) (l+1) (R₁+1)⌉₊
local notation "local₁" => ⌈localWork (cube.pred+1) (E+2) scales.α (ξ₁) (r₁) (l+1) (R₁+1)⌉₊
local notation "route₁" => 512*(cube.pred+1+BorderVNP.Cube.Tally.selectorWidth cube.pred cube.copies cube.h+1)
local notation3 (prettyPrint := false) "fixed₁" => (CubeConstants.install (cube.cubeID paid)).slots
local notation "argWidth" => BorderVNP.Cube.Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width
local notation "finish₁" => ScheduleClock.cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width argWidth
local notation "read₁" => BorderVNP.Cube.TeamRowClock.physicalCoefficient cube.pred cube.b cube.h cube.copies cube.width

local notation "readerInputs" => Fintype.card (Board.Physical params₁ (budget₁+6) w₁ identifiers)
local notation "selectedCost" => uniformWindows r₁ (R₁+1) outside₁ public₁ local₁ route₁ fixed₁ finish₁ read₁


local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "ctl₁" => RoutingOutputs.controlsBase origin₁
  (selectedTask).cube.cables (selectedTask).cube.cells (directory₁).entries ((directory₁).teams*(directory₁).sites)
local notation3 (prettyPrint := false) "offsets₁" =>
  (RoutingOutputs.bases origin₁ (selectedTask).cube.cables (selectedTask).cube.cells (directory₁).entries).ends
local notation3 (prettyPrint := false) "guesses₁" => Fintype.card (Guess (Fin params₁) reader.gridRank
  (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))

local notation3 (prettyPrint := false) "publicRoute" => routingExtension (signedBudgetWords w₁ outside₁)
  directory₁ origin₁ (selectedTask).cube.cables (selectedTask).cube.cells
local notation3 (prettyPrint := false) "placed₁" u => reader.frozenTaskPlacement selectedTask initial₁ u publicRoute
local notation3 (prettyPrint := false) "pin₁" u => CubeHeaderInstall.pinFields (placed₁ u).extension
  (Allocation.stop fresh₁ cap₁ (table₁).size (located₁).outputs w₁ w₁) (selectedTask).cube.header.d
  ((selectedTask).cube.n+1) ((selectedTask).cube.h*(selectedTask).cube.b) (selectedTask).cube.header.blocks cap₁
  (BorderVNP.Cube.Physical.declarationCap (selectedTask).cube.n (selectedTask).cube.header.d
    (selectedTask).cube.header.blocks (selectedTask).cube.b (selectedTask).cube.h (selectedTask).cube.s)
local notation3 (prettyPrint := false) "stripe₁" => GeometryAdviceRate.stripeWidth
  (GeometryOutput.packetCount cap₁ (table₁).size (located₁).outputs w₁*w₁) r₁
local notation3 (prettyPrint := false) "fields₁" u => Allocation.fields (pin₁ u) fresh₁ cap₁ (table₁).size
  (located₁).outputs w₁ ((initial₁).literal/4) stripe₁
local notation3 (prettyPrint := false) "packet₁" u => reader.packetAt (ReaderPlacement.inArena initial₁
  (placed₁ u).valuation (placed₁ u).entry (placed₁ u).totals (fields₁ u))


local notation3 (prettyPrint := false) "ad₁" => adviceOffsetWith (prog₁) r₁ 32 64 w₁ (l+1)
local notation3 (prettyPrint := false) "rawTally" => SignedTaskArena.rawAddress initial₁
  (selectedTask).cube.header.profile (selectedTask).cube.n (selectedTask).cube.header.d (selectedTask).cube.header.cap

open TeamContraction.JointHeader
local notation3 (prettyPrint := false) "boot(" live ")" => (boots₁).2.choose live

/-- Static feasibility on the actual deployed packet, control pointer and team count. -/
def SignedCalendarAt.NativeWriterFeasibility : Prop :=
  let task := selectedTask
  let sorts := cal.frozenPacketSortShape grid position
  task.DeployedFeasiblePost initial₁ directory₁ ctl₁ cap₁ cube.pred (BorderVNP.Cube.alphabet scales.α (l+1))
        task.cube.header.cap w₁ readerInputs guesses₁ reader.gates pins₁ r₁ sorts.1 sorts.2.1
        (Nat.clog 2 (r₁*(2*l+1)+1)) outside₁
        ⌈publicWork (task.cube.n+1) scales.α r₁ (l+1) (R₁+1)⌉₊
        ⌈localWork (task.cube.n+1) (E+2) scales.α ξ₁ r₁ (l+1) (R₁+1)⌉₊ reader.charge (R₁+1) params₁ scalars₁

/-- All physical requests on the positive starts of the selected calendar. -/
noncomputable def SignedCalendarAt.NativeWriterFamily (live : Fin pins₁ → Bool) : Type :=
  BootedPinStart.OriginalWriterFamily selectedTask (boot(live)) layout₁ hold₁

set_option cleanup.letToHave false in
set_option maxHeartbeats 6500000 in
set_option maxRecDepth 16000 in
/-- At the installed grid, any actual positive startup, original prefix and
observed public fields determine the complete physical post operands. -/
noncomputable def SignedCalendarAt.postOperandsWithFeasible
    (feasible : cal.NativeWriterFeasibility grid qpos position chart reader chargeFit)
    (live : Fin pins₁ → Bool)
    : cal.NativeWriterFamily grid qpos position chart reader chargeFit live :=
  fun x active u fields seen =>
    let b₀ := boot(live)
    let node := b₀ x u
    have keptSource : BootedPinStart.PublishedSourceReadback selectedTask (b₀ x) active u initial₁ fields origin₁
        (6+3*reader.gates+readerInputs) pins₁ :=
      BootedPinStart.PublishedReadbackFamily.readAt selectedTask b₀
        (cal.frozenPublishedReadback grid qpos position chart reader chargeFit hold₁ live)
        x active u fields seen
    have baseAt : (node.start.pub 0).val=(initial₁).frame :=
      congrFun (cal.frozenSites_frames grid qpos position chart reader chargeFit) u
    let request : FragmentRows.WriterPostRequest selectedTask (b₀ x) active u := {
      directory := directory₁
      offsets := offsets₁
      control := ctl₁
      liveStart := (RoutingOutputs.bases origin₁ (selectedTask).cube.cables (selectedTask).cube.cells (directory₁).entries).livePairs
      portCount := (directory₁).teams*(directory₁).sites
      limit := outside₁
      budget := (selectedCost).argumentsCalls
      startup := initial₁
      reserve := cap₁
      «axes» := cube.pred
      groups := BorderVNP.Cube.alphabet scales.α (l+1)
      cap := (selectedTask).cube.header.cap
      query := readerInputs
      guesses := guesses₁
      gates := reader.gates
      indexWidth := pins₁
      parameters := params₁
      scalars := scalars₁
      batch := r₁
      length := l+1
      logPower := E+2
      readerTicks := reader.charge
      alpha := scales.α
      exponent := ξ₁
      wp := (cal.frozenPacketSortShape grid position).1
      wd := (cal.frozenPacketSortShape grid position).2.1
      privateSize := Nat.clog 2 (r₁*(2*l+1)+1)
      fields := fields
      head := baseAt
      feasible := feasible
      destination := origin₁
      readback := keptSource
      team := u
      slot := ad₁
      packet := packet₁ u
      copy := (wiringWith prog₁ P₁ selectedSites pins₁ ℓ₁ (l+1) ec₁ (geo₁).fits).transferFrame u (layout₁).header (initial₁).broadcastBase
      advice := ((initial₁).unitAddresses ad₁ (packet₁ u)).advice
      layout := cal.frozenPublicationPinLayout grid qpos position chart reader chargeFit u
      gap := (selectedTask).p.privateGap
      base := signedBudgetWords w₁ outside₁
      packetOrigin := origin₁
      cables := (selectedTask).cube.cables
      cells := (selectedTask).cube.cells
      rawBase := rawTally
      who := u.val
      subtotal := w₁
      fresh := fresh₁
      areaSlots := cap₁
      gateCount := (table₁).size
      outputs := (located₁).outputs
      width := w₁
      off := (initial₁).literal/4
      stripe := stripe₁
      literal := cal.frozenPublicationLiteral grid qpos position chart reader chargeFit u }
    request

end Diagonal

end BorderVNP
end Computability
end OAI
