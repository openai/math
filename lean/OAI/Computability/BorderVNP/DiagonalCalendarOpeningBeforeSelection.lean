import OAI.Computability.BorderVNP.DiagonalCalendarCommonFrame
import OAI.Computability.BorderVNP.DiagonalCalendarResidentTaskFrame
import OAI.Computability.BorderVNP.DiagonalCalendarArgumentHeader
import OAI.Computability.BorderVNP.DiagonalCalendarOpeningFields
import OAI.Computability.BorderVNP.DiagonalCalendarSortedOutputWords
import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalCalendarNativePublishCells
import OAI.Computability.BorderVNP.DiagonalCalendarCanonicalPaths
import OAI.Computability.BorderVNP.DiagonalCalendarHeaderBoot
import OAI.Computability.BorderVNP.DiagonalCalendarPlacementExtents
import OAI.Computability.BorderVNP.DiagonalCalendarPublishedImage
import OAI.Computability.BorderVNP.DiagonalCalendarEarlyParameters
import OAI.Computability.BorderVNP.DiagonalCalendarPublishOperands
import OAI.Computability.BorderVNP.DiagonalCalendarPublicationRoom
import OAI.Computability.BorderVNP.DiagonalCalendarPublishSpace
import OAI.Computability.BorderVNP.PackedFrozenDirectoryPublication

/-! # The signed planner operands on the original returned startup memory -/

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


open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round Cover
open EnrichedOuter

attribute [local instance] portFintype
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "wr₁" => cal.seed.choose_spec.choose
local notation3 (prettyPrint := false) "inputs₁" => grid.packet_inputs φ q adv c charge factor coeff cal.output
  (tape₁) (grid.template_directory (pins₁) (geo₁)).1 grid.link_eq.symm (order₁) position description

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
local notation3 (prettyPrint := false) "task₁" => b.frozenSignedTask cube (l+1) l (size₁) header (initial₁)
  (dir₁) cap₁ ceiling₁ (located₁).outputs (w₁) (located₁).directories


local notation3 (prettyPrint := false) "physical₁" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "program₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "wired₁" => wiringWith (prog₁) (program₁) physical₁ (pins₁) (ℓ₁) (l+1) ec₁ (geo₁).fits
local notation3 (prettyPrint := false) "emission₁" late => SeedPlan.locatedFrozenEmission (tape₁) (order₁) position
  cal.frozenWitness cube b (initial₁) l (size₁) coeff grid.count grid.block_pos (grid.block_le.trans_eq grid.link_eq)
  grid.sites_pos inputs₁ late
local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false
local notation3 (prettyPrint := false) "base₁" => (plan₁).frozenStart (tape₁) (order₁) position Unit
local notation3 (prettyPrint := false) "widths₁" => fun i => Fintype.card (Machine.Guess S (d₁+1)
  (fun _ _ => 60*logWidth (r₁) (l+1)) i)
local notation3 (prettyPrint := false) "slots₁" => fun i => Fintype.equivFin (Machine.Guess S (d₁+1)
  (fun _ _ => 60*logWidth (r₁) (l+1)) i)
local notation3 (prettyPrint := false) "head₁" => WorkWords.grouped (CoverScale.sites (Cube D) (d₁+1))
  (copies₁*GridHosts.inputBlockWidth (r₁) (l+1) axes d₁)
local notation3 (prettyPrint := false) "key₁" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d₁))
local notation3 (prettyPrint := false) "fmt₁" => Boundary.seedFormat (tape₁) (order₁) position copies₁
local notation3 (prettyPrint := false) "steps₁" => (plan₁).compiled.tapeSteps (fmt₁) (head₁) (key₁) wr₁ hm
local notation3 (prettyPrint := false) "hist₁" => compile steps₁ T₁ le_rfl (repeatLeaf (fan S) base₁ T₁)
local notation3 (prettyPrint := false) "cells₁" => CoverScale.sites (Cube D) (EnrichedOuter.depth S (d₁+1) T₁)
local notation3 (prettyPrint := false) "fit₁" => (plan₁).profile_order_fits widths₁ slots₁
local notation3 (prettyPrint := false) "readOrder" => broadcastOrder (fan S) widths₁ slots₁ T₁
local notation3 (prettyPrint := false) "seed₁" v => (plan₁).frozenLeaf (tape₁) (order₁) position cal.frozenWitness tag₁
  sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute (tape₁) (order₁) position Unit).choose
local notation3 (prettyPrint := false) "code₁" v => (plan₁).compiled.machine.nativeCode (seed₁ v) geoSeed x₁ rfl widths₁ slots₁ fit₁

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "route₁" => routingExtension (signedBudgetWords w₁ outside₁)
  directory₁ origin₁ (selectedTask).cube.cables (selectedTask).cube.cells
local notation3 (prettyPrint := false) "placed₁" u => reader.frozenTaskPlacement selectedTask initial₁ u route₁
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


open CellMacro.Generator RoutingISA.CompactMachine


local notation3 (prettyPrint := false) "registers₁" => (physical₁).registers
local notation3 (prettyPrint := false) "mac₁" => TeamSiteEvents.macros (w:=w₁) (siteLibrary SparseExterior.driver) (nativeClock (l+1))
local notation3 (prettyPrint := false) "blank₁" => TimedProcessor.scaleData (signedProgram (cube.cubeID paid)).program
  (siteLibrary SparseExterior.driver) (fun _ : Fin 8 => some false) (geo₁) (fun _ _ => 0) (fun _ _ => 0)
  (fun _ _ => false) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "board₁" => Fintype.card (Board.Physical (pairedTableParameters (l+1) (size₁))
  (budget₁+6) w₁ (paid.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width))
local notation3 (prettyPrint := false) "guessBoard" => Fintype.card (Guess (Fin (pairedTableParameters (l+1) (size₁)))
  reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))
local notation3 (prettyPrint := false) "ordinary₁" => SignedTaskArena.withOrdinary blank₁ (fun _ => selectedTask) initial₁
  (fun _ => origin₁) (fun _ => 0) (fun _ => board₁) (fun _ => guessBoard) (fun _ => reader.gates)
local notation3 (prettyPrint := false) "loc₁" => fun j : Fin (R₁+1) => ReaderPlacement.inArena initial₁
  (placed₁ j).valuation (placed₁ j).entry (placed₁ j).totals (fields₁ j)
local notation3 (prettyPrint := false) "ad₁" => adviceOffsetWith (prog₁) r₁ 32 64 w₁ (l+1)
local notation3 (prettyPrint := false) "headers₁" => JointHeader.PositiveFields cap₁ (selectedTask).cube.n
  (selectedTask).cube.header.d (selectedTask).cube.header.cap (R₁+1) (selectedTask).dim (b.physical.tally (l+1))
open Packing.CellAddresses Packing.RoutingOutputs Packing.CellAddressPhysical
open ExternalSew.RowTrace ExternalSew.FieldExport GridHosts Packing.DeckGrid
open CellEntries JointHeader Routing

local notation3 (prettyPrint := false) "address₁" => fun u : Fin (R₁+1) => (initial₁).unitAddresses ad₁ (packet₁ u)
local notation3 (prettyPrint := false) "frame₁" u => (wired₁).transferFrame u (layout₁).header (initial₁).broadcastBase
local notation3 (prettyPrint := false) "owners₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "free₁" => (physical₁).enrichedFree prog₁ program₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "netAt[" v "," h "]" =>
  EnrichedTape.network (pins:=pins₁) prog₁ (geo₁).fits position free₁ grid.count
    (plan₁).compiled.machine (seed₁ v) rfl h
local notation3 (prettyPrint := false) "stageAt[" v "," h "]" => ((packHistory (seed₁ v) (plan₁).compiled.machine.epoch T₁).term h).val
local notation3 (prettyPrint := false) "cellsAt[" v "," h "]" => fun site : (netAt[v,h]).Site =>
  owners₁ (reduceMove (EnrichedOuter.depth S (d₁+1) T₁) ((stageAt[v,h]).route.origin site))
local notation3 (prettyPrint := false) "params₁" => (⟨R₁,r₁,(wired₁).program.length+(cutWidth (l+1)+extra₁),ℓ₁,
  GridHosts.inputBlockWidth r₁ (l+1) axes d₁,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "valid₁" => (⟨grid.block_pos,grid.block_le.trans_eq grid.link_eq,
  gridRoom wired₁ Fintype.card_pos⟩ : (params₁).Valid)
local notation3 (prettyPrint := false) "edgesAt[" v "," h "]" => mergedEdges params₁ valid₁ ((stageAt[v,h]).rows.edge)
local notation3 (prettyPrint := false) "portsAt" => (finProdFinEquiv : FreeBlock R₁ tiles ≃ Fin ((R₁+1)*tiles)).toEmbedding
local notation3 (prettyPrint := false) "hostsAt[" v "," h "]" => originalDescriptionRows (plan₁).compiled.machine (seed₁ v) h dir₁ rfl order₁
local notation3 (prettyPrint := false) "livePorts" => (Equiv.refl (FreeBlock R₁ tiles)).toEmbedding
local notation3 (prettyPrint := false) "lib₁" => install SparseExterior.driver (l+1) mac₁
local notation3 (prettyPrint := false) "nativeTime" u => jointBudget (packet₁ u).bits.length w₁+(frame₁ u).readTicks+2+
  ((pinSetup.slots+17*((initial₁).operands u ad₁ (packet₁ u)).layout.count+1)+GeometryAdviceRate.ticks
  ceiling₁ cap₁ (located₁).outputs w₁ w₁)
local notation3 (prettyPrint := false) "concreteTask" => (selectedTask).withNetwork
  (Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1)))
  ((boundaryShape S (d₁+1) T₁).edges+4*(R₁+1)*tiles)

set_option maxHeartbeats 13000000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5500000 in
/-- A single physical startup trace and its published geometry and original
output words authenticate every local operand of the native opener. -/
theorem SignedCalendarAt.frozenOpeningStartOfEvidence
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (h : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index)
    (u : Fin (R₁+1)) {k : ℕ} {pf : Pins.ProcessorFields ((initial₁).operands u ad₁ (packet₁ u)).layout}
    {bf : BroadcastFrame} {advice : AdviceLayout} {lib : TeamOpcode.Macros w₁ 8} {copy : List Bool}
    {init after postPin : Memory w₁} {bank placedPin regs : Bank w₁} {digits : Fin k → Bool} {used elapsed : ℕ}
    (resident : BootResidence (F:=pf) initial₁ u ad₁ (packet₁ u) bf advice ((physical₁).publicWords u)
      lib copy init bank digits after)
    (published : PublishedPin concreteTask dir₁ (netAt[values,h]) (cellsAt[values,h]) (edgesAt[values,h]) portsAt
      (hostsAt[values,h]) livePorts initial₁ u ad₁ (packet₁ u) origin₁ (selectedTask).p.privateGap bf copy pf
      ((physical₁).publicWords u) lib digits placedPin postPin regs after used elapsed)
    (image : cal.frozenPacketImage grid qpos position chart reader chargeFit values h (readings after))
    (written : ∀ j : Fin (located₁).outputs, readings after (origin₁+j.val)=nativeTableWords table₁ ((code₁ values) h).val j) :
    let t := cal.frozenPlannerTask grid qpos position chart reader chargeFit
    let base := ((physical₁).publicWords u 0).val
    let ctl := controlsBase origin₁ t.cube.cables t.cube.cells (dir₁).entries ((dir₁).teams*(dir₁).sites)
    Header base origin₁ t.cube.cables t.cube.cells (dir₁).entries (readings after) ∧
    (privateLayout base origin₁ t.cube.cables t.cube.cells (dir₁).entries (dir₁).description t.p.privateGap).Fits w₁
      (readings after) ∧ (∀ j : Fin 37,readings after (ctl+j.val)=t.controls j.val) ∧
    cal.frozenSortedBundleWords grid qpos position chart reader chargeFit values h (readings after) := by
  intro t base ctl
  obtain ⟨_,_,_,_,_,_,_,_,_,_,fits,_⟩ := published
  have head := cal.frozenArgumentHeader grid qpos position chart reader chargeFit routing u _ _ _ _ _ _ _ _ _ resident
  have native := cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit
  have early := cal.frozenEarlyTask grid qpos position chart reader chargeFit
  have same := native.symm.trans early
  have fp := cal.frozenSites_frame grid qpos position chart reader chargeFit u
  have dirs : directory₁=dir₁ := (cal.frozenSourceRoom grid qpos position chart reader chargeFit).1
  refine ⟨?_,?_,?_,?_⟩
  · dsimp only [t,base]
    rw [same]
    simpa only [dirs] using head
  · dsimp only [t,base]
    rw [←native,fp]
    exact fits
  · intro j
    dsimp only [ctl,t]
    rw [←native,(located₁).reserved_size]
    exact (image.2.1 j).trans (congrArg (fun t : SignedTaskArena.Layout => t.controls j.val) early).symm
  · apply cal.frozenSortedBundleWords_of_output grid qpos position chart reader chargeFit values h
    intro j
    simpa only [←dirs] using written j

set_option maxHeartbeats 4500000 in
/-- The opening and later argument readers use the same unmodified startup
registers and report-arena bounds on this actual planner. -/
theorem SignedCalendarAt.frozenOpeningWordsOfResidence
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1)) (u : Fin (R₁+1)) {k : ℕ}
    {pf : Pins.ProcessorFields ((initial₁).operands u ad₁ (packet₁ u)).layout}
    {bf : BroadcastFrame} {advice : AdviceLayout} {lib : TeamOpcode.Macros w₁ 8} {copy : List Bool}
    {init after : Memory w₁} {bank : Bank w₁} {digits : Fin k → Bool}
    (resident : BootResidence (F:=pf) initial₁ u ad₁ (packet₁ u) bf advice ((physical₁).publicWords u)
      lib copy init bank digits after) :
    let t := cal.frozenPlannerTask grid qpos position chart reader chargeFit
    let base := ((physical₁).publicWords u 0).val
    let ptr := bases origin₁ t.cube.cables t.cube.cells (dir₁).entries
    let ctl := controlsBase origin₁ t.cube.cables t.cube.cells (dir₁).entries ((dir₁).teams*(dir₁).sites)
    t.OpenFields u.val base ptr.ends ctl ptr.livePairs ((dir₁).teams*(dir₁).sites) (dir₁).entries (readings after) ∧
    readings after (base+30)=w₁ ∧ readings after (base+14)=t.before.limit ∧
    readings after (base+89)=(t.tasks 0 0 0 0).tasks := by
  have opening := cal.frozenOpeningFields grid qpos position chart reader chargeFit routing u _ _ _ _ _ _ _ _ _ resident
  have regs := cal.frozenResidence_task_words grid qpos position chart reader chargeFit routing u resident
  have same := (cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit).symm.trans
    (cal.frozenEarlyTask grid qpos position chart reader chargeFit)
  have fp := cal.frozenSites_frame grid qpos position chart reader chargeFit u
  have dirs : directory₁=dir₁ := (cal.frozenSourceRoom grid qpos position chart reader chargeFit).1
  dsimp only at opening ⊢
  rw [same,fp]
  exact ⟨by simpa only [dirs] using opening,regs⟩

end Diagonal

end BorderVNP
end Computability
end OAI
