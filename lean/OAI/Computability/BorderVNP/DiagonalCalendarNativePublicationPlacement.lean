import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalCalendarReportOpenRoom
import OAI.Computability.BorderVNP.DiagonalCalendarSourceRoom
import OAI.Computability.BorderVNP.DiagonalPublishedSlottedReadback

/-! # Native geometry and physical placement at a calibrated planner return -/

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
local notation "J₁" => (fan S)^T₁*tiles
local notation "description" => seedDescriptionWidth (l+1) (r₁) axes (d₁) (header*logWidth (r₁) (l+1))
  (BottomGridBank.bodyBudget (seedBoxCapacity (l+1) (r₁) axes (d₁) (Fintype.card (Direction axes))))
local notation "cap₁" => SeedPlan.profileReserve (r₁) (l+1)
local notation "ceiling₁" => geometryGateCeiling (8*(11920000+1500000+16008100*coeff+37)) (4*(E+2)) (r₁) (l+1)
local notation3 (prettyPrint := false) "dir₁" => freeDirectory (R₁) (r₁)
  ((tape₁).program.length+(TeamContraction.cutWidth (l+1)+extra₁)) (ℓ₁) tiles (GridHosts.inputBlockWidth (r₁) (l+1) axes (d₁)) J₁ description

open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round Cover
open EnrichedOuter

attribute [local instance] portFintype

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
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁

open CellMacro.Generator RoutingISA.CompactMachine

open Packing.CellAddresses Packing.RoutingOutputs Packing.CellAddressPhysical
open ExternalSew.RowTrace ExternalSew.FieldExport GridHosts Packing.DeckGrid
open CellEntries JointHeader Routing

open Packing.RoutingOutputs Packing.CellAddresses TeamContraction.JointHeader CompactMachine
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Tally Cube.LabelIndex
local notation3 (prettyPrint := false) "networkCells" => Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "cables₁" => (boundaryShape S (d₁+1) T₁).edges+4*(R₁+1)*tiles
local notation3 (prettyPrint := false) "geometry₁" => (selectedTask).withNetwork networkCells cables₁

open Packing.RoutingOutputs Packing.Directory.PrivateBank

private theorem roomAtPlacement {ar br : SignedTaskArena.Layout} {frame base origin entries live rows w : ℕ}
    (same : ar=br) (head : frame=base)
    (room : ar.OpenRoom base (bases origin ar.cube.cables ar.cube.cells entries).ends
      (controlsBase origin ar.cube.cables ar.cube.cells entries live)
      (bases origin ar.cube.cables ar.cube.cells entries).livePairs live entries rows w) :
    br.OpenRoom frame (bases origin br.cube.cables br.cube.cells entries).ends
      (controlsBase origin br.cube.cables br.cube.cells entries live)
      (bases origin br.cube.cables br.cube.cells entries).livePairs live entries rows w := by
  cases same
  exact head ▸ room

private theorem installedPlacement {D p w d g : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {task : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits}
    {cell : N.Site → Fin task.cube.cells} {edge : N.Edge ↪ Fin task.cube.cables} {port : P ↪ Fin p}
    {original : Fin dir.entries → N.Site} {live : (Fin dir.teams × Fin dir.sites) ↪ P}
    {a : StartupArena} {u : Fin a.teams} {slot : ℕ} {packet : ReferencePacket w d} {origin gap : ℕ}
    {f : BroadcastFrame} {hdr : List Bool} {fields : Pins.ProcessorFields (a.operands u slot packet).layout}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {v : Fin g → Bool}
    {postPin regs : Bank w} {pinMem mem seen middle : Memory w} {used cost frame : ℕ} {br : SignedTaskArena.Layout}
    (pin : PublishedPin task dir N cell edge port original live a u slot packet origin gap f hdr fields pub mac v
      postPin pinMem regs mem used cost)
    (layout : task=br) (epoch : Returns epochPlacement pub mac postPin pinMem)
    (publication : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2)
    (head : frame=a.frame) (geometry : seen=mem) (middleEq : epoch.val.2.2=middle) :
    (privateLayout frame origin br.cube.cables br.cube.cells dir.entries dir.description gap).Image
      (readings seen) dir.entries (readings middle) := by
  cases layout
  rw [head,geometry,←middleEq]
  exact (PublishedPin.actual_slotted task dir N cell edge port original live a u slot packet origin gap f hdr
    fields pub mac v postPin pinMem regs mem used cost pin epoch publication).2.2.1

private theorem plannerPlacementRoom :
    (initial₁).frame+112 ≤ (initial₁).next ∧ (initial₁).next+7*(dir₁).candidates≤origin₁ := by
  constructor
  · dsimp only [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]
    omega
  · have dirs : directory₁=dir₁ := (cal.frozenSourceRoom grid qpos position chart reader chargeFit).1
    dsimp only [Allocation.dest,Allocation.temp]
    rw [dirs]
    omega

local notation3 (prettyPrint := false) "raw₁" => SignedTaskArena.rawAddress initial₁ (geometry₁).cube.header.profile
  (geometry₁).cube.n (geometry₁).cube.header.d (geometry₁).cube.header.cap

set_option maxHeartbeats 9000000 in
set_option maxRecDepth 15000 in
/-- In every genuine native pin receipt, the measured geometry memory and its
published epoch determine all placement and room fields of the planner site. -/
noncomputable def SignedCalendarAt.frozenNativePublicationPlacement
    {dim portCount packetDim g : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {N : Network dim P bits} {cell : N.Site → Fin (geometry₁).cube.cells}
    {edge : N.Edge ↪ Fin (geometry₁).cube.cables} {port : P ↪ Fin portCount}
    {original : Fin (dir₁).entries → N.Site} {live : (Fin (dir₁).teams × Fin (dir₁).sites) ↪ P}
    {team : Fin (R₁+1)} {slotTeam : Fin (initial₁).teams} {slot gap : ℕ}
    {packet : ReferencePacket w₁ packetDim} {bf : BroadcastFrame} {hdr : List Bool}
    {fields : Pins.ProcessorFields ((initial₁).operands slotTeam slot packet).layout}
    {pub : Arg → Word w₁} {mac : TeamOpcode.Macros w₁ 8} {guess : Fin g → Bool}
    {postPin regs : Bank w₁} {pinMem mem seen middle : Memory w₁} {used cost frame ctl : ℕ}
    {literalWords : Fin 81 → Word w₁}
    (literal : literalWords=routingExtension ((geometry₁).extension raw₁ team.val w₁ (signedBudgetWords w₁ outside₁))
      dir₁ origin₁ (geometry₁).cube.cables (geometry₁).cube.cells)
    (control : ctl=controlsBase origin₁ (geometry₁).cube.cables (geometry₁).cube.cells (dir₁).entries ((dir₁).teams*(dir₁).sites))
    (head : frame=(initial₁).frame)
    (pinReceipt : PublishedPin geometry₁ dir₁ N cell edge port original live initial₁ slotTeam slot packet
      origin₁ gap bf hdr fields pub mac guess postPin pinMem regs mem used cost)
    (epoch : Returns epochPlacement pub mac postPin pinMem)
    (publication : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2)
    (geometry : seen=mem) (middleEq : epoch.val.2.2=middle) :=
  let equal := cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit
  let real := (cal.frozenEarlyTask grid qpos position chart reader chargeFit).symm.trans equal
  let room := cal.frozenReportOpenRoom grid qpos position chart reader chargeFit
  let bounds := plannerPlacementRoom cal grid qpos position chart reader chargeFit
  let old := literal.trans (congrArg (fun t : SignedTaskArena.Layout =>
    routingExtension (t.extension raw₁ team.val w₁ (signedBudgetWords w₁ outside₁)) dir₁ origin₁
      t.cube.cables t.cube.cells) equal)
  let address := control.trans (congrArg (fun t : SignedTaskArena.Layout =>
    controlsBase origin₁ t.cube.cables t.cube.cells (dir₁).entries ((dir₁).teams*(dir₁).sites)) equal)
  let space := roomAtPlacement real head room
  let placed := installedPlacement pinReceipt equal epoch publication head geometry middleEq
  let low := (congrArg (fun base : ℕ => base+112≤(initial₁).next) head).mpr bounds.1
  PLift.up (And.intro old (And.intro address (And.intro space (And.intro placed (And.intro low bounds.2)))))

end Diagonal

end BorderVNP
end Computability
end OAI
