import OAI.Computability.BorderVNP.DiagonalCalendarResidentRoutingHeader
import OAI.Computability.BorderVNP.DiagonalCalendarFinishShape
import OAI.Computability.BorderVNP.DiagonalSignedCandidateSiteSelection

/-! # The emitted address, gate count and original header on a returned calendar candidate -/

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

attribute [local irreducible] Nat.clog UniversalMachine.programPrefix logWidth prefixCapacity
  FieldProcessor.freeWidth Fintype.equivFin
set_option maxRecDepth 8000
set_option maxHeartbeats 4500000
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

open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round Cover
open EnrichedOuter

attribute [local instance] portFintype

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

local notation3 (prettyPrint := false) "physical₁" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "program₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
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

local notation3 (prettyPrint := false) "blank₁" => TimedProcessor.scaleData (signedProgram (cube.cubeID paid)).program
  (siteLibrary SparseExterior.driver) (fun _ : Fin 8 => some false) (geo₁) (fun _ _ => 0) (fun _ _ => 0)
  (fun _ _ => false) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "board₁" => Fintype.card (Board.Physical (pairedTableParameters (l+1) (size₁))
  (budget₁+6) w₁ (paid.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width))
local notation3 (prettyPrint := false) "guessBoard" => Fintype.card (Guess (Fin (pairedTableParameters (l+1) (size₁)))
  reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))
local notation3 (prettyPrint := false) "ordinary₁" => SignedTaskArena.withOrdinary blank₁ (fun _ => selectedTask) initial₁
  (fun _ => origin₁) (fun _ => 0) (fun _ => board₁) (fun _ => guessBoard) (fun _ => reader.gates)
local notation3 (prettyPrint := false) "ad₁" => adviceOffsetWith (prog₁) r₁ 32 64 w₁ (l+1)

open Packing.RoutingOutputs


open RoutingISA.Evaluator.SignedPrep BorderVNP.Cube Physical

private theorem zero_suffix_le (cables cells entries live payload spare : ℕ) :
    TerminalCells.signedGridOutputCount cables cells entries live 37 0 ≤
      TerminalCells.signedGridOutputCount cables cells entries live 37 payload+spare := by
  dsimp only [TerminalCells.signedGridOutputCount]
  omega

/-- At a candidate retained by the selection of the real geometry return,
its own recorded gate packet supplies the public origin and all native tables.
This gives the initial address and emission capacity for the reporter before
the report allocation and the argument return are inspected. -/
theorem SignedCalendarAt.frozenCandidateEmissionInputs
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1)) (u : Fin (R₁+1))
    {copy : BroadcastFrame} {advice : AdviceLayout} {headerBits : List Bool}
    {machine : TeamOpcode.Macros w₁ 8} {reg : Bank w₁} {before after : Memory w₁}
    {size : ℕ} {g : Fin size → Bool}
    {fields : Pins.ProcessorFields ((initial₁).operands u ad₁ (packet₁ u)).layout}
    (held : BootResidence (F:=fields) initial₁ u ad₁ (packet₁ u) copy advice
      ((physical₁).publicWords u) machine headerBits before reg g after)
    {ar : CubeArena.Layout} {D₀ : Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {budget dim : ℕ}
    {word : Broadcast ar.n ar.header.d ar.header.cap} {owner : ℕ → Fin (R₁+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R₁+1)}
    {pins : Pins.Layout} {cellFields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {pub : Arg → Word w₁} {mac : TeamOpcode.Macros w₁ 8}
    {bank : Bank w₁} {mem : Memory w₁} {I : Type*} [Fintype I]
    {host : I → Fin ar.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {Port Operand : Type*} {widths : Port → ℕ} {net : Network dim Port widths}
    {cell : net.Site → Fin ar.cells} {recv : Operand → Fin ar.cells} {span : Operand → ℕ}
    (site : CandidateSite (X:=budget) ar D₀ pp lp word owner decl group (initial₁).frame (initial₁).next pins
      cellFields f guess pub mac bank mem host key sizes net cell recv span)
    {old : Fin 81 → Word w₁} {offset stride ctrl pad used cost : ℕ} {claims : List (List Bool)}
    {profile : Fin cap₁ → Bool} {out : Bank w₁}
    (attained : site.OnReturn old fresh₁ (table₁).size (located₁).outputs w₁ offset stride ctrl
      (List.ofFn profile) claims pad out after used cost) :
    let t := selectedTask
    let d := dir₁
    let fresh := (initial₁).next+7*d.candidates
    let origin := origin₁
    site.fresh=fresh ∧
      origin = Allocation.dest fresh site.profile.length site.gates site.outputs site.width ∧
      TerminalCells.signedGridOutputCount t.cube.cables t.cube.cells d.entries (d.teams*d.sites) 37 0 ≤ site.outputs ∧
      Header (pub 0).val origin t.cube.cables t.cube.cells d.entries (readings site.geometry) := by
  intro t d fresh origin
  have dirs : directory₁=d := (cal.frozenSourceRoom grid qpos position chart reader chargeFit).1
  have same : fresh₁=fresh := congrArg (fun v : Directory.Layout => (initial₁).next+7*v.candidates) dirs
  refine ⟨attained.first.trans same,?_,?_,?_⟩
  · rw [attained.copiedProfile,List.length_ofFn,attained.gateCount,attained.outputCount,attained.fieldWidth]
    exact congrArg (fun base => Allocation.dest base cap₁ (table₁).size (located₁).outputs w₁) same
  · rw [attained.outputCount]
    obtain ⟨wp,wd,chunks,arity,_⟩ := cal.locatedGateTable_finishShape grid qpos position initial₁
    have nc : t.cube.cells=CoverScale.sites (Cube D) (EnrichedOuter.depth S ((d₁)+1) T₁) := by
      change CoverScale.sites (Cube D) (EnrichedOuter.depth S _ T₁)=_
      rw [grid.depth_eq]
    have ne : t.cube.cables=(boundaryShape S ((d₁)+1) T₁).edges+4*(R₁+1)*tiles := by
      change (boundary S _ T₁).edges+4*((R₁+1)*CoverScale.sites (Cube D) _)=_
      rw [grid.depth_eq,grid.tiles_eq,Nat.mul_assoc]
      rfl
    rw [ne,nc,arity]
    change TerminalCells.signedGridOutputCount _ _ J₁ ((R₁+1)*tiles) 37 0 ≤ _
    exact zero_suffix_le ..
  · rw [site.origin,attained.geometryMemory]
    exact (cal.frozenResidence_routingHeader grid qpos position chart reader chargeFit routing u held).1

end Diagonal

end BorderVNP
end Computability
end OAI
