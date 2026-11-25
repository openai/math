import OAI.Computability.BorderVNP.DiagonalCalendarDeployment
import OAI.Computability.BorderVNP.PackedLocatedFrozenSemantics
import OAI.Computability.BorderVNP.DiagonalCalendarSourceRoom
import OAI.Computability.BorderVNP.PackedHistoryFrozenHeaderSelection

/-! # Real local acceptance and the clocked signed packet on calendar exteriors -/

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
open private profilePaths_eq from OAI.Computability.BorderVNP.PackedHistoryChosenReservedGeometry

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
local notation3 (prettyPrint := false) "seedStrings" => (cal.frozenWitness).seedLiteralMatrix position tag₁ sites₁ edges₁ ports₁
  copies₁ ((fan S)^T₁) (header*logWidth (r₁) (l+1))

set_option maxHeartbeats 14500000 in
set_option maxRecDepth 9000 in
/-- A real local geometry return on this calendar's literal tape exists
exactly for a unique original history. Every declaration with that same raw
profile then has the full real signed packet on each of its physical pins.
The packet, its local boot fields and the bound on its return clock refer to
the same actual RAM run. -/
theorem SignedCalendarAt.frozenSites_headers (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (p : headers₁) (first : HeaderExterior layout₁ p.bits) (team : Fin (R₁+1)) (live : Fin pins₁ → Bool) :
    let start := reader.siteOperandsWith prog₁ program₁ ordinary₁ loc₁ (geo₁).fits (layout₁).header team
    let initialFields := (wired₁).processorFields team live first.val start.layout.ibase start.layout.hbase start.layout.starbase
    Nonempty (Returns (withStartup pinGeometry) ((physical₁).publicWords team) mac₁ (registers₁ team)
      (processorMemory initialFields (w₁))) ↔
    ∃! h : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index, ((code₁ values) h).val=p.profile ∧
      ∀ (other : headers₁), other.profile=p.profile → ∀ (wire : HeaderExterior layout₁ other.bits) (u : Fin (R₁+1))
        (pin : Fin pins₁ → Bool) (mac : TeamOpcode.Macros w₁ 8) (bank : Bank w₁),
        let op := reader.siteOperandsWith prog₁ program₁ ordinary₁ loc₁ (geo₁).fits (layout₁).header u
        let pk := packet₁ u
        let pub := (physical₁).publicWords u
        let F := (wired₁).processorFields u pin wire.val op.layout.ibase op.layout.hbase op.layout.starbase
        let frame := (wired₁).transferFrame u (layout₁).header op.broadcastBase
        let mem := processorMemory F w₁
        let time := jointBudget pk.bits.length w₁+frame.readTicks+2+((pinSetup.slots+17*op.layout.count+1)+
          GeometryAdviceRate.ticks ceiling₁ cap₁ (located₁).outputs w₁ w₁)
        ∃ fields : Pins.ProcessorFields ((initial₁).operands u ad₁ pk).layout, HEq fields F ∧
          ProfilePaths (withStartup pinGeometry) op.layout.guessWidth pub mac bank mem True time origin₁
            (nativeTableWords (table₁) ((code₁ values) h).val)
            (BootResidence (F:=fields) initial₁ u ad₁ pk frame op.advice pub mac other.bits mem bank) := by
  intro start initialFields
  have room := cal.frozenSourceRoom grid qpos position chart reader chargeFit
  have size := (located₁).reserved_size
  have address := room.2.2.2.2.1
  rw [size] at address
  have header := (cal.frozenLayout_fields chart reader chargeFit).1
  have select := reader.frozen_profile_header_selection prog₁ program₁ ordinary₁ (geo₁).fits
    (fun u => (placed₁ u).valuation) (fun u => (placed₁ u).entry) (fun u => (placed₁ u).totals) (fun u => pin₁ u)
    layout₁ plan₁ tape₁ order₁ position cal.frozenWitness tag₁ sites₁ edges₁ ports₁ values x₁ wr₁ hm widths₁ slots₁ fit₁
    (emission₁ tape₁).emitter directory₁ ceiling₁ (signedBootStripe (freeStartWith prog₁ r₁ 32 64 w₁ (l+1)))
    (fun _ => []) seedStrings p (located₁).raw_bound (p.bits_length.trans header.symm)
    room.2.2.2.1 room.2.1 le_rfl address first team live mac₁ (registers₁ team)
  constructor
  · intro answer
    obtain ⟨h,⟨code,paths⟩,_⟩ := select.mp answer
    refine ⟨h,⟨code,?_⟩,?_⟩
    · intro other same wire u pin mac bank
      obtain ⟨fields,align,read⟩ := paths other same wire u pin mac bank
      have words := (reserved_semantics hist₁ readOrder fit₁ (emission₁ tape₁).emitter x₁ ceiling₁ ((code₁ values) h).val).2
      have dest := congrArg (fun z => Allocation.dest fresh₁ cap₁ z (located₁).outputs w₁) size
      exact ⟨fields,align,profilePaths_eq read Iff.rfl rfl dest.symm words.symm⟩
    · intro z matchCode
      apply (code₁ values).injective
      exact Subtype.ext (matchCode.1.trans code.symm)
  · rintro ⟨h,⟨_,paths⟩,_⟩
    obtain ⟨_,_,observed⟩ := paths p rfl first team live mac₁ (registers₁ team)
    exact observed.passes.mpr trivial

end Diagonal

end BorderVNP
end Computability
end OAI
