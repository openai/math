import OAI.Computability.BorderVNP.DiagonalCalendarLocatedEmitter
import OAI.Computability.BorderVNP.DiagonalCalendarPacketNumerals
import OAI.Computability.BorderVNP.DiagonalCalendarControlWords
import OAI.Computability.BorderVNP.PackedFrozenDirectoryPublication

/-! # The forwarded task and native gate table of a calendar prefix -/

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
set_option maxHeartbeats 5500000
attribute [local irreducible] Nat.clog Fintype.card Finset.univ

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


local notation3 (prettyPrint := false) "program₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "emission₁" late => cal.locatedEmitter grid position (initial₁) late
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

local notation3 (prettyPrint := false) "num₁" => (fun z : paid.Entry => cube.scalarNumber paid (.inl z))

open Packing.RoutingOutputs Packing.Inherited.FrozenTape BottomReports CellPacketGeometry TerminalCells

local notation3 (prettyPrint := false) "owners₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation "hooks₁" => Fintype.card (paid.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(dir₁).candidates
local notation3 (prettyPrint := false) "dest₁" => Allocation.dest fresh₁ cap₁ ceiling₁ (located₁).outputs w₁
local notation3 (prettyPrint := false) "actualTask" => cal.frozenTask grid qpos position chart reader chargeFit

local notation "short₁" => 60*logWidth (r₁) (l+1)
local notation "live₁" => (R₁+1)*tiles
local notation3 (prettyPrint := false) "sh₁" => boundaryShape S (d₁+1) T₁
local notation3 (prettyPrint := false) "cables₁" => (sh₁).edges+4*(R₁+1)*tiles
local notation3 (prettyPrint := false) "updated" => (actualTask).withNetwork cells₁ cables₁

/-- Recomputing the selected history's numbers of receiving cells and cables
installs the same task on the physical calendar. -/
theorem SignedCalendarAt.frozenEarlyTask : updated = actualTask := by
  have cellEq : (actualTask).cube.cells=cells₁ := by
    change CoverScale.sites (Cube D) (EnrichedOuter.depth S _ T₁) = _
    rw [grid.depth_eq]
  have cableEq : (actualTask).cube.cables=cables₁ := by
    change (boundary S _ T₁).edges+4*((R₁+1)*CoverScale.sites (Cube D) _) = _
    rw [grid.depth_eq,grid.tiles_eq,Nat.mul_assoc]
    rfl
  exact (congrArg₂ (actualTask).withNetwork cellEq.symm cableEq.symm).trans
    (SignedTaskArena.Layout.withNetwork_self _)

/-- The reinstalled packet contains all 37 full native controls. -/
theorem SignedCalendarAt.frozenEarlyControlFits (i : Fin 37) : (updated).controls i.val<2^w₁ := by
  rw [cal.frozenEarlyTask grid qpos position chart reader chargeFit]
  exact cal.frozenTask_controlWords grid qpos position chart reader chargeFit i

local notation3 (prettyPrint := false) "sources₁" => (ProgramSchemas.epoch S (d₁+1) short₁ fmt₁ T₁).schema.append
  (Sewn.schema (2*(sh₁).edges+6*(R₁+1)*tiles) short₁)
local notation3 (prettyPrint := false) "last₁" => FinalTies.tieSchema cables₁ live₁ w₁

set_option maxHeartbeats 9000000 in
/-- Lowering the complete packet on the initial physical wiring with full-word
controls yields the table installed in the selected calendar. -/
theorem SignedCalendarAt.frozenEarlyGateTable
    (wideSites : (sh₁).sites<2^w₁) (rowWidths : ∀ j, (sources₁).width j≤w₁)
    (padded : (CellPacketGeometry.History.roster (sh₁).sites sources₁ last₁).length<2^w₁) :
    let blank := TimedProcessor.scaleData (signedProgram (cube.cubeID paid)).program
      (siteLibrary SparseExterior.driver) (fun _ : Fin 8 => some false) (geo₁)
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)
    let actual := wiringWith prog₁ program₁ blank pins₁ ℓ₁ (l+1) ec₁ (geo₁).fits
    let task := actualTask
    let labels := cal.frozenPacketTags grid position
    let small := (cal.frozenPacketInputs grid position grid.sites_pos).2.1
    let point := dest₁
    let banks := task.cube.cellWriter (initial₁).frame (controlsBase point cables₁ cells₁ J₁ live₁) 0
    let emission := fun (selected : SignedTaskArena.Layout) (ctrl : Fin 37 → Fin (2^w₁)) =>
      SeedPlan.frozenPacketWithBundles (reserve:=cap₁) S tape₁ order₁ position Unit actual grid.count owners₁
        small.2.2.2.2.2 (Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self cells₁) small.2.2.2.2.1))
        grid.block_pos (grid.block_le.trans_eq grid.link_eq) small.2.2.2.1 dir₁ num₁ grid.sites_pos
        small.2.2.2.1 selected.cube.cellBank selected.cube.cellStride selected.p.privateGap description hooks₁ w₁
        ctrl labels.1 labels.2 small.2.2.2.1 wideSites small.2.2.2.2.1 rowWidths padded point
        (header*logWidth r₁ (l+1)) banks (BundleSort.markedDepth cells₁ J₁)
        (cal.frozenWitness.frozenBundleShapes position ((fan S)^T₁) copies₁)
    let forwarded := task.withNetwork cells₁ cables₁
    let full : Fin 37 → Fin (2^w₁) := fun i => ⟨forwarded.controls i.val,
      cal.frozenEarlyControlFits grid qpos position chart reader chargeFit i⟩
    (located₁).raw = geometryTable hist₁ readOrder fit₁ (emission forwarded full) x₁ := by
  intro blank actual task labels small point banks emission forwarded full
  let encoded : Fin 37 → Fin (2^w₁) := fun i => Fin.ofNat _ (task.controls i.val)
  have sameTask : forwarded=task := cal.frozenEarlyTask grid qpos position chart reader chargeFit
  have sameCtrl : encoded=full := by
    funext i
    apply Fin.ext
    exact (cal.frozenTask_controlWord_value grid qpos position chart reader chargeFit i).trans
      (congrArg (fun t : SignedTaskArena.Layout => t.controls i.val) sameTask.symm)
  have late := SeedPlan.locatedFrozenEmission_program tape₁ order₁ position cal.frozenWitness cube b initial₁ l size₁ coeff
    grid.count grid.block_pos (grid.block_le.trans_eq grid.link_eq) grid.sites_pos inputs₁ actual rfl
  have native : (emission₁ actual).emitter=emission task encoded := rfl
  exact congrArg (fun gate => geometryTable hist₁ readOrder fit₁ gate x₁)
    (late.symm.trans (native.trans (congrArg₂ emission sameTask.symm sameCtrl)))

end Diagonal

end BorderVNP
end Computability
end OAI
