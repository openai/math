import OAI.Computability.BorderVNP.DiagonalCalendarDeployment
import OAI.Computability.BorderVNP.DiagonalCalendarControlFormats
import OAI.Computability.BorderVNP.DiagonalCalendarPostRate
import OAI.Computability.BorderVNP.DiagonalLocatedTableArgument

/-! # The argument window on the calendar's two actual sorted packet banks -/

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
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

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
local notation3 (prettyPrint := false) "task₁" => b.frozenSignedTask cube (l+1) l (size₁) header (initial₁)
  (dir₁) cap₁ ceiling₁ (located₁).outputs (w₁) (located₁).directories

open Packing.Inherited Packing.Inherited.FrozenTape CellPacketGeometry CellPacketGeometry.History
open CellPacketGeometry.LiveWords CellSparse.Packet TerminalCells
open Diagonal.CellEntries ParseBatchSort
local notation "short₁" => 60*logWidth (r₁) (l+1)
local notation "cells₁" => CoverScale.sites (Cube D) (EnrichedOuter.depth S (d₁+1) T₁)
local notation "live₁" => (R₁+1)*tiles
local notation "hooks₁" => Fintype.card (paid.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
local notation3 (prettyPrint := false) "num₁" => fun z : paid.Entry => cube.scalarNumber paid (.inl z)
local notation3 (prettyPrint := false) "fmt₁" => Boundary.seedFormat tape₁ order₁ position copies₁

local notation3 (prettyPrint := false) "shape₁" => boundaryShape S (d₁+1) T₁
local notation3 (prettyPrint := false) "cables₁" => (shape₁).edges+4*(R₁+1)*tiles
local notation3 (prettyPrint := false) "sources₁" => (ProgramSchemas.epoch S (d₁+1) short₁ fmt₁ T₁).schema.append
  (Sewn.schema (2*(shape₁).edges+6*(R₁+1)*tiles) short₁)
local notation3 (prettyPrint := false) "last₁" => FinalTies.tieSchema cables₁ live₁ w₁
local notation3 (prettyPrint := false) "boxes₁" => scheduledBoxes dir₁ rfl num₁ grid.sites_pos
local notation3 (prettyPrint := false) "priv₁" => FinalReports.Spare.priv (C:=cells₁) (g:=hooks₁) (digits:=w₁) (E:=Fin J₁)
local notation3 (prettyPrint := false) "reports₁" => FinalReports.Spare.reports (C:=cells₁) (g:=hooks₁) (digits:=w₁) (E:=Fin J₁)
local notation "tagCap₁" => ProgramSchemas.signedTagCapacity (e:=paid)
local notation "marked₁" => BottomReports.BundleSort.markedDepth cells₁ J₁
local notation3 (prettyPrint := false) "tpl₁" "(" hs "," hf ")" => template sources₁ last₁ boxes₁ hs hf priv₁ reports₁

open RoutingISA.Evaluator.ScheduleClock _root_.OAI.Computability.BorderVNP.Cube

include grid in
/-- Recover the selected packet's tag bound directly from the calendar grid. -/
private theorem argumentPacketTags :
    (∀ j, ((sources₁).tags j).length≤tagCap₁) ∧ (∀ j, ((last₁).tags j).length≤tagCap₁) := by
  have literal := (grid.template_directory (pins₁) (geo₁)).1
  have inputs := grid.packet_inputs φ q adv c charge factor coeff cal.output tape₁ literal grid.link_eq.symm
    order₁ position description
  have bound := inputs grid.sites_pos
  dsimp only at bound
  rw [←Nat.mul_assoc 6 (R₁+1) tiles,←Nat.mul_assoc 4 (R₁+1) tiles] at bound
  exact ⟨bound.2.2.2.2.choose,bound.2.2.2.2.choose_spec.choose⟩

private theorem slots_with_banks {a b e live words saved : ℕ} :
    signedGridOutputCount a b e live 37 words+saved =
      signedGridOutputCount a b e live (37+saved) words := by
  unfold signedGridOutputCount
  omega

/-- Once both numerical rates hold at the calendar length, every genuine
label directory of its deployed sparse emitter fits its argument window.
The two depths are fixed by the very template installed in the frozen
gate table, including its two original-bundle sort banks. -/
theorem SignedCalendarAt.frozenSites_argument_window
    (bound : LocatedTableArgumentAt cube b (l+1))
    (rate : CalendarPostRateAt cube b φ q adv c charge (l+1)) :
    let task := cal.frozenTask grid qpos position chart reader chargeFit
    let ar := task.cube
    let dir := dir₁
    let tags := argumentPacketTags cal grid position
    let tpl := tpl₁(tags.1,tags.2)
    let powers := ar.teams*(task.p.parameters*Nat.clog 2 (r₁*(2*l+1)+1))
    let ext := exterior (ξ₁) (r₁) (l+1)
    let fixed := (CubeConstants.install task.id).slots
    let coeff := cubeCoefficient ar.n ar.b ar.h ar.K ar.s (Tally.argumentWidth ar.n ar.b ar.h ar.K ar.s)
    ∀ pp lp (frame axis : ℕ) (after : ℕ → ℕ),
      let labels := LabelIndex.layout frame after
      let groups := LocalRow.weightLayout ar frame axis
      let owners := LocalRow.teamLayout ar (R₁)
      labels.cells=ar.cells → labels.cableCount=ar.cables →
      labels.deliveryCount=(dir.directory pp lp).length → labels.labels=ar.alphabet →
      fixed+argumentDirectory ar.cells dir.entries+
        32*descriptorTicks labels after (ar.alphabet-1) (ar.n+1) groups owners+
        (82*labels.cableCount+coeff*(ar.alphabet^2+ext+1))+
        cellWork (w₁) (2^tpl.publicDepth+2^tpl.chunkDepth) powers ext ≤
          (scales.chosenSignedWindows cube E (l+1) r₁).argumentsCalls := by
  intro task ar dir tags tpl powers ext fixed coeff pp lp frame axis after labels groups owners hc he hr hl
  have slots : powers ≤ r₁ := (rate l rfl chart reader chargeFit).1
  have endFit := (cal.frozenTask_room grid qpos position chart reader chargeFit).2.1
  have before : task.before.limit < 2^w₁ := (task.finish_word_room endFit).2.2.2
  have full : ar.stop ≤ task.before.limit := by
    change task.cube.stop ≤ task.before.limit
    apply le_trans _ (show task.before.start ≤ task.before.limit by rw [task.before.footprint]; omega)
    apply le_trans _ task.constants_le_before
    unfold CubeConstants.arenaEnd CubeConstants.idBase
    omega
  have stop : ar.stop < 2^w₁ := full.trans_lt before
  have level : (d₁)+1=CoverScale.initialDepth (Cube D) (r₁) (l+1) := Nat.sub_add_cancel (Nat.succ_pos _)
  have cables : ar.cables=cables₁ := by
    change (boundary S _ T₁).edges+4*((R₁+1)*CoverScale.sites (Cube D) _) =
      (boundaryShape S ((d₁)+1) T₁).edges+4*(R₁+1)*tiles
    calc
      _ = (boundary S ((d₁)+1) T₁).edges+4*((R₁+1)*CoverScale.sites (Cube D) ((d₁)+1)) :=
        congrArg (fun start => (boundary S start T₁).edges+4*((R₁+1)*CoverScale.sites (Cube D) start)) level.symm
      _ = _ := by
        rw [←seedPortCount (D:=D) d₁,Nat.mul_assoc]
        rfl
  have cells : ar.cells=cells₁ :=
    congrArg (fun start => CoverScale.sites (Cube D) (EnrichedOuter.depth S start T₁)) level.symm
  have emit : (located₁).outputs=signedGridOutputCount cables₁ cells₁ J₁ live₁ 37
      (Total tpl.publicDepth tpl.chunkDepth)+(2^marked₁+2^marked₁) := rfl
  let t := located₁
  have shape : t.outputs = signedGridOutputCount ar.cables ar.cells dir.entries live₁
      (37+(2^marked₁+2^marked₁)) (Total tpl.publicDepth tpl.chunkDepth) := by
    rw [cells,cables]
    exact emit.trans slots_with_banks
  have dirEq : dir=b.signedStartupDirectory (l+1) description := (grid.template_directory (pins₁) (geo₁)).2
  have measured := bound initial₁ description ceiling₁ l (size₁) header tiles J₁ t
  rw [←dirEq] at measured
  exact measured tpl.publicDepth tpl.chunkDepth live₁ (37+(2^marked₁+2^marked₁)) powers shape slots
    pp lp frame axis after stop hc he hr hl

end Diagonal

end BorderVNP
end Computability
end OAI
