import OAI.Computability.BorderVNP.DiagonalCalendarFinishShape

/-! # The original concrete sort dimensions of the selected calendar table -/

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
set_option maxHeartbeats 4800000

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

open CellPacketGeometry TerminalCells RoutingOutputs RoutingISA.SignedTaskArena
open GeometryAdviceRate

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

/-- The public sort depth, descriptor sort depth and number of chunks
used by the terminal packet from this very seed tape. -/
noncomputable def SignedCalendarAt.frozenPacketSortShape : ℕ × ℕ × ℕ := by
  have lit := (grid.template_directory (pins₁) (geo₁)).1
  have inputs := grid.packet_inputs φ q adv c charge factor coeff cal.output (tape₁) lit grid.link_eq.symm
    (order₁) position description grid.sites_pos
  dsimp only at inputs
  rw [←Nat.mul_assoc 6 (R₁+1) tiles,←Nat.mul_assoc 4 (R₁+1) tiles] at inputs
  let tpl := tpl₁(inputs.2.2.2.2.choose,inputs.2.2.2.2.choose_spec.choose)
  exact (tpl.publicDepth,tpl.chunkDepth,tpl.chunkLabels.length)

/-- All admissible proofs of the schema tag bounds give exactly the
same two sort depths and original chunk count on the deployed template. -/
theorem SignedCalendarAt.frozenPacketSortShape_eq
    (hs : ∀ j, ((sources₁).tags j).length≤tagCap₁) (hf : ∀ j, ((last₁).tags j).length≤tagCap₁) :
    cal.frozenPacketSortShape grid position =
      ((tpl₁(hs,hf)).publicDepth,(tpl₁(hs,hf)).chunkDepth,(tpl₁(hs,hf)).chunkLabels.length) := rfl

/-- The original lowering uses the same concrete sort dimensions in its
output arity and its installed directory, down to the chunk and marker addresses. -/
theorem SignedCalendarAt.locatedGateTable_finishSortShape (initial : StartupArena) :
    let dims := cal.frozenPacketSortShape grid position
    let t := cal.locatedGateTable grid qpos position initial
    let dest := Allocation.dest (initial.next+7*(dir₁).candidates) cap₁ ceiling₁ t.outputs w₁
    let ctl := controlsBase dest cables₁ cells₁ J₁ live₁
    let start := Retained.packetBase dest cables₁ cells₁ J₁ live₁ 37
    t.outputs=signedGridOutputCount cables₁ cells₁ J₁ live₁ 37 (Total dims.1 dims.2.1)+(2^marked₁+2^marked₁) ∧
      t.directories=GeometryDirectories.published start dims.1 dims.2.1 (cells₁+1) dims.2.2 ctl
        (Total dims.1 dims.2.1) marked₁ ∧ Total dims.1 dims.2.1 ≤ t.outputs := by
  intro dims t dest ctl start
  refine ⟨rfl,rfl,?_⟩
  exact ((((Nat.le_add_left _ 37).trans (Nat.le_add_left ..)).trans (Nat.le_add_left ..)).trans
    (Nat.le_add_left ..)).trans (Nat.le_add_right ..)

end Diagonal

end BorderVNP
end Computability
end OAI
