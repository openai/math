import OAI.Computability.BorderVNP.DiagonalCalendarPacketNumerals
import OAI.Computability.BorderVNP.PackedFrozenEnrichedPacketGeometry

/-! # Network representation and wire-size bounds for a returned signed history -/

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

/-- The word-by-word representation and the per-cell wire-size bounds for
the candidate writer on this selected history, using the actual enriched
free bits installed at each physical site. -/
noncomputable def SignedCalendarAt.frozenWriterTopology
    (values : (seedBundle tape₁ axes (d₁) order₁ position copies₁).Tables F) :=
  let plan := cal.seed.choose
  let wr := cal.seed.choose_spec.choose
  let fit := cal.seed.choose_spec.choose_spec
  let witness := cal.frozenWitness
  let named := witness.routedFine position
  let sites := (Fintype.equivFin named.Site).toEmbedding
  let edges := (Fintype.equivFin named.Edge).toEmbedding
  let ports := (Fintype.equivFin (Fin (r₁) × Fin (publicWidth tape₁))).toEmbedding
  let tag := ParseTable.signedLiteralCode (s:=size₁) ord
  let x := fun _ : Unit => false
  let before := plan.frozenLeaf tape₁ order₁ position witness tag sites edges ports values x
  let hw := (withStartup (signedBody (cube.cubeID paid))).program
  let data := cal.frozenSites grid qpos position chart reader chargeFit
  let actual := wiringWith prog₁ hw data (pins₁) (ℓ₁) (l+1) (ec₁) (geo₁).fits
  let inputs := cal.frozenPacketInputs grid position
  let shape := inputs grid.sites_pos
  let small := shape.2.1
  let owners := Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
  let widths := fun i => Fintype.card (Machine.Guess S (d₁+1) (fun _ _ => short₁) i)
  let slots := fun i => Fintype.equivFin (Machine.Guess S (d₁+1) (fun _ _ => short₁) i)
  let sourceBounds := grid.source_bounds
  let installed := (plan.frozen_leaf_installed tape₁ order₁ position witness tag sites edges ports values x).trans
    (SewnTape.native_grid_installed order₁ position prog₁ hw data (geo₁).fits)
  let key := Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d₁))
  let oldPorts := Flat.portRows T₁ (privatePorts S key T₁)
  let valid : (fieldSewParams actual axes d₁).Valid :=
    ⟨grid.block_pos,grid.block_le.trans_eq grid.link_eq,GridHosts.gridRoom actual Fintype.card_pos⟩
  let charged := 15*(S.publicProgramFactor^T₁*initialMass (D:=D) (l+1) r₁ d₁ copies₁ header)
  let fits : charged < 2^w₁ := sourceBounds.2.trans_le (Nat.pow_le_pow_right (by decide : 0<2) small.2.2.2.1)
  fun hist : (packHistory before plan.compiled.machine.epoch T₁).Index =>
    let stack := (plan.frozen_signed_packet_fields tape₁ order₁ position witness tag sites edges ports values x
      (fun t i z => (RowTrace.seedNumber S (d₁+1) t i z).val) num₁ oldPorts actual grid.count valid owners hm installed
      hist dir₁ grid.sites_pos).1
    PLift.up <| And.intro
      (plan.frozen_issued_enriched_rep tape₁ order₁ position witness tag sites edges ports values x wr hm
      (fun h i z => (RowTrace.seedNumber S (d₁+1) h i z).val) num₁ widths slots (plan.profile_order_fits widths slots)
      actual grid.count owners small.2.2.2.2.2 (Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self cells₁) small.2.2.2.2.1))
      grid.block_pos (grid.block_le.trans_eq grid.link_eq) sourceBounds.1 small.2.2.2.1 sourceBounds.2 fit.2.2.2.1
      hist installed)
      (fun c => (stack c).trans_lt fits)

end Diagonal

end BorderVNP
end Computability
end OAI
