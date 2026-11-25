import OAI.Computability.BorderVNP.DiagonalCalendarFrozenRouting

/-! # Exterior crossing widths on each original deployed history -/

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
    {schedule : PackedHistoryCircuit.Normalized.SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales schedule (cube.pred+1) extra}
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

variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

local notation "X₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)

open CellEntries Shortening Shortening.Adaptive Epoch.Round
attribute [local instance] portFintype

local notation3 (prettyPrint := false) "P₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "free₁" => (cal.frozenSites grid qpos position chart reader chargeFit).enrichedFree
  (prog₁) (P₁) (l+1) (ec₁) (ℓ₁)
local notation3 (prettyPrint := false) "seed" => cal.seed.choose
local notation3 (prettyPrint := false) "nameSite" => (Fintype.equivFin (cal.frozenWitness.routedFine position).Site).toEmbedding
local notation3 (prettyPrint := false) "nameEdge" => (Fintype.equivFin (cal.frozenWitness.routedFine position).Edge).toEmbedding
local notation3 (prettyPrint := false) "namePort" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag" => ParseTable.signedLiteralCode (s:=size₁) ord

/-- On each original packed term, count actual crossings after installing the frozen
site's literals. The very same numbered cell assignment fits the label-index scanner
in the task selected before the term. -/
theorem SignedCalendarAt.frozenSites_history_width
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (table : (seedBundle (tape₁) axes (d₁) (order₁) position copies₁).Tables F) :
    let dir := cal.frozenDirectory
    let ar := (cal.frozenTask grid qpos position chart reader chargeFit).cube
    let x := fun _ : Unit => false
    let bottom := (seed).frozenLeaf (tape₁) (order₁) position cal.frozenWitness tag nameSite nameEdge namePort table x
    let M := (seed).compiled.machine
    ∀ h : (packHistory bottom M.epoch T₁).Index,
    let N := EnrichedTape.network (e:=paid) (S:=schedule) (pins:=pins₁) (prog₁) (geo₁).fits position free₁ grid.count M bottom rfl h
    let st := ((packHistory bottom M.epoch T₁).term h).val
    let number := Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth (e:=paid) schedule ((d₁)+1) T₁+1))
    let cell := fun v : N.Site => number (reduceMove (EnrichedOuter.depth (e:=paid) schedule ((d₁)+1) T₁) (st.route.origin v))
    intercellWidth N cell ≤ 2*(R₁+1)*(X₁) ∧
      _root_.OAI.Computability.BorderVNP.Cube.LabelIndex.wordEnvelope ar.alphabet
        (intercellWidth N cell+dir.teams*((dir.fields+1)*(dir.processors*dir.literal))) < 2^(w₁) := by
  classical
  intro dir ar x bottom M h N st number cell
  have widths : (seed).SewnWidths grid.count (ℓ₁) (X₁) (1/2) :=
    (congrArg (fun link => (seed).SewnWidths grid.count link (X₁) (1/2)) grid.link_eq).mp
      (routing.sewn header Q (seed)).choose_spec
  have sparse := (seed).frozen_signed_intercell_width (prog₁) (geo₁).fits cal.frozenWitness position tag
    nameSite nameEdge namePort table x (free₁) grid.count widths h number
  have guard := (cal.locatedGateTable_routing grid qpos position chart reader chargeFit routing).1
  exact ⟨sparse.trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide : 0<2))),
    (seed).frozen_signed_label_envelope (prog₁) (geo₁).fits cal.frozenWitness position tag nameSite nameEdge
      namePort table x (free₁) grid.count widths h number guard rfl⟩

end Diagonal

end BorderVNP
end Computability
end OAI
