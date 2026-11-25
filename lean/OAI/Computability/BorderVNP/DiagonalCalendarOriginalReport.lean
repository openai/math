import OAI.Computability.BorderVNP.DiagonalCalendarDeployment
import OAI.Computability.BorderVNP.DiagonalFrozenOwnedBundleTransport
import OAI.Computability.BorderVNP.DiagonalDeployedOriginalMarked
import OAI.Computability.BorderVNP.DiagonalCalendarSourceRoom
import OAI.Computability.BorderVNP.PackedRetainedReportUse

/-! # The original marked report returned by the calendar's installed signed site -/

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
set_option maxHeartbeats 1300000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {schedule₀ : PackedHistoryCircuit.Normalized.SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales schedule₀ (cube.pred+1) extra}
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
local notation "J₁" => (EnrichedOuter.fan (e:=paid) schedule₀)^T₁*tiles
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
local notation3 (prettyPrint := false) "task₁" => cal.frozenTask grid qpos position chart reader chargeFit

open GeometryAdviceRate TeamContraction.JointHeader Cube.Physical Packing.BottomReports DiagonalTallyCellReports
open CellEntries Shortening Shortening.Adaptive BorderVNP.Epoch.Round Diagonal.ExternalSew.RowTrace
attribute [local instance] portFintype

local notation3 (prettyPrint := false) "blank" => TimedProcessor.scaleData (signedProgram (cube.cubeID paid)).program
  (siteLibrary SparseExterior.driver) (fun _ : Fin 8 => some false) (geo₁) (fun _ _ => 0) (fun _ _ => 0)
  (fun _ _ => false) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "P₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "nameSite" => (Fintype.equivFin (cal.frozenWitness.routedFine position).Site).toEmbedding
local notation3 (prettyPrint := false) "nameEdge" => (Fintype.equivFin (cal.frozenWitness.routedFine position).Edge).toEmbedding
local notation3 (prettyPrint := false) "namePort" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "data₁" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "t₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "external₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "wired₁" => wiringWith (prog₁) (P₁) (data₁) (pins₁) (ℓ₁) (l+1) (ec₁) (geo₁).fits

/-- Replacing the blank routing layout by the measured one for a native declaration keeps
the same installed source, including all original signed columns and the frozen gate table. -/
theorem SignedCalendarAt.frozenSites_on_returned_layout (later : Routing.WireLayout (R₁+1) (r₁) (ℓ₁))
    (same : (layout₁).header=later.header) :
    data₁ = reader.deployedFrozenSites (K:=F) (paid:=paid) (aux:=φ ∘ cube.table) (q:=q) (k:=l) (s:=size₁) (ord:=ord)
      (C:=common) (chart:=chart) (R:=R₁) (r:=r₁) (rw:=w₁) (pinWidth:=budget₁+6)
      (a:=a₁) (link:=ℓ₁) (ec:=ec₁) («axes»:=axes) (d:=d₁) (gridOrder:=order₁)
      (reserve:=cap₁) (o:=(located₁).outputs) (field:=w₁) (prog₁) (P₁) blank (geo₁).fits cal.frozenWitness position
      nameSite nameEdge namePort copies₁ ((EnrichedOuter.fan (e:=paid) schedule₀)^T₁) header later t₁ task₁ external₁ := by
  exact reader.deployedFrozenSites_header (K:=F) (paid:=paid) (aux:=φ ∘ cube.table) (q:=q) (k:=l) (s:=size₁) (ord:=ord)
      (C:=common) (chart:=chart) (R:=R₁) (r:=r₁) (rw:=w₁) (pinWidth:=budget₁+6)
      (a:=a₁) (link:=ℓ₁) (ec:=ec₁) («axes»:=axes) (d:=d₁) (gridOrder:=order₁)
      (reserve:=cap₁) (o:=(located₁).outputs) (field:=w₁) (prog₁) (P₁) blank (geo₁).fits cal.frozenWitness position
    nameSite nameEdge namePort copies₁ ((EnrichedOuter.fan (e:=paid) schedule₀)^T₁) header (layout₁) t₁ task₁ external₁ later same

local notation3 (prettyPrint := false) "tag" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "channels" => (groupedGridRows (tape₁) axes d₁ (order₁) position copies₁).edge
local notation3 (prettyPrint := false) "groups" => (Equiv.refl (Fin tiles)).toEmbedding
local notation3 (prettyPrint := false) "orderJ" => finProdFinEquiv.symm.trans
  ((Equiv.refl (Fin ((EnrichedOuter.fan (e:=paid) schedule₀)^T₁))).prodCongr (order₁))
local notation3 (prettyPrint := false) "origin₁" => Allocation.dest
  ((initial₁).next+7*(dir₁).candidates) cap₁ (t₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "control₁" => RoutingOutputs.controlsBase (origin₁)
  (task₁).cube.cables (task₁).cube.cells (dir₁).entries ((dir₁).teams*(dir₁).sites)
local notation3 (prettyPrint := false) "report₁" => DiagonalTallyAllocation.reportLayout (task₁).before (task₁).after
  (initial₁).frame (control₁) (task₁).p.parameters (task₁).p.siteWidth (task₁).p.bodyCap (task₁).cube.stop

/-- The source bundle has the signed report frame's true storage widths, regardless of
the local base, real receiving address or chosen site's fine assignment. -/
theorem SignedCalendarAt.frozenSites_report_shape :
    (report₁).fieldWidth=header*logWidth r₁ (l+1) ∧
    (report₁).bodyCap=BottomGridBank.bodyBudget (seedBoxCapacity (l+1) r₁ axes d₁ (Fintype.card (Direction axes))) :=
  ⟨rfl,rfl⟩

local notation3 (prettyPrint := false) "sourceBundle" => cal.frozenWitness.retainedBundle
  (copies:=copies₁) position (orderJ) tag nameSite nameEdge namePort channels groups

/-- Every actual received source ordinal contains the complete original marked report
of the deployed calendar witness. The emitting literal is fixed before the pin, while
the routing layout, receiving team, source position and live use assignment may vary. -/
theorem SignedCalendarAt.frozenSites_received_original
    (later : Routing.WireLayout (R₁+1) (r₁) (ℓ₁)) (same : (layout₁).header=later.header)
    (pin : Fin pins₁ → Bool) (wire : Exterior (R₁) (r₁) (ℓ₁) → Bool)
    (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R₁+1)) (runs : Fin (R₁+1) → TeamHistory (w₁))
    (ib hb sb : Fin (R₁+1) → ℕ)
    (delivery : ReturnedDelivery (wired₁) pin wire later (dir₁) pp lp owner (task₁).cube.cellBank
      (task₁).cube.cellStride runs (fun u => Wiring.pinLayout (wired₁) u (ib u) (hb u) (sb u)))
    (boxBase : Fin J₁ → ℕ) (bank : Fin J₁ → ℕ → Bool) (j : Fin J₁) :
    let slot := fun i : Fin J₁ => (task₁).cube.cellBank+(pp i.val).1*(task₁).cube.cellStride+(pp i.val).2
    (sourceBundle slot boxBase bank j).delivered report₁ description (readings (runs (owner (pp j.val).1)).history.val.2.2) := by
  intro slot
  obtain ⟨dirEq,_,_,room,_,tail,_,_,short,total,_⟩ := cal.frozenSourceRoom grid qpos position chart reader chargeFit
  have installed := cal.frozenSites_on_returned_layout grid qpos position chart reader chargeFit later same
  have widths := cal.frozenSites_report_shape grid qpos position chart reader chargeFit
  apply reader.deployedFrozenSites_routedMarked (K:=F) (paid:=paid) (aux:=φ ∘ cube.table) (q:=q) (k:=l) (s:=size₁) (ord:=ord)
      (C:=common) (chart:=chart) (R:=R₁) (r:=r₁) (rw:=w₁) (pinWidth:=budget₁+6)
      (a:=a₁) (link:=ℓ₁) (ec:=ec₁) («axes»:=axes) (d:=d₁) (gridOrder:=order₁)
      (reserve:=cap₁) (o:=(located₁).outputs) (field:=w₁) (prog₁) (P₁) blank (geo₁).fits cal.frozenWitness position
    nameSite nameEdge namePort copies₁ ((EnrichedOuter.fan (e:=paid) schedule₀)^T₁) header later t₁ task₁ external₁ pin wire pp lp owner runs
    ib hb sb _ _ _ _ _ j report₁ widths.1 widths.2 (boxBase j) copies₁ (bank j)
  · rw [←installed]
    rw [←same]
    exact Eq.mp (congrArg (fun actual : Directory.Layout =>
      ReturnedDelivery (wired₁) pin wire later actual pp lp owner (task₁).cube.cellBank
        (task₁).cube.cellStride runs (fun u => Wiring.pinLayout (wired₁) u (ib u) (hb u) (sb u))) dirEq.symm) delivery
  · rw [←same]
    exact room
  · exact tail
  · exact short
  · exact total

end Diagonal

end BorderVNP
end Computability
end OAI
