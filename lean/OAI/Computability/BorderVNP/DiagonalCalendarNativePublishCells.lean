import OAI.Computability.BorderVNP.DiagonalCalendarPublishSpace
import OAI.Computability.BorderVNP.PackedTerminalSignedHosts
import OAI.Computability.BorderVNP.PackedFrozenTapedInstallation

/-! # The placement bounds on the publisher's actual attached terminal hosts -/

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
local notation3 (prettyPrint := false) "dir₁" => freeDirectory (R₁) (r₁)
  ((tape₁).program.length+(cutWidth (l+1)+extra₁)) (ℓ₁) tiles (GridHosts.inputBlockWidth (r₁) (l+1) axes (d₁)) J₁ description


open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round Cover
open EnrichedOuter Diagonal.CellEntries

attribute [local instance] portFintype
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
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
local notation3 (prettyPrint := false) "wired₁" => wiringWith (prog₁) (program₁) physical₁ (pins₁) (ℓ₁) (l+1) ec₁ (geo₁).fits
local notation3 (prettyPrint := false) "names₁" => (cal.frozenWitness).routedFine position
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (names₁).Site).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (names₁).Edge).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "seed₁[" v "]" => (plan₁).frozenLeaf (tape₁) (order₁) position
  cal.frozenWitness tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "owners₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "free₁" => (physical₁).enrichedFree (prog₁) (program₁) (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "task₁" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "netAt[" v "," h "]" =>
  EnrichedTape.network (pins:=pins₁) (prog₁) (geo₁).fits position free₁ grid.count
    (plan₁).compiled.machine (seed₁[v]) rfl h
local notation3 (prettyPrint := false) "stageAt[" v "," h "]" => ((packHistory (seed₁[v]) (plan₁).compiled.machine.epoch T₁).term h).val
local notation3 (prettyPrint := false) "cellsAt[" v "," h "]" => fun site : (netAt[v,h]).Site =>
  owners₁ (reduceMove (EnrichedOuter.depth S (d₁+1) T₁) ((stageAt[v,h]).route.origin site))
local notation3 (prettyPrint := false) "hostsAt[" v "," h "]" =>
  originalDescriptionRows (plan₁).compiled.machine (seed₁[v]) h dir₁ rfl (order₁)


open Packing.RoutingOutputs

local notation3 (prettyPrint := false) "nativeDir" => freeDirectory R₁ r₁
  ((wired₁).program.length+(cutWidth (l+1)+extra₁)) ℓ₁ tiles (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description

attribute [local irreducible] Nat.clog Fintype.card Finset.univ
open ExternalSew.FieldExport Shortening.Adaptive

local notation3 (prettyPrint := false) "actual" => task₁
local notation3 (prettyPrint := false) "nativeParams" => (⟨R₁,r₁,(wired₁).program.length+(cutWidth (l+1)+extra₁),
  ℓ₁,GridHosts.inputBlockWidth r₁ (l+1) axes d₁,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "nativeHosts[" v "," h "]" =>
  GridHosts.attachedHosts wired₁ Fintype.card_pos grid.count (flattenPack T₁ (stageAt[v,h]).pack).layout
local notation3 (prettyPrint := false) "nativeNet[" v "," h "]" => FieldExport.finalLayout nativeParams (nativeHosts[v,h])
local notation3 (prettyPrint := false) "nativeCell[" v "," h "]" => fun site : (nativeNet[v,h]).Site =>
  owners₁ (reduceMove (EnrichedOuter.depth S (d₁+1) T₁) ((stageAt[v,h]).route.origin site))
local notation3 (prettyPrint := false) "original[" v "," h "]" =>
  originalDescriptionRows (plan₁).compiled.machine (seed₁[v]) h nativeDir rfl (order₁)
local notation3 (prettyPrint := false) "rebuilt" => (actual).withNetwork
  (Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1)))
  ((boundaryShape S (d₁+1) T₁).edges+(nativeParams).slots)



local notation3 (prettyPrint := false) "installedAt[" v "]" =>
  ((plan₁).frozen_leaf_installed tape₁ order₁ position cal.frozenWitness tag₁ sites₁ edges₁ ports₁
      v x₁).trans (SewnTape.native_grid_installed (R:=R₁) (r:=r₁) (copies:=copies₁) (pins:=pins₁)
      order₁ position prog₁ program₁ physical₁ (geo₁).fits)

set_option maxHeartbeats 3000000 in
/-- Attaching the original native grid and retaining its hosts through the
enriched history give the same block owners on the flattened terminal pack. -/
theorem SignedCalendarAt.frozenSites_publication_hosts
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (history : (packHistory (seed₁[values]) (plan₁).compiled.machine.epoch T₁).Index) :
    nativeHosts[values,history] = enrichedBlockHosts wired₁ axes d₁ order₁ position grid.count
      (plan₁).compiled.machine (seed₁[values]) (installedAt[values]) history :=
  enrichedBlockHosts_attached wired₁ axes d₁ order₁ position grid.count
    (plan₁).compiled.machine (seed₁[values]) (installedAt[values]) history

set_option maxHeartbeats 3000000 in
/-- Terminal publication attaches the same actual block hosts as the enriched
verifier retains on this history. Hence the two crossing networks agree. -/
theorem SignedCalendarAt.frozenSites_publication_network
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (history : (packHistory (seed₁[values]) (plan₁).compiled.machine.epoch T₁).Index) :
    nativeNet[values,history] = netAt[values,history] := by
  exact congrArg (FieldExport.finalLayout nativeParams)
    (cal.frozenSites_publication_hosts grid qpos position chart reader chargeFit values history)

set_option maxHeartbeats 3000000 in
/-- The local and global memory bounds in the exact order expected by the
directory-publication interpreter, using its attached-host layout. -/
theorem SignedCalendarAt.frozenSites_native_publish_cells
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (history : (packHistory (seed₁[values]) (plan₁).compiled.machine.epoch T₁).Index) :
    (∀ c, Packing.CellAddresses.suppliedSize (nativeNet[values,history]) (nativeCell[values,history]) c+
      (actual).p.privateGap+(∑ j : Fin J₁,
        if (nativeCell[values,history]) ((original[values,history]) j)=c then description else 0)
        ≤ (rebuilt).cube.cellStride) ∧
    (∀ c, Packing.CellAddresses.suppliedSize (nativeNet[values,history]) (nativeCell[values,history]) c+
      (actual).p.privateGap+J₁*description ≤ (actual).cube.cellStride) := by
  have hosts := cal.frozenSites_publication_hosts grid qpos position chart reader chargeFit values history
  let attached := nativeHosts[values,history]
  let room (host : type_of% attached) : Prop :=
    let N := FieldExport.finalLayout nativeParams host
    let cell := fun site : N.Site => owners₁ (reduceMove (EnrichedOuter.depth S (d₁+1) T₁)
      ((stageAt[values,history]).route.origin site))
    (∀ c, Packing.CellAddresses.suppliedSize N cell c+(actual).p.privateGap+
      (∑ j : Fin J₁, if cell ((original[values,history]) j)=c then description else 0)
        ≤ (rebuilt).cube.cellStride) ∧
    (∀ c, Packing.CellAddresses.suppliedSize N cell c+(actual).p.privateGap+J₁*description
        ≤ (actual).cube.cellStride)
  have previous := cal.frozenSites_publish_cells grid qpos position chart reader chargeFit values history
  exact (congrArg room hosts).mpr ⟨fun c => (previous c).1,fun c => (previous c).2⟩

end Diagonal

end BorderVNP
end Computability
end OAI
