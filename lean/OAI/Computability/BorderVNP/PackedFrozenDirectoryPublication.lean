import OAI.Computability.BorderVNP.PackedFrozenSignedPacketGeometry
import OAI.Computability.BorderVNP.PackedFrozenRoutingNames
import OAI.Computability.BorderVNP.PackedFrozenSignedEmitter
import OAI.Computability.BorderVNP.PackedTerminalStagedSewnImage
import OAI.Computability.BorderVNP.PackedSewnFragmentSelectedFields
import OAI.Computability.BorderVNP.DiagonalBootedProfilePublication

/-! # Native cell placement on the attained frozen grid and the actual free directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

/-- Install the cell and cable rectangles of the selected frozen geometry in
the arena before computing any of its absolute addresses. -/
def Layout.withNetwork (task : Layout) (cells cables : ℕ) : Layout :=
  {task with cube := {task.cube with cells := cells, cables := cables}}

/-- A hardware layout already assigned its correct rectangles is recovered verbatim. -/
theorem Layout.withNetwork_self (task : Layout) : task.withNetwork task.cube.cells task.cube.cables = task := rfl

end RoutingISA.SignedTaskArena

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.PreparedBins
open Packing.PhysicalEpochs
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales VPVNP.VerifierNetwork
open TerminalCells FieldExport GridHosts Diagonal.ExternalSew.RowTrace Packing.CellAddressCircuit Packing.SewnField
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {σ : Type} [Fintype σ] {g : ℕ} {len : Fin n} {state : Fin g}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K) (x : σ → Bool)

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*logWidth r n
local notation "mass" => initialMass (D:=D) n r d copies headerFactor
local notation "V" => CoverScale.sites (Cube D) (d+1)
local notation "extent" => copies*GridHosts.inputBlockWidth r n axes d
local notation "header" => WorkWords.grouped V extent
local notation "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "geom" => (plan.execute G order position σ).choose.eval x
local notation3 (prettyPrint := false) "old₀" => Boundary.seedBirthPrograms S order position W tag sites edges ports table geom
local notation3 "fmt" => Boundary.seedFormat G order position copies
local notation3 "source" => plan.frozenStart G order position σ

local notation3 (prettyPrint := false) "seed₀" => plan.frozenLeaf G order position W tag sites edges ports table x

variable (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < m)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ)

local notation3 "compiled" => plan.compiled
local notation3 (prettyPrint := false) "steps" => (compiled).tapeSteps fmt header key wr hm
local notation3 (prettyPrint := false) "names" => (compiled).privateSiteRows key seeds


variable {reserve : ℕ} (widths : ℕ → ℕ)
    (ord : ∀ j, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) j ≃ Fin (widths j))
    (fit : broadcastWidth (fan S) widths T ≤ reserve)

local notation3 (prettyPrint := false) "epochFormat" => ProgramSchemas.epoch S (d+1) w fmt T
local notation3 (prettyPrint := false) "aug" => compile steps T le_rfl (repeatLeaf (fan S) source T)
local notation3 (prettyPrint := false) "base" => (plan.execute G order position σ).choose


variable {R rTime rPins ell rInner : ℕ} {Wire : Type}
    (actual : Wiring R r rTime rPins ell rInner n Wire) (count : (fan S)^T*copies=R+1)
    {cells k packetWidth : ℕ} (cellNumber : (Cube D → Deck (EnrichedOuter.depth S (d+1) T+1)) ≃ Fin cells)
    (vf : (boundaryShape S (d+1) T).sites ≤ 2^(60*logWidth r n)) (cf : cells ≤ 2^k)
    (hg : 0 < inputBlockWidth r n (Fintype.card (Cube D)) d) (short : inputBlockWidth r n (Fintype.card (Cube D)) d ≤ ell)
    (pw : copies*inputBlockWidth r n (Fintype.card (Cube D)) d < 2^(60*logWidth r n))
    (extend : 60*logWidth r n ≤ packetWidth) (room : 15*(S.publicProgramFactor^T*initialMass (D:=D) n r d copies headerFactor) < 2^(60*logWidth r n))
    (hook : Compiled.HookRoom S T (60*logWidth r n) (initialMass (D:=D) n r d copies headerFactor))
    (q : (packHistory (plan.frozenLeaf G order position W tag sites edges ports table x) plan.compiled.machine.epoch T).Index)

local notation3 (prettyPrint := false) "s₁" => ((packHistory seed₀ (compiled).machine.epoch T).term q).val
local notation3 (prettyPrint := false) "N₀" => (flattenPack T (s₁).pack).layout
local notation3 (prettyPrint := false) "code₁" => ((compiled).machine.nativeCode seed₀ base x rfl widths ord fit q).val
local notation3 (prettyPrint := false) "input₁" => Retained.branch aug (broadcastOrder (fan S) widths ord T) fit x code₁
local notation3 (prettyPrint := false) "prior₁" => (compiled).machine.terminalPrivatePrograms names number seed₀ old₀ q
local notation "offs" => flatOffset (compiledOffset S (d+1)) T
local notation "g₁" => inputBlockWidth r n axes d
local notation3 (prettyPrint := false) "p₁" => (⟨R,r,actual.program.length+rTime,ell,g₁,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "hp₁" => (⟨hg,short,gridRoom actual Fintype.card_pos⟩ : (p₁).Valid)
local notation3 (prettyPrint := false) "h₁" => attachedHosts actual Fintype.card_pos count N₀
local notation3 (prettyPrint := false) "lane₁" => groupedLane actual tiles Fintype.card_pos ((fan S)^T) copies count
local notation3 (prettyPrint := false) "edge₁" => mergedEdges p₁ hp₁ (s₁).rows.edge
local notation3 (prettyPrint := false) "port₁" => (finProdFinEquiv : FreeBlock R tiles ≃ Fin ((R+1)*tiles)).toEmbedding
local notation3 (prettyPrint := false) "oldPort" => Flat.portRows T (privatePorts S key T)
local notation3 (prettyPrint := false) "finalN" => finalLayout p₁ h₁
local notation3 (prettyPrint := false) "cells₁" => fun v => cellNumber (reduceMove (EnrichedOuter.depth S (d+1) T) ((s₁).route.origin v))
local notation3 (prettyPrint := false) "F₀" => TerminalCells.fields (Move := allowedMoves (Cube D) S.budget) (q := axes)
  (d := EnrichedOuter.depth S (d+1) T) (E := (boundaryShape S (d+1) T).edges) vf cf (@groupRow ((fan S)^T) tiles offs)
  (fun _ => copies*g₁)
local notation3 (prettyPrint := false) "route₁" => Retained.Terminal.route (X := σ) (reserve := reserve) epochFormat
local notation3 (prettyPrint := false) "ext₁" => Retained.Terminal.width (X := σ) (reserve := reserve) epochFormat true
local notation3 (prettyPrint := false) "source₁" => withSewnFields (boundFrame (factorEnum D) cellNumber cf route₁ ext₁)
local notation3 (prettyPrint := false) "F₁" => FieldExport.fields F₀ p₁ (attachedName offs copies)
local notation3 (prettyPrint := false) "source₂" => stagedSource F₁ source₁
local notation3 (prettyPrint := false) "F₂" => Fields.widenWidths (stagedFields F₁) extend (Sum.inr false)
local notation3 (prettyPrint := false) "rawState" => sewnPrograms N₀ lane₁ (h₁).bundle (fun _ : FreeBlock R tiles => g₁)
    (freeLane hg (gridRoom actual Fintype.card_pos)) (h₁).groupOwner ((h₁).groupAligned hg (gridRoom actual Fintype.card_pos))
    (s₁).rows.edge oldPort edge₁ port₁ prior₁
open VPVNP.BurstRAM RoutingISA RoutingISA.Pins RoutingISA.CompactMachine RoutingISA.Evaluator
open ProcessorSlots Packing.CellAddresses Packing.RoutingOutputs Packing.CellAddressPhysical CellMacro.Generator Diagonal DiagonalResidueRAM

variable (template : SignedTaskArena.Layout) (desc : ℕ)
local notation "H₁" => boundaryShape S (d+1) T
local notation "J₁" => (fan S)^T*tiles
local notation3 (prettyPrint := false) "task₁" => template.withNetwork cells ((H₁).edges+(p₁).slots)
local notation3 (prettyPrint := false) "dir₁" => freeDirectory R r (actual.program.length+rTime) ell tiles g₁ J₁ desc
local notation3 (prettyPrint := false) "hosts₁" => originalDescriptionRows plan.compiled.machine seed₀ q dir₁ rfl order
local notation3 (prettyPrint := false) "live₁" => Function.Embedding.refl (Fin (R+1) × Fin tiles)
variable {pinCount hTime hInner hw : ℕ} {hwEdge : Type} {gen : Fragment CellMacro.Generator.IO}
    {native : Wiring R r hTime pinCount ell hInner n hwEdge} {pubs : Fin (R+1) → Arg → Word hw}
    {registers : Fin (R+1) → RoutingISA.Bank hw} {args : Fin (R+1) → UnitAddresses}
    {pin : Fin pinCount → Bool} {wire : Exterior R r ell → Bool} {u : Fin (R+1)}
    (node : BootedPinStart gen native pubs registers args pin wire u)
local notation3 (prettyPrint := false) "lib" => install gen n (TeamSiteEvents.macros («w»:=hw) (siteLibrary gen) (nativeClock n))
local notation3 (prettyPrint := false) "f₀" => native.transferFrame u (args u).header (args u).dst
local notation3 (prettyPrint := false) "L₀" => native.pinLayout u (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "fs₀" => native.processorFields u pin wire (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "initial" => processorMemory fs₀ hw

variable (a : StartupArena) (ua : Fin a.teams) (slot : ℕ) (packet : ReferencePacket hw pinCount) (headerBits : List Bool)
    (pf : Pins.ProcessorFields (a.operands ua slot packet).layout) (advice : AdviceLayout)
    (other : Arg → Word hw) (old : Fin 81 → Word hw)
    (origin gap bufferExtent raw team subtotalWidth fresh reserve₀ gates outputs width off stripe : ℕ)
    (guess : Fin (native.pinLayout u (args u).ibase (args u).hbase (args u).starbase).guessWidth → Bool)
local notation3 (prettyPrint := false) "B" => a.operands ua slot packet
local notation3 (prettyPrint := false) "loc" => privateLayout a.frame origin (task₁).cube.cables cells J₁ desc gap
local notation3 (prettyPrint := false) "tabs" => bases origin (task₁).cube.cables cells J₁
local notation3 (prettyPrint := false) "controlBase" => controlsBase origin (task₁).cube.cables cells J₁ ((R+1)*tiles)

set_option maxHeartbeats 3800000
set_option maxRecDepth 9000

include pw room hook in
/-- The original frozen row order and the complete emitted cell table
drive the placement of this booted pin's physical free directory. -/
theorem frozen_profile_publication {o clock : ℕ} {words : Fin o → ℕ}
    (sitePos : 0<(H₁).sites)
    (wireFit : ∀ c, guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c<2^packetWidth)
    (paths : ProfilePaths (withStartup pinGeometry) (L₀).guessWidth (pubs u) lib (registers u) initial True clock origin words
      (BootResidence (F:=pf) a ua slot packet f₀ advice (pubs u) lib headerBits initial (registers u)))
    (rows : ∀ ret : Returns (withStartup pinGeometry) (pubs u) lib (registers u) initial,
      Image F₂ (@TerminalCells.originalPins ((fan S)^T) tiles (H₁).sites sitePos offs) id ((source₂).eval input₁)
        origin (readings ret.val.2.2) ∧ ∀ i : Fin 37,readings ret.val.2.2 (controlBase+i.val)=(task₁).controls i.val)
    (pubEq : pubs u=(B).bank (core (withDemandBase ((task₁).routeBank a.frame other) a.next) origin (task₁).cube.cables cells))
    (installed : packet.extension=signedProfileExtension task₁ old dir₁ origin (task₁).cube.cables cells
      raw team subtotalWidth fresh reserve₀ gates outputs width off stripe)
    (fits₀ : (B).Fits hw) (room₀ : (task₁).cube.stop<2^hw) (one : 1<2^hw) (hk : k≤packetWidth)
    (wide : packetWidth≤hw) (cellPos : 0<cells) (cellFit : cells≤2^hw)
    (span : a.next+7*(dir₁).candidates≤origin) (rawRoom : a.next+7*(dir₁).candidates≤(task₁).cube.header.header)
    (ta : R+1=a.teams) (ra : r=a.processors) (la : actual.program.length+rTime=a.literal) (ea : ell=a.link)
    (rs : r≤tiles) (posR : 0<r) (positiveTail : 0<(actual.program.length+rTime)/2)
    (tail : J₁*desc≤(R+1)*r*((actual.program.length+rTime)/2))
    (localRoom : ∀ c,suppliedSize finalN cells₁ c+gap+(∑ j,if cells₁ (hosts₁ j)=c then desc else 0)≤(task₁).cube.cellStride)
    (globalRoom : ∀ c,suppliedSize finalN cells₁ c+gap+J₁*desc≤bufferExtent)
    (ctl : controlBase+8<2^hw)
    (wrRoom : Directory.ISA.wordBound (Directory.ISA.placementBound dir₁ (loc).raw (tabs).livePairs bufferExtent)<2^hw)
    (dst : (f₀).dst=a.broadcastBase) (length : headerBits.length=a.header) (gap₀ : (task₁).controls 8=gap) :
    ∃ ret : Returns (withStartup pinGeometry) (pubs u) lib (registers u) initial,
      ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn guess ∧ traceCost ret.val.1≤clock ∧
      BootResidence (F:=pf) a ua slot packet f₀ advice (pubs u) lib headerBits initial (registers u) guess ret.val.2.2 ∧
      (∀ i : Fin 37,readings ret.val.2.2 (controlBase+i.val)=(task₁).controls i.val) ∧
      PublishedPin task₁ dir₁ finalN cells₁ edge₁ port₁ hosts₁ live₁ a ua slot packet origin gap f₀ headerBits pf
        (pubs u) lib guess (node.pins guess).val.2.1 (node.pins guess).val.2.2 ret.val.2.1 ret.val.2.2
        (node.used+traceCost (node.pins guess).val.1) (traceCost ret.val.1) := by
  have net := (plan.frozen_signed_packet_geometry G order position W tag sites edges ports table x wr hm seeds number
    widths ord fit actual count cellNumber vf cf hg short pw extend room hook q).2.1
  have bounds : (dir₁).DestinationBounds := by
    refine ⟨positiveTail,hg,posR,le_rfl,?_⟩
    simpa only [freeDirectory,Directory.Layout.stride,Nat.add_sub_cancel,publicWidth] using
      gridRoom actual (show 0<tiles from Fintype.card_pos)
  have epochsFit : (fan S)^T≤R+1 := by
    rw [←count]
    apply Nat.le_mul_of_pos_right
    by_contra! zero
    rw [Nat.eq_zero_of_le_zero zero,Nat.mul_zero] at count
    omega
  obtain ⟨ret,spelling,cost,resident,_,published⟩ := booted_profile_publication task₁ dir₁ finalN cells₁ edge₁ port₁ hosts₁ live₁ a ua slot packet origin gap
    headerBits pf node (fun v => (rawState v).program.size) (s₁).rows.site F₂ ((source₂).eval input₁)
    net (fun _ => rfl) wireFit (fun _ => rfl) other old bufferExtent raw team subtotalWidth fresh reserve₀ gates outputs
    width off stripe advice guess paths (fun ret => ⟨plan.frozen_routing_image G order position W tag sites edges
      ports table x q dir₁ sitePos F₂ ((source₂).eval input₁) origin (readings ret.val.2.2) (rows ret).1,fun i : Fin 28 => (rows ret).2 (i.castLE (by decide))⟩)
    pubEq installed fits₀ room₀ one hk wide cellPos cellFit span rawRoom ta ra la ea (by decide : 0<2) le_rfl
    (Nat.succ_pos R) rs (Nat.mul_le_mul_right tiles epochsFit) tail bounds localRoom globalRoom ctl wrRoom dst length gap₀
  exact ⟨ret,spelling,cost,resident,(rows ret).2,published⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
