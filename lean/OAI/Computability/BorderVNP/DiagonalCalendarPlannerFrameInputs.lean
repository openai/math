import OAI.Computability.BorderVNP.DiagonalCalendarPlannerTask
import OAI.Computability.BorderVNP.DiagonalCalendarWriterDestinations
import OAI.Computability.BorderVNP.DiagonalCalendarFrozenRealization
import OAI.Computability.BorderVNP.DiagonalCalendarHeaderCopies
import OAI.Computability.BorderVNP.DiagonalCalendarHeaderBoot
import OAI.Computability.BorderVNP.DiagonalCalendarWriterTopology
import OAI.Computability.BorderVNP.DiagonalCalendarPublicationRoom
import OAI.Computability.BorderVNP.DiagonalSignedSelectedCandidates

/-! # The calibrated common planner frame from its returned native sites -/

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
  ((tape₁).program.length+(TeamContraction.cutWidth (l+1)+extra₁)) (ℓ₁) tiles (GridHosts.inputBlockWidth (r₁) (l+1) axes (d₁)) J₁ description

open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round Cover
open EnrichedOuter

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
local notation3 (prettyPrint := false) "seed₁" v => (plan₁).frozenLeaf (tape₁) (order₁) position cal.frozenWitness tag₁
  sites₁ edges₁ ports₁ v x₁

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

local notation3 (prettyPrint := false) "ad₁" => adviceOffsetWith (prog₁) r₁ 32 64 w₁ (l+1)
local notation3 (prettyPrint := false) "headers₁" => JointHeader.PositiveFields cap₁ (selectedTask).cube.n
  (selectedTask).cube.header.d (selectedTask).cube.header.cap (R₁+1) (selectedTask).dim (b.physical.tally (l+1))
open Packing.CellAddresses Packing.RoutingOutputs Packing.CellAddressPhysical
open ExternalSew.RowTrace ExternalSew.FieldExport GridHosts Packing.DeckGrid
open CellEntries JointHeader Routing

local notation3 (prettyPrint := false) "address₁" => fun u : Fin (R₁+1) => (initial₁).unitAddresses ad₁ (packet₁ u)
local notation3 (prettyPrint := false) "owners₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "free₁" => (physical₁).enrichedFree prog₁ program₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "netAt[" v "," h "]" =>
  EnrichedTape.network (pins:=pins₁) prog₁ (geo₁).fits position free₁ grid.count
    (plan₁).compiled.machine (seed₁ v) rfl h
local notation3 (prettyPrint := false) "stageAt[" v "," h "]" => ((packHistory (seed₁ v) (plan₁).compiled.machine.epoch T₁).term h).val
local notation3 (prettyPrint := false) "cellsAt[" v "," h "]" => fun site : (netAt[v,h]).Site =>
  owners₁ (reduceMove (EnrichedOuter.depth S (d₁+1) T₁) ((stageAt[v,h]).route.origin site))
local notation3 (prettyPrint := false) "params₁" => (⟨R₁,r₁,(wired₁).program.length+(TeamContraction.cutWidth (l+1)+extra₁),ℓ₁,
  GridHosts.inputBlockWidth r₁ (l+1) axes d₁,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "valid₁" => (⟨grid.block_pos,grid.block_le.trans_eq grid.link_eq,
  gridRoom wired₁ Fintype.card_pos⟩ : (params₁).Valid)
local notation3 (prettyPrint := false) "edgesAt[" v "," h "]" => mergedEdges params₁ valid₁ ((stageAt[v,h]).rows.edge)
local notation3 (prettyPrint := false) "portsAt" => (finProdFinEquiv : FreeBlock R₁ tiles ≃ Fin ((R₁+1)*tiles)).toEmbedding
local notation3 (prettyPrint := false) "hostsAt[" v "," h "]" => originalDescriptionRows (plan₁).compiled.machine (seed₁ v) h dir₁ rfl order₁
local notation3 (prettyPrint := false) "livePorts" => (Equiv.refl (FreeBlock R₁ tiles)).toEmbedding

open Packing.RoutingOutputs Packing.CellAddresses TeamContraction.JointHeader CompactMachine
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Tally Cube.LabelIndex

open PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan Cube.MeanChoice Cube.Tally
open Directory.PrivateBank CellAddressPhysical TeamContraction.JointHeader RoutingISA.LocalRow

set_option maxHeartbeats 32000000 in
/-- Collect the native writers for a fixed pin assignment and header. The
result retains the supplying site at every exterior and team as well as its
writer projection in the single calibrated route. -/
theorem SignedCalendarAt.frozenPlannerFrameOfSites
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (headerBound : ((layout₁).header:ℝ)≤r₁*((l+1:ℕ):ℝ)^(24/25:ℝ))
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (h : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index)
    (p : headers₁)
    (fixed : Routing.Block (R₁+1)) (pin rawPin : Fin pins₁ → Bool) :
  let planner := cal.frozenPlannerTask grid qpos position chart reader chargeFit
  let ar := planner.cube
  let area := initial₁
  let G := wired₁
  let layout := layout₁
  let dir := dir₁
  let inputBase := fun u => ((address₁) u).ibase
  let headerBase := fun u => ((address₁) u).hbase
  let starBase := fun u => ((address₁) u).starbase
  let dst := fun u => ((address₁) u).dst
  let digits := (G.jointGuess inputBase headerBase starBase).symm rawPin
  let observe := fun u => Pins.extendGuess (digits u)
  let returned := cal.frozenSites_header_boot grid qpos position chart reader chargeFit fixed pin p
  let roster := cal.frozenSites_boots grid qpos position chart reader chargeFit fixed
  let nodes := fun z : HeaderExterior layout p.bits => roster.2.choose pin ⟨z.val,(returned z).choose⟩
  let pubAt := fun (_ : HeaderExterior layout p.bits) (u : Fin (R₁+1)) => (physical₁).publicWords u
  let libAt := fun (z : HeaderExterior layout p.bits) (u : Fin (R₁+1)) =>
    install (w:=w₁) SparseExterior.driver (l+1) (nodes z u).start.routines
  let entry := fun (z : HeaderExterior layout p.bits) (u : Fin (R₁+1)) => (nodes z u).pins (digits u)
  let regs := fun z u => (entry z u).val.2.1
  let mems := fun z u => (entry z u).val.2.2
  let N := netAt[values,h]
  let cell := cellsAt[values,h]
  let edge := edgesAt[values,h]
  let port := portsAt
  let original := hostsAt[values,h]
  let gap := planner.p.privateGap
  let bounds : dir.DestinationBounds := cal.frozenWriterDestinations grid qpos position chart reader chargeFit routing
  let positive : 0 < ar.header.d := (cal.frozenSpliceBounds grid).2.2
  let rows := NativeDemands.rows N cell edge port dir original livePorts gap
  let recv := NativeDemands.receiver N cell edge port dir original livePorts gap bounds
  let amount := fun i : Fin rows.length => (rows[i.val]'i.isLt).width
  let pp := NativeDemands.privatePair N cell edge port dir original livePorts gap
  let lp := NativeDemands.livePair N cell edge port dir original livePorts gap
  let axis := Fin.ofNat (ar.n+1) (readCode (ar.n+1) p.cube.1)
  let decl := Prod.mk axis (fun (e : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) => readCode (ar.header.cap+1) (p.cube.2 e j))
  let label := meanPackedLabel N cell recv amount (List.finRange ar.cells) ar.n ar.header.d positive
  let mass := declarationWeight ar.header.blocks ar.b ar.K ar.h decl label recv amount
  let group := fun j : Fin ar.header.d => TeamNative.owner R₁ mass j.val
  let owner := fun c : ℕ => if ok:c<ar.cells then group (label ⟨c,ok⟩ axis) else 0
  let supply := Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin ar.cells → Fin ar.cells)
  let prefixWidth := Sum.elim (supplyWidth N cell) (fun _ : Fin ar.cells => gap)
  let keyID := numbered (reserveID (C:=ar.cells) (suppliedID N cell edge port))
  let host := Sum.elim supply (cell ∘ original)
  let sizes := Sum.elim prefixWidth (fun _ : Fin dir.entries => dir.description)
  let atSite := fun (x : HeaderExterior layout p.bits) (u : Fin (R₁+1)) =>
    SignedPrep.CandidateSite (X:=outside₁) ar dir pp lp p.cube owner decl group area.frame area.next
      (G.pinLayout u (inputBase u) (headerBase u) (starBase u))
      (G.processorFields u pin x.val (inputBase u) (headerBase u) (starBase u))
      (G.transferFrame u layout.header (dst u)) (observe u) (pubAt x u) (libAt x u) (regs x u) (mems x u)
      host keyID sizes N cell recv amount
  ∀ Q₀ : (z : HeaderExterior layout p.bits) → (u : Fin (R₁+1)) → atSite z u → Prop,
    (∀ z u, ∃ s, Q₀ z u s) → declarationInRange p.cube →
    ∃ site : ∀ (z : HeaderExterior layout p.bits) (u : Fin (R₁+1)), atSite z u,
      (∀ x u, Q₀ x u (site x u)) ∧ ∃ (wire : WireLayout (R₁+1) r₁ ℓ₁) (same : wire.header=layout.header),
        let back := (HeaderExterior.changeLayout layout wire same p.bits).symm
        let W := fun (x : HeaderExterior wire p.bits) u => (site (back x) u).receipt
        ∃ F : PreparationFrame G wire ar decl p.bits pin (pubAt ∘ back) (libAt ∘ back) (regs ∘ back) (mems ∘ back),
          PreparationFrame.WriterProjection G wire ar dir pp lp owner decl group area.frame p.bits pin observe
            dst inputBase headerBase starBase (pubAt ∘ back) (libAt ∘ back) (regs ∘ back) (mems ∘ back)
            (fun x u => (site (back x) u).epoch) (fun x u => (site (back x) u).published)
            (fun x u => (W x u).endReg) (fun x u => (W x u).out) (fun x u => (W x u).events)
            (fun x u => (W x u).history) F := by
  intro planner ar area G layout dir inputBase headerBase starBase dst digits observe returned roster nodes pubAt libAt entry
    regs mems N cell edge port original gap bounds positive rows recv amount pp lp axis
    decl label mass group owner supply prefixWidth keyID host sizes atSite Q₀ per valid
  let normalized := cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit
  let installed := cal.locatedGateTable_routing grid qpos position chart reader chargeFit routing
  let early := cal.frozenEarlyTask grid qpos position chart reader chargeFit
  let fitFor := fun task : SignedTaskArena.Layout => RouteTableInputs task.cube dir scales.α ξ₁ (l+1) w₁ area.frame ℓ₁
  let fit : fitFor planner := (congrArg fitFor normalized).mp ((congrArg fitFor early).mpr installed.2.1)
  let room := cal.frozenPublicationRoom grid qpos position chart reader chargeFit routing
  let subRoom (u : Fin (R₁+1)) : area.frame + 13 < inputBase u ∧ inputBase u + (G.pinLayout u (inputBase u) (headerBase u) (starBase u)).count≤ar.header.header := by
    change area.frame + 13 < area.ibase ∧ area.ibase+area.count≤planner.cube.header.header
    let floor := fun task : SignedTaskArena.Layout => area.ibase+area.count≤task.cube.header.header
    have before : area.ibase+area.count≤area.next := by unfold StartupArena.next StartupArena.hbase; omega
    have low : area.frame + 13 < area.ibase := by unfold StartupArena.ibase StartupArena.broadcastBase StartupArena.dense; omega
    have high : area.next+7*dir.candidates≤(selectedTask).cube.header.header := room.2.2.2.2.1
    exact ⟨low,(congrArg floor normalized).mp (before.trans ((Nat.le_add_right _ _).trans high))⟩
  let copied := cal.frozenHeaderCopies grid qpos position chart reader chargeFit fixed pin p
  let width := p.bits_length.trans (cal.frozenLayout_fields chart reader chargeFit).1.symm
  let literalRoom : dir.literal≤TeamScales.literal scales.α (l+1) := (grid.template_directory (pins₁) (geo₁)).1.le
  exact signed_selected_candidates
    (G:=G) (skeleton:=layout) (header:=p.bits) (len:=width) (ar:=ar) (D:=dir) (pin:=pin) (guess:=observe)
    (dst:=dst) (ib:=inputBase) (hb:=headerBase) (sb:=starBase) (frame:=area.frame) (receivingBase:=area.next)
    (word:=p.cube) (fit:=fit) (perPin:=per) (subRoom:=subRoom) (copied:=copied)
    (processors:=rfl) (literal:=rfl) (teams:=rfl) (literalRoom:=literalRoom) (headRoom:=headerBound) (valid:=valid)

end Diagonal

end BorderVNP
end Computability
end OAI
