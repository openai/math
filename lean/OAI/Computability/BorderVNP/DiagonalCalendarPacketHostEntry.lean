import OAI.Computability.BorderVNP.DiagonalCalendarPlannerNetwork
import OAI.Computability.BorderVNP.DiagonalCalendarWriterDestinations
import OAI.Computability.BorderVNP.DiagonalCandidateLiteralHostSource
import OAI.Computability.BorderVNP.DiagonalPhysicalReturnCanonicalEntry
import OAI.Computability.BorderVNP.PackedFrozenRoutingNames
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedPlacement

/-! # The native host slots of a calendar packet at its actual publication -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank LocalRow BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex
open scoped Classical

open CellMacro.Generator RoutingISA.CompactMachine PackedHistoryCircuit

private noncomputable def nativeEntryOnPacket
    {D p : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {task : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits}
    {cell : N.Site → Fin task.cube.cells} {edgeID : N.Edge ↪ Fin task.cube.cables} (portID : P ↪ Fin p)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    {ns cb lb wb origin : ℕ} {σ : Type} [Fintype σ] {aux : N.Site → ℕ} {ids : N.Site ↪ Fin ns}
    {geom : Fields ns task.cube.cables p task.cube.cells cb lb wb σ} {x : σ → Bool}
    {present : (ℕ → ℕ) → Prop}
    (network : ∀ ram,present ram → CellAddressPhysical.Represents N cell aux ids edgeID portID geom x ∧
      (∀ c,(geom.cells c).val=c.val) ∧ (∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^wb) ∧
      Image geom (ids ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin ram)
    (width : ∀ j,bits (live j)=dir.block) (bounds : dir.DestinationBounds)
    (siteLiteral : ℕ) (sameLiteral : siteLiteral=dir.literal) :=
  PLift.up <| fun {w d g R X baseFrame gap : ℕ} {a : StartupArena} {u : Fin a.teams} {slot : ℕ}
      {packet : ReferencePacket w d} {f : BroadcastFrame} {hdr : List Bool}
      {fields : Pins.ProcessorFields (a.operands u slot packet).layout} {pub : Arg → Word w}
      {mac : TeamOpcode.Macros w 8} {v : Fin g → Bool} {postPin : Bank w} {pinMem : Memory w}
      {pp lp : ℕ → ℕ × ℕ} {word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
      {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration task.cube.n task.cube.header.d}
      {group : Fin task.cube.header.d → Fin (R+1)} {guesses : ℕ → Bool} {I A : Type} [Fintype I]
      {host : I → Fin task.cube.cells} {keys : I ↪ ℕ} {sizes : I → ℕ} {recv : A → Fin task.cube.cells} {amount : A → ℕ}
      (site : SignedPrep.CandidateSite (X:=X) task.cube {dir with literal:=siteLiteral} pp lp word owner decl group baseFrame a.next
        (a.operands u slot packet).layout fields f guesses pub mac postPin pinMem host keys sizes N cell recv amount)
      (pin : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields pub mac
        v postPin pinMem site.geometryRegs site.geometry site.used site.profileCost)
      (stored : present (readings site.geometry)) =>
    let net := network _ stored
    PublishedPin.candidateCanonicalEntryAtLiteral (task:=task) (original:=original) (live:=live) (portID:=portID)
      site sameLiteral pin aux ids geom x net.1 net.2.1 width net.2.2.1 net.2.2.2 bounds

private noncomputable def nativeProgramOnPacket
    {D p : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {task : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits}
    {cell : N.Site → Fin task.cube.cells} {edgeID : N.Edge ↪ Fin task.cube.cables} (portID : P ↪ Fin p)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    {ns cb lb wb origin : ℕ} {σ : Type} [Fintype σ] {aux : N.Site → ℕ} {ids : N.Site ↪ Fin ns}
    {geom : Fields ns task.cube.cables p task.cube.cells cb lb wb σ} {x : σ → Bool}
    {present : (ℕ → ℕ) → Prop}
    (network : ∀ ram,present ram → CellAddressPhysical.Represents N cell aux ids edgeID portID geom x ∧
      (∀ c,(geom.cells c).val=c.val) ∧ (∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^wb) ∧
      Image geom (ids ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin ram)
    (width : ∀ j,bits (live j)=dir.block) (bounds : dir.DestinationBounds) :=
  PLift.up <| fun {w d g gap used cost : ℕ} {a : StartupArena} {u : Fin a.teams} {slot : ℕ}
      {packet : ReferencePacket w d} {f : BroadcastFrame} {hdr : List Bool}
      {fields : Pins.ProcessorFields (a.operands u slot packet).layout} {pub : Arg → Word w}
      {mac : TeamOpcode.Macros w 8} {v : Fin g → Bool} {postPin regs : Bank w} {pinMem seen middle : Memory w}
      (pin : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f hdr fields pub mac
        v postPin pinMem regs seen used cost)
      (epoch : Returns epochPlacement pub mac postPin pinMem)
      (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2)
      (epochMemory : epoch.val.2.2=middle) (stored : present (readings seen)) =>
    let net := network _ stored
    pin.programCanonicalEntry epoch published epochMemory aux ids geom x net.1 net.2.1 width net.2.2.1 net.2.2.2 bounds

open Lean Meta Elab Term in
/-- The site reader has already been instantiated with the calendar's certified row
geometry and capacity. Supply those same parameters to the program reader. -/
elab "programsFromHostPacket%" siteReader:term:max : term => do
  let reader ← elabTerm siteReader none
  let some native ← whnfUntil reader ``nativeEntryOnPacket |
    throwError "expected a calendar entry on its certified packet"
  let info ← getConstInfo ``nativeProgramOnPacket
  let count ← forallTelescope info.type fun inputs _ => pure inputs.size
  let args := native.getAppArgs
  unless args.size=count+2 do throwError "expected the site's literal extent and its equality after the packet data"
  return mkAppN (mkConst info.name native.getAppFn.constLevels!) (args.extract 0 count)

end PackedHistoryCircuit

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

local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
open CellMacro.Generator RoutingISA.CompactMachine

open Packing.CellAddresses Packing.RoutingOutputs Packing.CellAddressPhysical
open ExternalSew.RowTrace ExternalSew.FieldExport GridHosts Packing.DeckGrid
open CellEntries JointHeader Routing

local notation3 (prettyPrint := false) "owners₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "free₁" => (physical₁).enrichedFree prog₁ program₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "netAt[" v "," h "]" =>
  EnrichedTape.network (pins:=pins₁) prog₁ (geo₁).fits position free₁ grid.count
    (plan₁).compiled.machine (seed₁ v) rfl h
local notation3 (prettyPrint := false) "stageAt[" v "," h "]" => ((packHistory (seed₁ v) (plan₁).compiled.machine.epoch T₁).term h).val
local notation3 (prettyPrint := false) "cellsAt[" v "," h "]" => fun site : (netAt[v,h]).Site =>
  owners₁ (reduceMove (EnrichedOuter.depth S (d₁+1) T₁) ((stageAt[v,h]).route.origin site))
local notation3 (prettyPrint := false) "params₁" => (⟨R₁,r₁,(wired₁).program.length+(cutWidth (l+1)+extra₁),ℓ₁,
  GridHosts.inputBlockWidth r₁ (l+1) axes d₁,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "valid₁" => (⟨grid.block_pos,grid.block_le.trans_eq grid.link_eq,
  gridRoom wired₁ Fintype.card_pos⟩ : (params₁).Valid)
local notation3 (prettyPrint := false) "edgesAt[" v "," h "]" => mergedEdges params₁ valid₁ ((stageAt[v,h]).rows.edge)
local notation3 (prettyPrint := false) "portsAt" => (finProdFinEquiv : FreeBlock R₁ tiles ≃ Fin ((R₁+1)*tiles)).toEmbedding
local notation3 (prettyPrint := false) "hostsAt[" v "," h "]" => originalDescriptionRows (plan₁).compiled.machine (seed₁ v) h dir₁ rfl order₁
local notation3 (prettyPrint := false) "livePorts" => (Equiv.refl (FreeBlock R₁ tiles)).toEmbedding

open Packing.RoutingOutputs Packing.CellAddresses TeamContraction.JointHeader CompactMachine
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Tally Cube.LabelIndex
set_option cleanup.letToHave false in
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 18000 in
private noncomputable def packetEntryForLiteral
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (hist : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index)
    (siteLiteral : ℕ) (sameLiteral : siteLiteral=(dir₁).literal) :=
  let layout := congrArg SignedTaskArena.Layout.cube (cal.frozenPlannerTask_eq grid qpos position chart reader chargeFit)
  let cell := cast (congrArg (fun a : CubeArena.Layout => (netAt[values,hist]).Site → Fin a.cells) layout) (cellsAt[values,hist])
  let edge := cast (congrArg (fun a : CubeArena.Layout => (netAt[values,hist]).Edge ↪ Fin a.cables) layout) (edgesAt[values,hist])
  let network := (cal.plannerNetworkOnPacket grid qpos position chart reader chargeFit values).down hist
  let address := (cal.frozenIssuedPlacement grid qpos position chart reader chargeFit).2.2.1
  let bound := cal.frozenWriterDestinations grid qpos position chart reader chargeFit routing
  nativeEntryOnPacket (task:=cal.frozenPlannerTask grid qpos position chart reader chargeFit)
    (N:=netAt[values,hist]) (dir:=dir₁) (cell:=cell) (edgeID:=edge) (origin:=origin₁)
    (present:=cal.frozenPacketImage grid qpos position chart reader chargeFit values hist)
    portsAt (hostsAt[values,hist]) livePorts (fun m stored => by
      let packet := network m stored
      refine ⟨?_,?_,?_,?_⟩
      · exact packet.1
      · exact packet.2.1
      · exact packet.2.2.1
      · let named := (plan₁).frozen_routing_image tape₁ order₁ position cal.frozenWitness tag₁ sites₁ edges₁ ports₁
          values x₁ hist dir₁ grid.sites_pos _ _ _ _ packet.2.2.2
        exact (congrArg (fun base => Packing.RoutingOutputs.Image _ _ _ _ base m) address).mpr named) (fun _ => rfl) bound siteLiteral sameLiteral

set_option maxHeartbeats 16000000 in
/-- The canonical W row keys and writer on a site whose directory already uses the semantic literal extent. -/
noncomputable def SignedCalendarAt.frozenHostPacketEntry
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (hist : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index) :=
  packetEntryForLiteral cal grid qpos position chart reader chargeFit routing values hist (dir₁).literal rfl

set_option maxHeartbeats 16000000 in
/-- The actual issued site's published memory realizes the same W row keys and signed reports
when its directory records the startup literal extent. -/
noncomputable def SignedCalendarAt.frozenIssuedHostPacketEntry
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (values : (seedBundle tape₁ axes d₁ order₁ position copies₁).Tables F)
    (hist : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index) :=
  let same := congrArg Directory.Layout.literal (cal.frozenIssuedPlacement grid qpos position chart reader chargeFit).1
  packetEntryForLiteral cal grid qpos position chart reader chargeFit routing values hist (initial₁).literal same

set_option maxHeartbeats 16000000 in
/-- Decode the canonical W report addresses from the selected pin and the two actual
native returns, using the processor fields supplied by that pin. -/
noncomputable def SignedCalendarAt.frozenHostProgramEntry
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (values : (seedBundle tape₁ axes d₁ (order₁) position copies₁).Tables F)
    (hist : (packHistory (seed₁ values) (plan₁).compiled.machine.epoch T₁).Index) :=
  programsFromHostPacket% (cal.frozenHostPacketEntry grid qpos position chart reader chargeFit routing values hist)

end Diagonal

end BorderVNP
end Computability
end OAI
