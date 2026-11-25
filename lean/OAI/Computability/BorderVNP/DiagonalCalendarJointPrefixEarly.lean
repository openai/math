import OAI.Computability.BorderVNP.DiagonalDeployedFrozenPrefixWriter
import OAI.Computability.BorderVNP.DiagonalCalendarEarlyParameters
import OAI.Computability.BorderVNP.DiagonalCalendarEarlyHistoryWidth
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedFrontWindow
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedSource
import OAI.Computability.BorderVNP.DiagonalCalendarIssuedHistory
import OAI.Computability.BorderVNP.DiagonalCalendarBootChecks
import OAI.Computability.BorderVNP.DiagonalCalendarPublicationRoom

/-! # The early clock on a decoded history of the actual signed calendar -/

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
open Diagonal.ExternalSew GridHosts
open scoped Classical BorderVNP.Epoch.Cube


open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
attribute [local instance] portFintype
attribute [local irreducible] Nat.clog UniversalMachine.programPrefix logWidth prefixCapacity
  FieldProcessor.freeWidth Fintype.equivFin
set_option maxRecDepth 8200
set_option maxHeartbeats 4400000
set_option synthInstance.maxSize 4000

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
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "number₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "table₁" => (located₁).raw.reserve ceiling₁
local notation "outside₁" => TeamScales.exterior (ξ₁) (r₁) (l+1)
local notation3 (prettyPrint := false) "directory₁" => freeDirectory R₁ r₁ (initial₁).literal ℓ₁ tiles
  (GridHosts.inputBlockWidth r₁ (l+1) axes d₁) J₁ description
local notation3 (prettyPrint := false) "fresh₁" => (initial₁).next+7*(directory₁).candidates
local notation3 (prettyPrint := false) "origin₁" =>
  Allocation.dest fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "P₁" => (signedProgram (cube.cubeID paid)).program
local notation3 (prettyPrint := false) "free₁" => (selectedSites).enrichedFree prog₁ P₁ (l+1) ec₁ ℓ₁
local notation3 (prettyPrint := false) "geoSeed" => ((plan₁).execute tape₁ order₁ position Unit).choose
local notation3 (prettyPrint := false) "widths₁" => fun i =>
  Fintype.card (Machine.Guess S (d₁+1) (fun _ _ => 60*logWidth r₁ (l+1)) i)
local notation3 (prettyPrint := false) "slots₁" => fun i =>
  Fintype.equivFin (Machine.Guess S (d₁+1) (fun _ _ => 60*logWidth r₁ (l+1)) i)
local notation3 (prettyPrint := false) "fit₁" => (plan₁).profile_order_fits widths₁ slots₁
local notation3 (prettyPrint := false) "arenaBase" =>
  Allocation.stop ((initial₁).next+7*(dir₁).candidates) cap₁ ceiling₁ (located₁).outputs w₁ w₁
open BorderVNP.Cube.Physical.NativeAssignments DiagonalTallyPacketEmit

local notation3 (prettyPrint := false) "addresses" => reader.deployedReferenceAddresses initial₁ selectedTask directory₁
  (adviceOffsetWith prog₁ r₁ 32 64 w₁ (l+1)) outside₁ fresh₁ cap₁ (table₁).size (located₁).outputs w₁
local notation3 (prettyPrint := false) "hold₁" => cal.frozenRouteBlock chart reader chargeFit
local notation3 (prettyPrint := false) "boots₁" => cal.frozenSites_boots grid qpos position chart reader chargeFit hold₁
local notation3 (prettyPrint := false) "bounds₁" => cal.frozenSpliceBounds grid
local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
local notation3 (prettyPrint := false) "codec(" v ")" => ((plan₁).compiled.machine.nativeCode (leaf(v))
   geoSeed x₁ rfl widths₁ slots₁ fit₁).toEmbedding.trans (Function.Embedding.subtype _)
local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
open RoutingISA.Evaluator.ScheduleClock
local notation "params₁" => pairedTableParameters (l+1) (size₁)
local notation "scalars₁" => Fintype.card (paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
local notation "public₁" => ⌈publicWork (cube.pred+1) scales.α (r₁) (l+1) (R₁+1)⌉₊
local notation "local₁" => ⌈localWork (cube.pred+1) (E+2) scales.α (ξ₁) (r₁) (l+1) (R₁+1)⌉₊
local notation "route₁" => 512*(cube.pred+1+BorderVNP.Cube.Tally.selectorWidth cube.pred cube.copies cube.h+1)
local notation3 (prettyPrint := false) "fixed₁" => (CubeConstants.install (cube.cubeID paid)).slots
local notation "argWidth" => BorderVNP.Cube.Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width
local notation "finish₁" => ScheduleClock.cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width argWidth
local notation "read₁" => BorderVNP.Cube.TeamRowClock.physicalCoefficient cube.pred cube.b cube.h cube.copies cube.width


open TeamContraction.JointHeader Packing.RoutingOutputs Packing.Inherited.FrozenTape
open BottomReports CellPacketGeometry TerminalCells Epoch.Round

local notation "cells₁" => CoverScale.sites (Cube D) (EnrichedOuter.depth S (d₁+1) T₁)
local notation3 (prettyPrint := false) "cables₁" => (boundaryShape S (d₁+1) T₁).edges+4*(R₁+1)*tiles
local notation "live₁" => (R₁+1)*tiles
local notation3 (prettyPrint := false) "program₁" => (withStartup (signedBody (cube.cubeID paid))).program
local notation3 (prettyPrint := false) "blank₁" => TimedProcessor.scaleData program₁
  (siteLibrary SparseExterior.driver) (fun _ : Fin 8 => some false) (geo₁)
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "issuedArgs" => cal.frozenIssuedAddresses grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "issuedMachine" => wiringWith prog₁ program₁ selectedSites pins₁ ℓ₁ (l+1) ec₁ (geo₁).fits
local notation3 (prettyPrint := false) "fieldHeader" => PositiveFields cap₁ (selectedTask).cube.n (selectedTask).cube.header.d
  (selectedTask).cube.header.cap (R₁+1) (selectedTask).dim w₁
local notation "window₁" => uniformWindows r₁ (R₁+1) outside₁ public₁ local₁ route₁ fixed₁ finish₁ read₁

set_option maxHeartbeats 8400000 in
/-- The exterior observed on a decoded calendar history, with the actual signed boots and
the issued receiver addresses, pays the early phase on each of its joint return tuples. -/
theorem SignedCalendarAt.frozenSites_profile_prefix_early
    (front : LocatedTableFrontAt cube b (E+2) fixed₁ finish₁ read₁ (l+1))
    (routing : LocatedFrozenRoutingAt cube b φ q adv c charge (l+1))
    (coreBound : CoreAt scales.α (ξ₁) (l+1))
    (headerBound : ((layout₁).header:ℝ)≤r₁*((l+1:ℕ):ℝ)^(24/25:ℝ))
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (historyIndex : history(values)) (p : fieldHeader) (pin : Fin pins₁ → Bool)
    (ex : {z // PositiveExterior issuedMachine issuedArgs pin w₁ z})
    (seen : ∀ e, JointHeader.observed layout₁ ex.val e=p.bits)
    (encoded : codec(values) historyIndex=p.profile) :
    let team := (boots₁).2.choose pin ex
    let starts := fun u => (team u).start
    ∀ (run : PinStart.JointPrefix (selectedTask).id starts) u,
      let v := PinStart.visits (selectedTask).id starts (run u)
      (team u).used+traceCost ((team u).pins (run u).1).val.1+
        traceCost v.profile.val.1+traceCost v.routing.val.1≤(window₁).core+(window₁).before := by
  let inputs := cal.frozenPacketInputs grid position
  have fields := inputs grid.sites_pos
  dsimp only at fields
  rw [←Nat.mul_assoc 6 (R₁+1) tiles,←Nat.mul_assoc 4 (R₁+1) tiles] at fields
  let small := fields.2.1
  let slots := fields.2.2.2.2.choose_spec.choose_spec
  let tags := cal.frozenPacketTags grid position
  let ctrl := cal.frozenEarlyControlFits grid qpos position chart reader chargeFit
  let deploy := cal.frozenEarlyTask grid qpos position chart reader chargeFit
  let geometry := cal.frozenEarlyGateTable grid qpos position chart reader chargeFit slots.1 fields.2.2.1 slots.2.2.1
  let bankStart := (initial₁).next+7*(dir₁).candidates
  let target := Allocation.dest bankStart cap₁ ceiling₁ (located₁).outputs w₁
  let banks := (selectedTask).cube.cellWriter (initial₁).frame
    (controlsBase target cables₁ cells₁ J₁ live₁) 0
  let outputEq := cal.frozenPacketOutputs grid qpos position chart reader chargeFit tags.1 tags.2
  let packetFits := cal.frozenPacketAllocation grid qpos position chart reader chargeFit
  let room := cal.frozenPublicationRoom grid qpos position chart reader chargeFit routing
  let addressesFit := room.2.2.2
  let gridFits := addressesFit.2.2.2
  let descriptions := gridFits.2.2.2
  let placement := cal.frozenSites_issued_placement_bounds grid qpos position chart reader chargeFit routing values historyIndex
  let routes := cal.locatedGateTable_routing grid qpos position chart reader chargeFit routing
  let traffic := cal.frozenEarlyHistoryWidth (ord:=ord) grid position routing values historyIndex
  let boot := cal.frozenBootBounds grid qpos position chart reader chargeFit
  let word := boot.2.2.2
  let hdr := word.2.2
  have targetEq : Allocation.dest bankStart cap₁ (table₁).size (located₁).outputs w₁=target :=
    congrArg (fun gates => Allocation.dest bankStart cap₁ gates (located₁).outputs w₁) (located₁).reserved_size
  have cellCount : cells₁=(selectedTask).cube.cells := congrArg (fun t : SignedTaskArena.Layout => t.cube.cells) deploy
  let placesFit (count : ℕ) := controlsBase target (selectedTask).cube.cables count J₁ live₁+8<2^w₁ ∧
    Directory.ISA.wordBound (Directory.ISA.placementBound dir₁
      (privateLayout (initial₁).frame target (selectedTask).cube.cables count J₁ description (selectedTask).p.privateGap).raw
      (bases target (selectedTask).cube.cables count J₁).livePairs (selectedTask).cube.cellStride)<2^w₁
  have locations : placesFit cells₁ := (congrArg placesFit cellCount).mpr placement.2.2
  have ceilingFit := geometry ▸ (located₁).raw_bound
  let applied := reader.deployed_frozen_prefix_early
    (paid:=paid) (aux:=φ ∘ cube.table) (characteristic:=q) (C:=common) (chart:=chart)
    (lenPred:=l) (s:=size₁) (literalOrder:=ord) (R:=R₁) (r:=r₁) (rw:=w₁) (pinWidth:=budget₁+6)
    (a:=a₁) (link:=ℓ₁) (ec:=ec₁) (d:=d₁) (order:=order₁) (schedule:=S) (T:=T₁) (Q:=Q)
    (copies:=copies₁) (headerFactor:=header) (σ:=Unit) (reserve:=cap₁) (cells:=cells₁)
    (ownerBits:=60*logWidth r₁ (l+1)) (packetWidth:=w₁) (qbits:=w₁) (tagCap:=ProgramSchemas.signedTagCapacity (e:=paid))
    (physical:=prog₁) (P:=program₁) (basis:=blank₁) (machineFit:=(geo₁).fits)
    (W:=W₁) (position:=position) (sites:=sites₁) (edges:=edges₁) (ports:=ports₁)
    (plan:=plan₁) (wireLayout:=layout₁) (x:=x₁) (seedTable:=values) (wr:=cal.seed.choose_spec.choose)
    (hm:=hm) (seeds:=fun t i z => (RowTrace.seedNumber S (d₁+1) t i z).val)
    (number:=fun z => cube.scalarNumber paid (.inl z)) (widths:=widths₁) (ord:=slots₁) (fit:=fit₁)
    (count:=grid.count) (cellNumber:=number₁) (vf:=small.2.2.2.2.2)
    (cf:=(Nat.lt_trans (Nat.lt_succ_self cells₁) small.2.2.2.2.1).le) (hg:=grid.block_pos)
    (short:=grid.block_le.trans_eq grid.link_eq) (pw:=grid.source_bounds.1) (extend:=small.2.2.2.1)
    (room:=grid.source_bounds.2) (hook:=cal.seed.choose_spec.choose_spec.2.2.2.1)
    (histQ:=historyIndex) (hardwareTemplate:=selectedTask) (sitePos:=grid.sites_pos)
    (cellPos:=Fintype.card_pos (α:=Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1)))
    (ownerFits:=small.2.2.2.1) (gadgets:=scalars₁) (digits:=w₁) (ctrlFit:=ctrl) (hs:=tags.1) (hf:=tags.2)
    (keyFits:=small.2.2.2.1) (sitesFit:=slots.1) (keysFit:=small.2.2.2.2.1) (sw:=fields.2.2.1) (pad:=slots.2.2.1)
    (dest:=target) (hdr:=header*logWidth r₁ (l+1)) (bankLayout:=banks) (bundleBits:=BundleSort.markedDepth cells₁ J₁)
    (shapes:=(W₁).frozenBundleShapes position ((fan S)^T₁) copies₁)
    (U:=8*(11920000+1500000+16008100*coeff+37)) (deg:=4*(E+2)) (exteriorBudget:=outside₁)
  let withTable := applied table₁ (congrArg (fun t => t.reserve ceiling₁) geometry) selectedTask deploy.symm rfl rfl
    inputs (grid.packetNumerals w₁ small.2.2.2.1) (outputEq ▸ packetFits) ceilingFit
    (congrArg (fun o => Allocation.dest bankStart cap₁ ceiling₁ o w₁) outputEq.symm)
    (cal.frozenDecoderHeaderWidth grid qpos position chart reader chargeFit)
  let atBoot := withTable hold₁ boot.1 boot.2.1 le_rfl (outputEq ▸ packetFits) boot.2.2.1 word.1
    word.2.1 hdr.1 hdr.2.1 (cal.frozenSewnPacketClock grid qpos position chart reader chargeFit)
  let atHeader := atBoot p pin ex seen encoded (selectedTask).cube.cellStride room.1 room.2.1 (cellCount.le.trans room.2.2.1)
    (addressesFit.1.trans_eq targetEq) addressesFit.2.1 gridFits.1 gridFits.2.1 gridFits.2.2.1 descriptions.1
    placement.1 placement.2.1 locations.1 locations.2 descriptions.2.1 descriptions.2.2
  let bounded := atHeader routes.1 traffic routes.2.1 rfl
    (congrArg StartupArena.literal (reader.frozenTask_startupArena (geo₁) ℓ₁ (layout₁).header)).le
    headerBound coreBound window₁
  let frozen := bounded (cal.frozenSites_issued_front_window grid qpos position chart reader chargeFit front routing values historyIndex _ _ _)
  intro nodes starts run u
  exact frozen run u

end Diagonal

end BorderVNP
end Computability
end OAI
