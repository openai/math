import OAI.Computability.BorderVNP.DiagonalCalendarOpeningAtOriginalReadback
import OAI.Computability.BorderVNP.DiagonalReindexedOpeningWriter
import OAI.Computability.BorderVNP.DiagonalIssuedNetworkParameters
import OAI.Computability.BorderVNP.DiagonalCalendarReportGeometryRep
import OAI.Computability.BorderVNP.DiagonalHistoryOpeningWordsOnReturn
import OAI.Computability.BorderVNP.DiagonalSelectedHistoryReportBanks
import OAI.Computability.BorderVNP.DiagonalSelectedOpeningOnHistory
import OAI.Computability.BorderVNP.DiagonalSelectedLookupHistoryMethods
import OAI.Computability.BorderVNP.DiagonalCalendarLookupInstalledOpeningWords
import OAI.Computability.BorderVNP.DiagonalCalendarNativeOpeningRule
import OAI.Computability.BorderVNP.DiagonalIssuedEnumerations
import OAI.Computability.BorderVNP.DiagonalCalendarLookupReportTests
import OAI.Computability.BorderVNP.DiagonalCandidateBankReportTests
import OAI.Computability.BorderVNP.DiagonalCalendarOpeningStaticFields
import OAI.Computability.BorderVNP.DiagonalCalendarOpeningBundleFit
import OAI.Computability.BorderVNP.DiagonalCalendarSortedSiteHeaders
import OAI.Computability.BorderVNP.DiagonalCalendarArgumentScalars
import OAI.Computability.BorderVNP.DiagonalOpeningNativePlacement
import OAI.Computability.BorderVNP.DiagonalCalendarArgumentRoom
import OAI.Computability.BorderVNP.DiagonalReplayOpeningReadback
import OAI.Computability.BorderVNP.DiagonalSelectedOpeningReadback
import OAI.Computability.BorderVNP.DiagonalCandidateControlCableCast
import OAI.Computability.BorderVNP.PackedNativeDemandCableCast
import OAI.Computability.BorderVNP.DiagonalSelectedReportPacking
import OAI.Computability.BorderVNP.PackedCableOrderCast

/-! # Native control returns on the selected report bank -/

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

variable (oper : FrozenExecutionAt cube b φ q adv c charge header (hm:=hm) (l+1)) (qpos : 1 ≤ Q)
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
local notation3 (prettyPrint := false) "located₁" => cal.locatedGateTable oper.grid qpos position (initial₁)
local notation3 (prettyPrint := false) "plan₁" => cal.seed.choose
local notation3 (prettyPrint := false) "W₁" => cal.frozenWitness
local notation3 (prettyPrint := false) "sites₁" => (Fintype.equivFin (((W₁).routedFine position).Site)).toEmbedding
local notation3 (prettyPrint := false) "edges₁" => (Fintype.equivFin (((W₁).routedFine position).Edge)).toEmbedding
local notation3 (prettyPrint := false) "ports₁" => (Fintype.equivFin (Fin (r₁) × Fin (publicWidth (tape₁)))).toEmbedding
local notation3 (prettyPrint := false) "number₁" => Fintype.equivFin (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1))
local notation3 (prettyPrint := false) "tag₁" => ParseTable.signedLiteralCode (s:=size₁) ord
local notation3 (prettyPrint := false) "x₁" => fun _ : Unit => false

local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "selectedSites" => cal.frozenSites oper.grid qpos position chart reader chargeFit
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
local notation3 (prettyPrint := false) "boots₁" => cal.frozenSites_boots oper.grid qpos position chart reader chargeFit hold₁
local notation3 (prettyPrint := false) "bounds₁" => cal.frozenSpliceBounds oper.grid
local notation3 (prettyPrint := false) "leaf(" v ")" => (plan₁).frozenLeaf tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ v x₁
local notation3 (prettyPrint := false) "history(" v ")" => (packHistory (leaf(v)) (plan₁).compiled.machine.epoch T₁).Index
local notation3 (prettyPrint := false) "codec(" v ")" => ((plan₁).compiled.machine.nativeCode (leaf(v))
   geoSeed x₁ rfl widths₁ slots₁ fit₁).toEmbedding.trans (Function.Embedding.subtype _)
local notation "identifiers" => paid.Entry ⊕ BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "numberIDs" => (Fintype.equivFin identifiers).toEmbedding.trans Fin.valEmbedding
local notation "qdim" => pairedTableParameters (l+1) size₁+Fintype.card identifiers
local notation3 (prettyPrint := false) "fullPin" h => (boxPinCodec (pairedTableParameters (l+1) size₁) reader.rankFits reader.boxFits).encode h

open JointHeader Routing RoutingISA.Evaluator.SignedPrep CellEntries
local notation3 (prettyPrint := false) "geom₁" =>
  (selectedTask).withNetwork (Fintype.card (Cube D → Deck (EnrichedOuter.depth S (d₁+1) T₁+1)))
    ((boundaryShape S (d₁+1) T₁).edges+4*(R₁+1)*tiles)
local notation3 (prettyPrint := false) "planner₁" => cal.frozenPlannerTask oper.grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "elig(" vs "," hist ")" =>
  (plan₁).signedBroadcastAllowed prog₁ (geo₁).fits W₁ position tag₁ sites₁ edges₁ ports₁ vs
    ((geoSeed).eval x₁) (leaf(vs)).property free₁ oper.grid.count (bounds₁).2.1 hist cube scales.α ξ₁
    (bounds₁).1 (geo₁).literalSize (bounds₁).2.2 number₁ (selectedTask).p arenaBase cap₁
local notation3 (prettyPrint := false) "packet(" vs "," hist ")" =>
  (plan₁).signedPackets oper.grid.count tape₁ order₁ position W₁ tag₁ sites₁ edges₁ ports₁ vs
    ((geoSeed).eval x₁) (leaf(vs)).property cube scales.α ξ₁ (bounds₁).1
    (geo₁).literalSize (bounds₁).2.2 (bounds₁).2.1 number₁ (selectedTask).p.privateGap hist
local notation3 (prettyPrint := false) "source(" vs "," hist ")" =>
  (plan₁).signedReportSources (D:=D) (m:=«m») (e:=paid) (S:=S) (R:=R₁) (r:=r₁) (pins:=pins₁)
    (link:=ℓ₁) (k:=l) (d:=d₁) (a:=extra₁) (regs:=64) (rw:=w₁) (ec:=ec₁) (width:=w₁+1)
    (s:=size₁) (copies:=copies₁) (T:=T₁) (header:=header) (work:=Q)
    prog₁ (geo₁).fits W₁ position tag₁ sites₁ edges₁ ports₁ vs ((geoSeed).eval x₁) (leaf(vs)).property
    (fun t i z => ((ExternalSew.RowTrace.seedNumber S (d₁+1) t i) z).val) free₁ oper.grid.count
    (Sum.inl : paid.Entry → identifiers) numberIDs (bounds₁).2.1 hist cube scales.α ξ₁ (bounds₁).1 (geo₁).literalSize
    (bounds₁).2.2 number₁ (selectedTask).p arenaBase cap₁ (fun u => ((selectedSites).publicWords u 0).val)
    (fun _ => origin₁)



open Packing.RoutingOutputs

private theorem originalHeaderOnFrame {old frame origin cables cells entries : ℕ} {ram : ℕ → ℕ}
    (same : old = frame) (header : Header old origin cables cells entries ram) :
    Header frame origin cables cells entries ram := same ▸ header

private theorem originalOpenFieldsOnFrame {t : SignedTaskArena.Layout}
    {team old frame ends ctrl live ports entries : ℕ} {ram : ℕ → ℕ}
    (same : old = frame) (fields : t.OpenFields team old ends ctrl live ports entries ram) :
    t.OpenFields team frame ends ctrl live ports entries ram := same ▸ fields

private theorem actualRoomOnCommonFrame {task : SignedTaskArena.Layout}
    {base frame ends ctrl live ports entries rows width : ℕ}
    (same : base = frame) (room : task.OpenRoom base ends ctrl live ports entries rows width) :
    task.OpenRoom frame ends ctrl live ports entries rows width := same ▸ room

set_option cleanup.letToHave false in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 25000000 in
set_option Elab.async false in
/-- The exact control predicate for the issued calendar at its actual reached selection. -/
private def SignedCalendarAt.issuedOriginalOpeningPredicate
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) (allowed : (elig(values,hist)) raw.val) : Prop :=
    originalNativeOpeningHandler% (cal.frozenLookupAt oper qpos position chart reader chargeFit values h i hist claim raw allowed)

set_option cleanup.letToHave false in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 25000000 in
set_option Elab.async false in
private theorem originalReturnedNativeOpening
    (values : (seedBundle (tape₁) axes d₁ (order₁) position copies₁).Tables F)
    (h : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin (pairedTableParameters (l+1) size₁))
      (chart.pinRadius (R₁+1) r₁))
    (i : Fin pins₁ → Bool) (hist : history(values)) (claim : Fin ((R₁+1)*(qdim)*w₁) → Bool)
    (raw : CheckedBroadcast (planner₁).cube) (allowed : (elig(values,hist)) raw.val)
    (publication : cal.LookupReportPublicationAt oper qpos position chart reader chargeFit values h i hist claim raw allowed)
    (capacity : cal.LookupReportCapacityAt oper qpos position chart reader chargeFit values h i hist claim raw allowed) :
    cal.issuedOriginalOpeningPredicate oper qpos position chart reader chargeFit values h i hist claim raw allowed := by
  classical
  let lookup := cal.frozenLookupAt oper qpos position chart reader chargeFit values h i hist claim raw allowed
  let enumerations := lookup.issuedEnumerations
  let _ := enumerations.1
  let _ := enumerations.2
  intro operands z H delivery _table _row writers actual _pins _received q endRows handoff observed symbols
  let exterior := z.1
  let atSite := originalSiteOnActual% lookup exterior H actual
  let reportOnHistory := originalPublicationOnActual% lookup exterior H actual (publication exterior)
  let pub₁ := Classical.choice reportOnHistory
  let capacityOnHistory := originalCapacityOnActual% lookup exterior H actual (capacity exterior q.val)
  let capData := Classical.choice capacityOnHistory
  applyOriginalReportOpening lookup exterior H actual
  have stages := originalStagesOnActual% lookup exterior H actual
  let allWords := (cal.frozenLookupInstalledOpeningWords oper qpos position chart reader chargeFit values h i hist claim raw allowed).2
  have readAt (u : Fin (R₁+1)) : cal.LookupOpeningWords oper qpos position chart reader chargeFit values hist u
      (readings (issuedField% geometry (atSite u))) :=
    openingWordsOnHistory% (w₁) allWords exterior u stages
  have memory (u : Fin (R₁+1)) := (readAt u).1
  have start (u : Fin (R₁+1)) := (readAt u).2
  have budget := cal.frozenOpeningStaticFields oper qpos position chart reader chargeFit values hist
  have layout := cal.frozenArgumentPublicationRoom oper.grid qpos position chart reader chargeFit oper.routing
  have bundleFits := cal.frozenOpeningBundleFit oper qpos position chart reader chargeFit
  have same := (cal.frozenPlannerTask_eq oper.grid qpos position chart reader chargeFit).symm.trans
    (cal.frozenEarlyTask oper.grid qpos position chart reader chargeFit)
  have scalars := cal.frozenArgumentScalars oper.grid qpos position chart reader chargeFit oper.routing
  have teamRoom := layout.2.2
  have fieldRoom := teamRoom.2.2
  have cellRoom := fieldRoom.2.2
  let shape := (W₁).frozenBundleShapes position ((fan S)^T₁) copies₁
  have sortedAt := fun u => (memory u).2.2.2
  have fitted := fun u => (memory u).2.1
  have heads := fun u => (memory u).1
  have ready := fun u => (start u).1
  have literals := fun u => (memory u).2.2.1
  let issued := cal.frozenReportGeometry oper.grid qpos position chart reader chargeFit values hist
  have orderCap := (plan₁).issuedReportPacking prog₁ (geo₁).fits W₁ position tag₁ sites₁ edges₁ ports₁
    values ((geoSeed).eval x₁) (leaf(values)).property free₁ oper.grid.count (bounds₁).2.1 hist cube scales.α ξ₁
    (bounds₁).1 (geo₁).literalSize (bounds₁).2.2 number₁ (selectedTask).p arenaBase cap₁
  let seedIDs := fun t j v => ((ExternalSew.RowTrace.seedNumber S (d₁+1) t j) v).val
  have edgeEq := ((plan₁).signedReportArena_cables prog₁ (geo₁).fits W₁ position tag₁ sites₁ edges₁ ports₁
    values ((geoSeed).eval x₁) (leaf(values)).property seedIDs free₁ oper.grid.count
    (Sum.inl : paid.Entry → identifiers) numberIDs (bounds₁).2.1 hist cube scales.α ξ₁ (bounds₁).1
    (geo₁).literalSize (bounds₁).2.2 number₁ (selectedTask).p arenaBase cap₁).symm
  have geometry := cal.frozenReportGeometry_rep oper.grid qpos position chart reader chargeFit values hist
  let originalRep := geometry.1
  let originalPorts := issuedNetworkField% originalRep P
  let _ : Fintype originalPorts := inferInstanceAs (Fintype (FreeBlock R₁ tiles))
  let network := issuedNetworkField% originalRep N
  let locations := issuedNetworkField% originalRep cell
  let costs := issuedNetworkField% originalRep aux
  let siteKeys := issuedNetworkField% originalRep siteID
  let cableKeys := issuedNetworkField% originalRep edgeID
  let portKeys := issuedNetworkField% originalRep portID
  let hardwareCables : network.Edge ↪ Fin (planner₁).cube.cables := cableKeys.trans (finCongr edgeEq).toEmbedding
  let hardware := issued.1.castRect rfl edgeEq
  have represented : ∀ _u : Fin (R₁+1),
      CellAddressPhysical.Represents network locations costs siteKeys hardwareCables portKeys hardware issued.2 :=
    fun _ => CellAddressPhysical.Represents.castCables edgeEq originalRep
  have numbered (c : Fin (planner₁).cube.cells) : (hardware.cells c).val=c.val :=
    (congrArg (fun e => (e c).val) (CellAddressCircuit.Fields.castRect_cells (F:=issued.1) edgeEq)).trans (geometry.2 c)
  have publicFrame (u : Fin (R₁+1)) := cal.frozenSites_frame oper.grid qpos position chart reader chargeFit u
  have wherePlaced (u : Fin (R₁+1)) := (issuedField% place pub₁) u
  have originals (u : Fin (R₁+1)) := (issuedField% image pub₁) u
  let live : (Fin (dir₁).teams × Fin (dir₁).sites) ↪ originalPorts :=
    (Equiv.refl (FreeBlock R₁ tiles)).toEmbedding
  let pinSite : Fin (dir₁).entries ↪ network.Site := originalDescriptionRows (plan₁).compiled.machine (leaf(values)) hist dir₁ rfl order₁
  applyIssuedOpeningReadback (cal.openingPlanAtHistory oper qpos position chart reader chargeFit values hist)
  apply writers.candidate_control_tests_castCables (task:=planner₁) (gap:=(planner₁).p.privateGap)
    (geoOrigin:=origin₁) (frame:=(initial₁).frame) (next:=(initial₁).next) (N:=network) (cell:=locations)
    (aux:=costs) (siteID:=siteKeys) (edgeID:=cableKeys) (he:=edgeEq) (portID:=portKeys) (fields:=issued.1)
    (x:=fun _ => issued.2) (original:=pinSite) (live:=live) (shape:=shape)
    (valid:=VPVNP.VerifierNetwork.Frame.initial (fun _ : Unit => Sum.inr true)) (raw:=raw.val) (broadcast:=(initial₁).broadcastBase)
    (hd:=show 0<(planner₁).cube.header.d by rw [same]; exact scalars.2.1) (site:=atSite)
    (q:=q.val) (symbols:=symbols) (handoff:=handoff) (receipt:=observed) (bounds:=scalars.1)
    (common:=rfl) (shared:=fun u => congrArg readings (stages u).2.2.2.2.2.1.symm)
    (old:=(issuedField% old pub₁)) (pinned:=(issuedField% pin pub₁)) (subtotal:=(issuedField% subtotal pub₁))
    (literal:=(issuedField% literal pub₁)) (address:=(issuedField% address pub₁)) (copyAt:=fun _ => rfl)
    (net:=represented) (codes:=numbered) (fieldRoom:=(issuedField% widths capData))
    (hk:=(cal.frozenPacketInputs oper.grid position oper.grid.sites_pos).2.1.2.2.2.1)
    (wordFit:=(issuedField% fit capData)) (liveWidth:=fun _ => rfl) (img:=originals)
    (placement:=fun u => actualPrivateImageOnFrame (issuedField% origin (atSite u)) (wherePlaced u))
    (scratch:=layout.1) (originFit:=layout.2.1) (teams:=teamRoom.1) (procs:=teamRoom.2.1)
    (fieldFit:=fieldRoom.1) (lit:=fieldRoom.2.1) (cells:=by simpa only [same] using cellRoom.1)
    (strideFit:=by simpa only [same] using cellRoom.2.1)
    (keysFit:=by simpa only [same] using bundleFits.1) (descFit:=bundleFits.2.1)
    (scanFit:=bundleFits.2.2.1) (copies:=bundleFits.2.2.2.1) (strides:=bundleFits.2.2.2.2)
    (room:=actualRoomOnCommonFrame (issuedField% origin (atSite 0)) ((issuedField% space pub₁) 0))
    (packing:=orderCap)
  case positive => exact Fintype.card_pos
  case privateRoom => intro u; exact actualPrivateFitOnFrame (publicFrame u) (fitted u)
  case head => intro u; exact originalHeaderOnFrame (publicFrame u) (heads u)
  case nativeW =>
    intro u
    let physicalNet := (issuedField% net capData) u
    let canonical := issuedField% placement (atSite u)
    let physicallyIndexed := writerAcrossCables% canonical edgeEq
    let resolvedPlace := actualPrivateImageOnFrame (issuedField% origin (atSite u)) (wherePlaced u)
    let resolvedFit := actualPrivateFitOnFrame (publicFrame u) (fitted u)
    exact ⟨SlottedWriter.onNativePlacement (ar:=(planner₁).cube)
      (N:=issuedNetworkField% physicalNet N) (cell:=issuedNetworkField% physicalNet cell)
      (dir:=dir₁) (edges:=issuedNetworkField% physicalNet edgeID) (ports:=issuedNetworkField% physicalNet portID)
      (F:=issuedNetworkField% physicalNet F) (gap:=(planner₁).p.privateGap)
      (writer:=physicallyIndexed) (original:=pinSite) (live:=live) (head:=(initial₁).frame) (origin:=origin₁)
      (before:=issuedField% geometry (atSite u)) (net:=physicalNet) (codes:=issuedField% codes capData)
      (extent:=issuedField% widths capData) (liveWidth:=fun _ => rfl) (image:=originals u)
      (placed:=resolvedPlace) (fit:=resolvedFit)⟩
  case payload => exact budget.payload
  case rank => exact budget.rank
  case ctrlFit => exact budget.ctrlFit
  case boot => intro u; exact originalOpenFieldsOnFrame (t:=planner₁) (publicFrame u) (ready u)
  case capacity => exact budget.capacity
  case controls => intro u j; exact literals u j
  case sorted =>
    intro u j
    exact cal.frozenSortedBundleWords_on_layout oper.grid qpos position chart reader chargeFit values hist
      (readings (issuedField% geometry (atSite u))) (sortedAt u) edgeEq (planner₁) same.symm
      (initial₁).frame (controlsBase origin₁ (planner₁).cube.cables (planner₁).cube.cells
        (dir₁).entries ((dir₁).teams * (dir₁).sites))
      (Fin.ofNat ((planner₁).cube.n+1) (BorderVNP.Cube.Physical.readCode ((planner₁).cube.n+1) raw.val.1)) j

private noncomputable def originalReturnedNativeOpeningProof : (P : Prop) ×' P :=
  ⟨_, @originalReturnedNativeOpening⟩

/-- On every reached replay of the selected writer, the native controls test the
marked headers and preserve the incoming memory read by each team. -/
theorem SignedCalendarAt.frozenNativeOpeningHandler : originalReturnedNativeOpeningProof.1 :=
  originalReturnedNativeOpeningProof.2

end Diagonal

end BorderVNP
end Computability
end OAI
