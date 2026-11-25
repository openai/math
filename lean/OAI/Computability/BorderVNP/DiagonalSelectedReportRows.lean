import OAI.Computability.BorderVNP.DiagonalSignedPacketAdmission
import OAI.Computability.BorderVNP.DiagonalFrozenReportBundleRoom
import OAI.Computability.BorderVNP.PackedNativeDemandBundleHeader
import OAI.Computability.BorderVNP.PackedNativeDemandPlacement
import OAI.Computability.BorderVNP.PackedFrozenBundleShape
import OAI.Computability.BorderVNP.DiagonalCompiledGuardedDirectory
import OAI.Computability.BorderVNP.DiagonalRoutedReportProposals
import OAI.Computability.BorderVNP.DiagonalCubeSelectedWorkspace
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomParameters
import OAI.Computability.BorderVNP.DiagonalFixedSignedSites
import OAI.Computability.BorderVNP.DiagonalReportSourcePrefix
import OAI.Computability.BorderVNP.PackedRetainedReportUse
import OAI.Computability.BorderVNP.PackedSeedCoreChoices
import OAI.Computability.BorderVNP.DiagonalSignedSewnRetainedBirths
import OAI.Computability.BorderVNP.FiniteEvaluatorCellKey

/-! # The filled signed report directory on each history, before private claims -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open Packing.BundleDirectory

/-- A cell emitted by the stable original-bundle grouping contains exactly
its source bundles in ordinal order. -/
theorem sourceCells_bundles {C J : ℕ} (l : ReportLayout) (home : Fin J → Fin C)
    (payload : Fin J → ReportBundle) (team : ℕ) (who bank supply privateWidth : ℕ → ℕ)
    (digits : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (i : Fin (sourceCells l home payload team who bank supply privateWidth digits).length) :
    let r := (sourceCells l home payload team who bank supply privateWidth digits).get i
    r.bundles = (sourceRows home r.number).map payload := by
  intro r
  have hr : r ∈ sourceCells l home payload team who bank supply privateWidth digits := List.get_mem _ i
  obtain ⟨c,_,eq⟩ := List.mem_map.mp hr
  exact (congrArg (fun v : ReportCell l => v.bundles = (sourceRows home v.number).map payload) eq).mp rfl

/-- The reported widths on a compact cell come from that cell's global
supplied and private word counts. -/
theorem sourceCells_widths {C J : ℕ} (l : ReportLayout) (home : Fin J → Fin C)
    (payload : Fin J → ReportBundle) (team : ℕ) (who bank supply privateWidth : ℕ → ℕ)
    (digits : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (i : Fin (sourceCells l home payload team who bank supply privateWidth digits).length) :
    let r := (sourceCells l home payload team who bank supply privateWidth digits).get i
    r.supplied = supply r.number ∧ r.privateWires = privateWidth r.number := by
  intro r
  have hr : r ∈ sourceCells l home payload team who bank supply privateWidth digits := List.get_mem _ i
  obtain ⟨c,_,eq⟩ := List.mem_map.mp hr
  exact (congrArg (fun v : ReportCell l => v.supplied = supply v.number ∧ v.privateWires = privateWidth v.number) eq).mp ⟨rfl,rfl⟩

end DiagonalTallyCellReports.ReportDirectory

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP
open VPVNP.ParseGrammar EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pins link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "C" => plan.compiled
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "budget" => boundaryBudget S mass
local notation3 (prettyPrint := false) "word₀" => 60*logWidth r (k+1)
local notation3 (prettyPrint := false) "seedBlock" => GridHosts.inputBlockWidth r (k+1) axes d
local notation3 (prettyPrint := false) "seedCap" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation3 (prettyPrint := false) "desc" => seedDescriptionWidth (k+1) r axes d (header*logWidth r (k+1)) (BottomGridBank.bodyBudget seedCap)

variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := word₀) budget
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "baseProg" => Boundary.wiredSeedStatePrograms S W position code sites edges ports copies table words
local notation3 (prettyPrint := false) "source" => EnrichedTape.base (Gadget := Gadget) p fit W position leaf rfl
local notation3 (prettyPrint := false) "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "M" => (C).machine
local notation3 (prettyPrint := false) "rows" => (C).privateSiteRows key seeds
local notation3 (prettyPrint := false) "oldPorts" => privatePorts S key
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words) good)
      plan.compiled.machine.epoch T).Index)
local notation3 (prettyPrint := false) "lastState" => ((packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).term q).val
local notation3 (prettyPrint := false) "net" => EnrichedTape.network (pins := pins) p fit position free count M leaf rfl q
local notation3 (prettyPrint := false) "host" => ((Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2))).symm.toEmbedding.trans
  (enrichedOuterHosts M leaf q).site)
local notation3 (prettyPrint := false) "lastProgs" => (C).machine.terminalPrivatePrograms rows (num ∘ pos) leaf baseProg q
local notation3 (prettyPrint := false) "programs" => enrichedSewnPrograms G₁ axes d order position count M leaf rfl (Flat.portRows T (oldPorts T))
  hp q lastProgs
local notation3 (prettyPrint := false) "slabs" => fun j : Fin ((fan S)^T) × (Fin axes → Deck (d+2)) => W.seedSlab position code sites edges ports j.2
local notation3 (prettyPrint := false) "hidden" => W.bottomChoicesEquiv position edges slabs (fun _ => rfl)

open BorderVNP.Cube (TableEntry)
open BorderVNP.Cube.Physical Packing.CellAddresses Packing.BottomReports
open BorderVNP.Packing.RoutingOutputs.NativeDemands
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open DiagonalTallyAllocation DiagonalTallyCellReports ReportDirectory

variable {F : Type} [Field F] (cube : FixedCube F) (α ξ : ℝ)
    (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)

variable (parameters : RoutingISA.SignedTaskArena.Parameters)
local notation3 (prettyPrint := false) "gap" => parameters.privateGap
local notation3 (prettyPrint := false) "deliveries" => freeDirectory R r ((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))
  link tiles seedBlock ((fan S)^T*tiles) desc
local notation3 (prettyPrint := false) "cell" => fun v : (net).Site => number (reduceMove (depth S (d+1) T) ((lastState).route.origin v))
local notation3 (prettyPrint := false) "edge" => FieldExport.mergedEdges (fieldSewParams G₁ axes d) hp (lastState).rows.edge
local notation3 (prettyPrint := false) "port" => (finProdFinEquiv.toEmbedding : FreeBlock R tiles ↪ Fin ((R+1)*tiles))
local notation3 (prettyPrint := false) "original" => originalDescriptionRows M leaf q deliveries rfl order
local notation3 (prettyPrint := false) "live" => (Equiv.refl (FreeBlock R tiles)).toEmbedding
local notation3 (prettyPrint := false) "packed" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap q
local notation3 (prettyPrint := false) "allRows" => calibrated G₀ lit order position W code sites edges ports table words good
local notation3 (prettyPrint := false) "rowBudget" => (allRows).choose_spec q number edge port gap
local notation3 (prettyPrint := false) "demandRows" => RoutingOutputs.NativeDemands.rows net cell edge port deliveries original live gap
local notation3 (prettyPrint := false) "recv" => RoutingOutputs.NativeDemands.receiver net cell edge port deliveries original live gap (allRows).choose
local notation3 (prettyPrint := false) "weight" => fun z : Fin (demandRows).length => (demandRows)[z.val].width

local notation3 (prettyPrint := false) "B" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number gap

variable (arenaBase profileBits : ℕ)
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "task" => (SignedTaskArena.Layout.mk arena (cube.cubeID e) parameters)
variable (frame origin : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "charts" => fun u : Fin (R+1) =>
  reportLayout (task).before (task).after (frame u)
    (RoutingOutputs.controlsBase (origin u) (arena).cables cells (deliveries).entries ((R+1)*tiles))
    parameters.parameters parameters.siteWidth parameters.bodyCap (arena).stop
local notation3 (prettyPrint := false) "home" => fun j : Fin (deliveries).entries => (B).cell (original j)
local notation3 (prettyPrint := false) "charges" => placedSize net (B).programs
local notation3 (prettyPrint := false) "supply" =>
  fun c : ℕ => suppliedSize net (fun v => ((B).cell v).val) c
local notation3 (prettyPrint := false) "wire" => fun c : ℕ =>
  guessedSize net (fun v => ((B).cell v).val) c+siteSize net (fun v => ((B).cell v).val) c charges
local notation3 (prettyPrint := false) "sourceSlot" => fun j : Fin (deliveries).entries =>
  (arena).cellBank+(home j).val*(arena).cellStride+
    (RoutingOutputs.NativeDemands.destination net cell edge port deliveries original live gap (.inl j)).2
local notation3 (prettyPrint := false) "boxStart" => fun j : Fin (deliveries).entries =>
  siteBase net (B).cell (home j) (B).siteID charges (Subtype.mk (original j) rfl)
local notation3 (prettyPrint := false) "bundleIdx" => descriptionOrder (leaf).val.pack ((fan S)^T) tiles (deliveries).entries rfl order
local notation3 (prettyPrint := false) "ch" => (groupedGridRows G₀ axes d order position copies).edge
local notation3 (prettyPrint := false) "gp" => (Equiv.refl (Fin tiles)).toEmbedding
local notation3 (prettyPrint := false) "bundle" => fun j : Fin (deliveries).entries =>
  W.seedUseBundle position code sites edges ports ch gp ((bundleIdx j).2) (sourceSlot j) (boxStart j) copies (fun _ => false)

/-- The physical allocation's cable rectangle equals the selected program's
sparse old-edge and sewn-edge directory on this history. -/
theorem signedReportArena_cables : (arena).cables = (B).edgeRows := by
  change (boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1)) =
    (boundary S (d+1) T).edges+4*(R+1)*tiles
  rw [←seedPortCount (D:=D) d,Nat.mul_assoc]

/-- The actual physical report address map on each team. -/
noncomputable abbrev signedNativeReportLayouts : Fin (R+1) → ReportLayout := charts

/-- The chosen selector assigns each cell to its selected physical group owner. -/
noncomputable abbrev signedGroupOwner (v : Routed (b:=cube.b) (s:=cube.width) (B).owners)
    (c : Fin cells) : Fin (R+1) :=
  (B).owners v.1 ((packed).label c (BorderVNP.Cube.Physical.chosen cube.b cube.width v.1))

/-- The actual reduced receiving cell of each original serialized bundle. -/
noncomputable abbrev signedReportHome (j : Fin (deliveries).entries) : Fin cells := home j

/-- The original opaque factor packet, with the numeric absolute address of
its sidecar and the relative offset of its birth work in the receiving cell. -/
noncomputable abbrev signedReportBundle (j : Fin (deliveries).entries) : ReportBundle := bundle j

/-- Each actual history of the seed plan fits the report reservation of the chosen
signed task. The canonical private row numbering determines the original tile; its
word offset, birth offset and cell number are those of this history's deployed bank. -/
theorem signedReportBundle_frozen_room {extra exponent dlog Q A B₀ depthIndex : ℕ}
    {scale : EpochScales S (cube.pred+1) extra}
    (sched : JointSchedule.{0} scale (exponent+1) dlog Q A B₀ depthIndex)
    (initial : TeamContraction.ProcessorSlots.StartupArena) (H reserve ceiling outputs field : ℕ)
    (dirs : SignedTaskArena.GeometryDirectories)
    (length : r=stretch sched.ρ (k+1))
    (chart : CoverScale.initialDepth (Cube D) r (k+1)=d+1)
    (history : T=epochs scale.τ (k+1)) (team : R=sched.physical.teamsPred (k+1)) :
    let sa := sched.frozenSignedTask cube (k+1) k s H initial deliveries reserve ceiling outputs field dirs
    (∀ c : Fin cells, supplementWords ((BundleDirectory.sourceRows home c.val).map bundle) ≤ sa.p.report.supplementStride) ∧
    (∀ j, (bundle j).positions.length ≤ sa.p.report.marked) ∧
    (∑ j, (bundle j).useCount) = sa.p.report.uses := by
  let orig := (bundleIdx).trans (Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2)))
  exact sched.frozenReportBundle_room cube (copies:=copies) W position orig code sites edges ports ch gp
    sourceSlot boxStart (fun _ _ => false) initial deliveries H reserve ceiling outputs field dirs length chart
    (by rw [history]; rfl) (count.trans (congrArg (·+1) team)) home

/-- The birth checker and report sidecar share one original row address,
source order, copy count, work range and native finite factor list. -/
noncomputable abbrev signedReportCoreBundles (j : Fin (deliveries).entries) : Packing.BottomReports.Bundle :=
  W.seedCoreBundle position code sites edges ports ((bundleIdx j).2) (sourceSlot j) (boxStart j) copies

/-- Opaque stored one-copy factor body of the original physical packet. -/
noncomputable abbrev signedReportBody (j : Fin (deliveries).entries) : List CellSparse.Factor :=
  W.seedStored position code sites edges ports ch gp (bundleIdx j).2

/-- The complete retained bundle list of a cell, in native original source order. -/
noncomputable abbrev signedCellBundles (c : Fin cells) : List Packing.BottomReports.Bundle :=
  (Packing.BundleDirectory.sourceRows home c.val).map
    (fun j => W.seedCoreBundle position code sites edges ports (bundleIdx j).2 (sourceSlot j) (boxStart j) copies)

/-- Every original physical bundle has a positive copy count and a nonempty
work stride, including a tile with no selected private source wires. -/
theorem signedReportOrigins_positive (hr : 0<r) (j : Fin (deliveries).entries) :
    0 < (bundle j).header.copies ∧ 0 < (bundle j).header.stride := by
  have copiesPos : 0 < copies := Nat.pos_of_ne_zero (fun h => by rw [h,Nat.mul_zero] at count; omega)
  have capPos := seedSiteCapacity_pos (Nat.succ_pos k) hr axes d
  change 0<copies ∧ 0<_ + seedSiteCapacity (k+1) r axes d
  exact ⟨copiesPos,Nat.add_pos_right _ capPos⟩

/-- All named source rows are genuine retained births of the terminal checker,
with the same physical private work base and sparse site number. -/
theorem signedReportRetainedBirths :
    RetainedBirths net (fun v => ((B).cell v).val) (fun v => ((B).programs v).program) (B).siteID original
      (fun j => W.seedCoreBundle position code sites edges ports (bundleIdx j).2 (sourceSlot j) (boxStart j) copies) := by
  let ix := ((bundleIdx).trans (Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2)))).toEmbedding
  apply signedSewn_retainedBirths W position code sites edges ports table C words good seeds key (num ∘ pos)
    G₁ count hp rfl q ix (fun v => ((B).cell v).val) (B).siteID sourceSlot boxStart
  intro j
  exact (FiniteEvaluator.Merged.CellKey.site net (B).cell Fin.valEmbedding (home j) (B).siteID
    (fun v => ((B).programs v).program) ⟨original j,rfl⟩).symm

/-- Every original report body is read at the retained vertex of its
original row-major bundle. Its source slot includes the reserved report gap. -/
noncomputable def signedReportSources : SourceReports arena (B).owners :=
  routedSourceReports arena net (B).cell (B).owners (B).slot (packed).label charts home bundle supply wire

local notation3 (prettyPrint := false) "sources" => plan.signedReportSources p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin

/-- The physical padding condition in the selected report source is the
same pair of endpoint tests that defines a reconstructed routed cube. -/
theorem signedReportSources_route :
    {v : Routed (b:=cube.b) (s:=cube.width) (B).owners // (sources).pins v} = (B).Route cube.width := rfl

/-- On a raw routed choice the report-source admission is exactly the
native pair of endpoint padding tests, before a report or cell bank is fixed. -/
theorem signedReportSources_pins (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) :
    (sources).pins v ↔ RoutedPins net (B).cell (B).owners (B).slot v := Iff.rfl

/-- Actual globally numbered signed report rows at the chosen selector. -/
noncomputable def signedReceivedRows (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) :
    ReceivedRows charts (B).cells :=
  routedReceivedRows arena (B).owners (packed).label charts home bundle supply wire v

local notation3 (prettyPrint := false) "received" => plan.signedReceivedRows p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin

/-- The reports sampled from the selected routed source index exactly
those same true cells, including empty cells and empty choices. -/
def signedReportAssignments (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) :
    (sources).actual v ≃ ((u : Fin (R+1)) → ReportAssignments ((received v).cells u)) := Equiv.refl _

/-- The global numerical row on every issued team-local cell, including
cells with no opaque originals. -/
theorem signedReceivedRows_number (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1))
    (i : Fin ((received v).cells u).length) :
    (((received v).cells u).get i).number = ((received v).order ⟨u,i⟩).val := (received v).number u i

/-- The joined team's two source widths are the actual supplied lanes and
the actual private wire and program sizes at its retained global cell. -/
theorem signedReceivedRows_widths (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1))
    (i : Fin ((received v).cells u).length) :
    let c := ((received v).order ⟨u,i⟩).val
    let row := ((received v).cells u).get i
    row.supplied = supply c ∧ row.privateWires = wire c := by
  intro c row
  have sz := sourceCells_widths (charts u) home bundle u.val (routedOwnerWord arena (B).owners (packed).label v)
    (fun c => (arena).cellBank+c*(arena).cellStride) supply wire (fun _ _ _ => false) i
  have eq : row.number = c := (received v).number u i
  exact ⟨sz.1.trans (congrArg supply eq),sz.2.trans (congrArg wire eq)⟩

/-- A cell's opaque sources occur in increasing original bundle ordinal. -/
theorem signedReceivedRows_bundles (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1))
    (i : Fin ((received v).cells u).length) :
    (((received v).cells u).get i).bundles =
      (Packing.BundleDirectory.sourceRows home ((received v).order ⟨u,i⟩).val).map bundle := by
  rw [←(received v).number u i]
  exact sourceCells_bundles (charts u) home bundle u.val (routedOwnerWord arena (B).owners (packed).label v)
    (fun c => (arena).cellBank+c*(arena).cellStride) supply wire (fun _ _ _ => false) i

/-- The selected report source and the retained private checker count the
same marked-use digits on every team-local cell. -/
theorem signedReceivedRows_useCount (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1))
    (i : Fin ((received v).cells u).length) :
    ((((received v).cells u).get i).bundles.map ReportBundle.useCount).sum =
      (((Packing.BundleDirectory.sourceRows home ((received v).order ⟨u,i⟩).val).map
        (fun j => W.seedCoreBundle position code sites edges ports (bundleIdx j).2 (sourceSlot j) (boxStart j) copies)).map
          Packing.BottomReports.Bundle.useBits).sum := by
  rw [plan.signedReceivedRows_bundles p fit W position code sites edges ports table words good seeds free count pos
    num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u i]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  exact W.seedUseBundle_useBits position code sites edges ports ch gp (bundleIdx j).2 (sourceSlot j)
    (boxStart j) copies (fun _ => false)

/-- Ownership of each returned local cell in the numbered global directory. -/
theorem signedReceivedRows_owner (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1))
    (i : Fin ((received v).cells u).length) :
    (B).owners v.1 ((packed).label ((received v).order ⟨u,i⟩) (BorderVNP.Cube.Physical.chosen cube.b cube.width v.1)) = u :=
  receivedSourceRows_owner _ _ _ _ _ _ _ _ _ _ u i

/-- Readback of each original's public origin in exactly the order of the
physical description pairs. -/
theorem signedReportSources_original (j : Fin (deliveries).entries) :
    original j = (enrichedOuterHosts M leaf q).site (bundleIdx j) := rfl

/-- Common reference bank of this attained signed history, in the same
cell and native port order as its report and packet sources. -/
noncomputable def signedReportReferenceBank :=
  RoutingOutputs.NativeDemands.referenceBank net cell edge port deliveries original live gap (fun _ => rfl)

/-- The original private row is in its actual report cell, and the report
reads its opaque body from that cell's bank at the reference displacement. -/
theorem signedReportBundle_referenceSlot (j : Fin (deliveries).entries) :
    let row := (deliveries).keyPlacement
      (RoutingOutputs.NativeDemands.privatePair net cell edge port deliveries original live gap)
      (RoutingOutputs.NativeDemands.livePair net cell edge port deliveries original live gap) (.inl j)
    row.1=(home j).val ∧
      (bundle j).header.siteSlot=(arena).cellBank+row.1*(arena).cellStride+row.2 := by
  intro row
  have placed := RoutingOutputs.NativeDemands.keyPair net cell edge port deliveries original live gap (.inl j)
  have own : row.1=(home j).val := congrArg Prod.fst placed
  have disp : row.2=(RoutingOutputs.NativeDemands.destination net cell edge port deliveries original live gap (.inl j)).2 :=
    congrArg Prod.snd placed
  exact ⟨own,congrArg₂ (fun c z => (arena).cellBank+c*(arena).cellStride+z) own.symm disp.symm⟩

/-- On an actual native placement the absolute opaque pointer, local work base and
four geometry fields are precisely those of the selected signed report source. -/
theorem signedReportBundle_geometryHeader {levels ownerWidth word machineWord : ℕ} {σ : Type} [Fintype σ]
    (fields : Packing.CellAddressCircuit.Fields (B).siteRows (B).edgeRows (B).portRows cells levels ownerWidth word σ)
    (x : σ → Bool) (u : Fin (R+1)) (before placed after : ℕ → ℕ)
    (physical : Packing.CellAddressPhysical.Represents net cell charges (B).siteID edge port fields x)
    (ids : ∀ c, (fields.cells c).val=c.val)
    (room : ∀ c, guessedSize net cell c+siteSize net cell c charges+suppliedSize net cell c<2^word)
    (route : RoutingOutputs.Image fields ((B).siteID ∘ original) (port ∘ live ∘ finProdFinEquiv.symm) x (origin u) before)
    (placedRows : (RoutingOutputs.privateLayout (frame u) (origin u) (B).edgeRows cells (deliveries).entries desc gap).Image
      before (deliveries).entries placed)
    (placementRoom : (RoutingOutputs.privateLayout (frame u) (origin u) (B).edgeRows cells (deliveries).entries desc gap).Fits
      machineWord before)
    (kept : ∀ j : Fin (deliveries).entries, let raw := (RoutingOutputs.bases (origin u) (B).edgeRows cells (deliveries).entries).privatePairs
      after (raw+2*j.val)=placed (raw+2*j.val) ∧ after (raw+2*j.val+1)=placed (raw+2*j.val+1))
    (hostWord : ∀ c : Fin cells, after ((arena).hostDirectory+2*c.val+1)=(arena).cellBank+c.val*(arena).cellStride)
    (j : Fin (deliveries).entries) :
    let sh := W.frozenBundleShapes position ((fan S)^T) copies j
    let l := RoutingOutputs.privateLayout (frame u) (origin u) (B).edgeRows cells (deliveries).entries desc gap
    geometryHeader (Retains.id net) (B).siteID fields (x:=x) l after (arena).hostDirectory original j
      sh.copies sh.fine sh.incoming sh.cap = (bundle j).header := by
  exact RoutingOutputs.NativeDemands.placed_bundle_header net cell charges (B).siteID edge port deliveries original live gap
    fields x physical ids room (frame u) (origin u) (arena).hostDirectory (arena).cellBank (arena).cellStride machineWord
    before placed after (W.frozenBundleShapes position ((fan S)^T) copies) (fun _ => rfl)
    route placedRows placementRoom kept hostWord j

/-- The opaque factor body and the sidecar positions read by the report
routine are exactly the ones in this original witness's transmitted description. -/
theorem signedReportBundle_sourcePayload (j : Fin (deliveries).entries) :
    (bundle j).factors=W.seedStored position code sites edges ports ch gp (order (finProdFinEquiv.symm j).2) ∧
    (bundle j).positions=W.seedPositions position code sites edges ports (order (finProdFinEquiv.symm j).2) := ⟨rfl,rfl⟩

/-- The declared minimum and cube capacity tested on this history's true
native receivers and original field widths, including zero-width entries. -/
def signedBroadcastAllowed (raw : RawBroadcast arena) : Prop :=
  broadcastAllowed R (TeamScales.exterior ξ r (k+1)) (packed).blocks cube.b cube.copies cube.h
    (packed).label recv weight raw

/-- Every routed assignment reconstructed on the selected signed directory
broadcasts an admissible header on the actual profile's calibrated row list. -/
theorem signedBroadcastAllowed_honest (admitted : plan.AdmitsSignedPackets cube α ξ count calibrated)
    (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) :
    broadcastAllowed R (TeamScales.exterior ξ r (k+1)) (packed).blocks cube.b cube.copies cube.h
      (packed).label recv weight (routeBroadcast arena (B).owners v).val := by
  exact admitted G₀ lit order position W code sites edges ports table words good hd hp q number gap v.1

/-- Width of the routing-table census installed by the signed owner scanner.
The data part is the native private and live demand list on this history.
Every unordered pair of distinct labels contributes one further slot. -/
noncomputable def signedNativeReportEntries : ℕ :=
  (demandRows).length+(BorderVNP.Cube.alphabet α (k+1)).choose 2

local notation3 (prettyPrint := false) "teamReportProposals" =>
  (v : (B).Route cube.width) × ((u : Fin (R+1)) → ReportAssignments ((received v.val).cells u))

/-- Reading the pinned route and the report from the chosen history gives the
original selection together with its actual ordered reports at every team. -/
noncomputable def signedPinnedReportProposals : (sources).Proposals ≃ teamReportProposals := by
  dsimp only [signedReportSources,signedReceivedRows,CoreDirectory.Route]
  exact routedReportProposals arena net (B).cell (B).owners (B).slot (packed).label charts home bundle supply wire

local notation3 (prettyPrint := false) "reportProposals" => plan.signedPinnedReportProposals p fit W position code sites edges ports
  table words good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin

/-- The inverse at a receiving team preserves the entire layout, cell list
and report assignment on that history. -/
theorem signedPinnedReportProposals_key (z : teamReportProposals) (u : Fin (R+1)) :
    let before := (reportProposals).symm z
    (⟨_,_,before.2 u⟩ : (l : ReportLayout) × (cs : List (ReportCell l)) × ReportAssignments cs) =
      ⟨_,_,z.2 u⟩ := by
  dsimp only [signedPinnedReportProposals]
  exact routedReportProposals_key arena net (B).cell (B).owners (B).slot (packed).label charts home bundle supply wire z u

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
