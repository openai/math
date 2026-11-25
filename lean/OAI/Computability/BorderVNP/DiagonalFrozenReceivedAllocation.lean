import OAI.Computability.BorderVNP.DiagonalActualSourceCellAllocation
import OAI.Computability.BorderVNP.DiagonalSelectedReportBounds
import OAI.Computability.BorderVNP.DiagonalSelectedReportMarkRoom
import OAI.Computability.BorderVNP.DiagonalReceivedFrameAllocation

/-! # Allocating the frozen signed report cells at the actual prefix frame -/

namespace OAI
namespace Computability
namespace BorderVNP

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
    {ns ne np : ℕ}
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
variable (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
local notation3 (prettyPrint := false) "code" => (ParseTable.numberedLabelEquiv ord k s).toEmbedding.trans Fin.valEmbedding
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

local notation3 (prettyPrint := false) "deliveries" => freeDirectory R r ((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))
  link tiles seedBlock ((fan S)^T*tiles) desc
variable {extra exponent dlog Q A B₀ tick : ℕ} {sc : EpochScales S (cube.pred+1) extra}
    (sched : JointSchedule.{0} sc (exponent+1) dlog Q A B₀ tick) (initial : ProcessorSlots.StartupArena)
    (H reserve ceiling outputs field : ℕ) (dirs : SignedTaskArena.GeometryDirectories)
local notation3 (prettyPrint := false) "fullTask" => sched.frozenSignedTask cube (k+1) k s H initial deliveries reserve ceiling outputs field dirs
local notation3 (prettyPrint := false) "parameters" => (fullTask).p
local notation3 (prettyPrint := false) "gap" => (fullTask).p.privateGap
local notation3 (prettyPrint := false) "arenaBase" =>
  GeometryAdvice.Allocation.stop (initial.next+7*(deliveries).candidates) reserve ceiling outputs field (sched.physical.word (k+1))
local notation3 (prettyPrint := false) "profileBits" => reserve
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

local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "task" => (SignedTaskArena.Layout.mk arena (cube.cubeID e) parameters)
local notation3 (prettyPrint := false) "frame" => fun _ : Fin (R+1) => initial.frame
local notation3 (prettyPrint := false) "origin" => fun _ : Fin (R+1) =>
  GeometryAdvice.Allocation.dest (initial.next+7*(deliveries).candidates) reserve ceiling outputs field
local notation3 (prettyPrint := false) "charts" => fun u : Fin (R+1) =>
  reportLayout (task).before (task).after (frame u)
    (RoutingOutputs.controlsBase (origin u) (arena).cables cells (deliveries).entries ((R+1)*tiles))
    (parameters).parameters (parameters).siteWidth (parameters).bodyCap (arena).stop
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

local notation3 (prettyPrint := false) "core" => fun j : Fin (deliveries).entries =>
  W.seedCoreBundle position code sites edges ports ((bundleIdx j).2) (sourceSlot j) (boxStart j) copies
local notation3 (prettyPrint := false) "received" => plan.signedReceivedRows p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin

open CellSparse
open Packing.InheritedBank Packing.BottomReports


local notation3 (prettyPrint := false) "ctl" => RoutingOutputs.controlsBase ((origin) 0) (arena).cables
  cells (deliveries).entries ((R+1)*tiles)
local notation3 (prettyPrint := false) "report(" j ")" =>
  reportLayout (task).before (task).after j ctl (parameters).parameters (parameters).siteWidth
    (parameters).bodyCap (arena).stop

/-- Each selected source cell is allocated at its native receive-bank address,
with the exact header, report tags, unary uses, and finite row ordering required
by the positive suffix. The cut may use any actual public register with this
startup frame, and it retains the same original mark and bank bounds. -/
theorem signedReceivedRows_frozenAllocation {w : ℕ} (hm : 0 < m) (hr : 1≤r) (short : seedBlock≤link)
    (gpos : 0 < (parameters).report.gadgets) (fits : ∀ z, num (pos z) ≤ (parameters).report.gadgets-1)
    (length : r=stretch sched.ρ (k+1)) (indexDepth : CoverScale.initialDepth (Cube D) r (k+1)=d+1)
    (history : T=epochs sc.τ (k+1)) (teams : R=sched.physical.teamsPred (k+1))
    (labelFit : Branch.pairedTableParameters (k+1) s ≤ 2^w) (wordFit : logWidth r (k+1) ≤ w)
    (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1)) (axis : Fin (cube.pred+1))
    (frameWord : ℕ) (installed : initial.frame=frameWord) {level limit : ℕ} :
    let size := S.publicProgramFactor^T*mass
    let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    let Z := signedMarkedLimit copies seedCap coeff size
    SignedReceivedScale level (TeamScales.width (k+1) (1/4)) (parameters).report.countWidth (parameters).report.gadgets size
      (max (tableLimit e) (max 8 seedCap)) Z limit →
    let rc := (received v).atLayout (congrArg (fun j => report(j)) installed)
    ReportAllocation (task).before (task).after ((arena).cellWriter frameWord ctl axis) (report(frameWord))
      (rc.cells u) (task).after.reportCursor ∧
    ∀ c ∈ rc.cells u, ∀ b ∈ c.bundles, ∀ g ∈ b.positions, g.parameter<2^w ∧ g.place<w := by
  intro size coeff Z scaleRoom rc
  have cEq : cells=CoverScale.sites (Cube D) (depth S (d+1) T) := by
    simpa only [CoverScale.sites,Fintype.card_fin] using (Fintype.card_congr number).symm
  have cellsFit : cells≤(parameters).report.cells := by
    change cells≤CoverScale.sites (Cube D) (depth S (CoverScale.initialDepth (Cube D) (stretch sched.ρ (k+1)) (k+1)) (epochs sc.τ (k+1)))
    rw [←length,indexDepth,←history,cEq]
  have bundlesFit : (deliveries).entries≤(parameters).report.bundles := by
    change (fan S)^T*tiles ≤ (epochCopies S)^(epochs sc.τ (k+1))*CoverScale.sites (Cube D) (CoverScale.initialDepth (Cube D) (stretch sched.ρ (k+1)) (k+1))
    rw [←length,indexDepth,←history,←seedPortCount (D:=D) d]; rfl
  have rooms := plan.signedReportBundle_frozen_room p fit W position code sites edges ports table words good seeds free
    count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits sched initial H reserve ceiling outputs
    field dirs length indexDepth history teams
  have receive := plan.signedReceivedRows_supply_stride p fit W position code sites edges ports table words good seeds free
    count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin hm hr short gpos fits v scaleRoom
  have reservation : ∀ c : Fin cells, supply c.val+
      ((parameters).report.gadgets*(parameters).report.countWidth+weightedCopies ((BundleDirectory.sourceRows home c.val).map bundle)) ≤
      (arena).cellStride := by
    intro c
    have widthEq := (FinalReports.bank_sizes net (B).cell (fun z => ((B).programs z).program) c).2.2
    apply (Nat.add_le_add_right widthEq.le _).trans
    exact receive c
  have beforeBank : initial.frame+96 ≤ (arena).cellBank := by
    apply le_trans _ (task).open_table_order.1
    change initial.frame+96 ≤ arenaBase
    dsimp only [GeometryAdvice.Allocation.stop,GeometryAdvice.Allocation.packed,GeometryAdvice.Allocation.dense,
      GeometryAdvice.Allocation.dest,GeometryAdvice.Allocation.temp,ProcessorSlots.StartupArena.next,
      ProcessorSlots.StartupArena.hbase,ProcessorSlots.StartupArena.ibase,ProcessorSlots.StartupArena.broadcastBase,
      ProcessorSlots.StartupArena.dense]
    omega
  have allocated := (task).sourceCellsAllocation (control:=ctl) home bundle
    (fun c => (B).owners v.1 ((packed).label c (BorderVNP.Cube.Physical.chosen cube.b cube.width v.1)))
    (routedOwnerWord arena (B).owners (packed).label v) (routedOwnerWord_at arena (B).owners (packed).label v)
    supply wire (fun _ _ _ => false) u axis beforeBank cellsFit bundlesFit reservation rooms.1 rooms.2.1 rooms.2.2.le
  exact ⟨(received v).allocationAtFrame task ctl (parameters).siteWidth (parameters).bodyCap installed u ctl axis allocated,
    (received v).marksAtFrame task ctl (parameters).siteWidth (parameters).bodyCap installed u
      (plan.signedReceivedRows_markRoom p fit W position sites edges ports table words good seeds free count pos num hp q
        cube α ξ calibrated lit hd number parameters ord arenaBase profileBits frame origin labelFit hr wordFit v u)⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
