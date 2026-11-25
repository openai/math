import OAI.Computability.BorderVNP.DiagonalSelectedReportIntervals
import OAI.Computability.BorderVNP.DiagonalSelectedReportBounds
import OAI.Computability.BorderVNP.DiagonalFrozenIntervalBudget
import OAI.Computability.BorderVNP.DiagonalOneTeamOpenedReports
import OAI.Computability.BorderVNP.DiagonalSignedProfileReportRows
import OAI.Computability.BorderVNP.DiagonalSameReportIntervals
import OAI.Computability.BorderVNP.DiagonalLocalReportAllocation

/-! # Physical report room on one opened selected directory before its first local report -/

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

variable {D m : ℕ} [NeZero D] {K Gadget : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
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
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := word₀) budget
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "M" => (C).machine
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words) good)
      plan.compiled.machine.epoch T).Index)
local notation3 (prettyPrint := false) "lastState" => ((packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).term q).val
local notation3 (prettyPrint := false) "net" => EnrichedTape.network (pins := pins) p fit position free count M leaf rfl q

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


local notation3 (prettyPrint := false) "received" =>
  plan.signedReceivedRows p fit W position code sites edges ports table words good seeds free count pos num hp q cube α ξ
    calibrated lit hd number parameters arenaBase profileBits frame origin

open DiagonalTallyCellReports ReportDirectory
open BorderVNP.Cube.Physical.NativeAssignments
open CellMacro.Generator

open RoutingISA.Evaluator.SignedPrep RoutingISA.SignedTaskArena FiniteEvaluator DiagonalTallyAllocation
attribute [local irreducible] UniversalMachine.programPrefix Nat.clog
local notation3 (prettyPrint := false) "tbl" uu => RoutingOutputs.bases (origin uu) (arena).cables cells (deliveries).entries
local notation3 (prettyPrint := false) "issuedOrigin" =>
  (bundleIdx).trans (Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2)))
local notation3 (prettyPrint := false) "hdr" => fun j : Fin (deliveries).entries =>
  W.seedUseHeader position ((issuedOrigin j).2) (sourceSlot j) (boxStart j) copies
local notation3 (prettyPrint := false) "body" => fun j : Fin (deliveries).entries =>
  W.seedStored position code sites edges ports ch gp ((issuedOrigin j).2)
local notation3 (prettyPrint := false) "factors" => fun j : Fin (deliveries).entries =>
  W.nativeFactors position code sites edges ports ((issuedOrigin j).2)
local notation3 (prettyPrint := false) "opening(" vv "," uu "," ww ")" =>
  (let ar := task
   let hosts : Fin (deliveries).entries → Fin ar.cube.cells := home
   SingleOpenedReport (R:=R) (J:=(deliveries).entries) ar uu (frame uu) (origin uu) ((R+1)*tiles) hosts hdr body factors
     (fun c => if h : c<cells then (plan.signedGroupOwner p fit W position code sites edges ports table words
       good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters vv ⟨c,h⟩).val else 0)
     supply wire ww)

/-- The raw compact directory of the returning team and the selected
source rows contain the same banks, supply and wire widths, original
bundle positions and six-word headers on this routed choice. -/
theorem signedDirectory_source_on_return (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1)) {w : ℕ}
    (opened : opening(v,u,w)) :
    SameReportCells opened.cells ((received v).cells u) := opened.same_source

/-- The selected report intervals and word bounds therefore apply before
the team's report program reads its first private choice bit. -/
theorem signedDirectory_intervals_on_return (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1)) {w : ℕ}
    (opened : opening(v,u,w))
    {J : Type} [Fintype J] (ix : J ↪ (net).Site) (boxes : J → Packing.BottomReports.Bundle) (ids : Fin cells → List J)
    (owner : Fin (B).siteRows → ℕ) {privateMax exteriorMax z high boundTable boundRows digits : ℕ}
    (bound : ReceivedBounds (received v) net (B).cell (B).siteID owner (B).programs ix boxes ids
       privateMax exteriorMax z high boundTable boundRows digits)
    (hr : 1≤r) (hm : privateMax ≤ TeamScales.width (k+1) (1/5)) (he : exteriorMax ≤ TeamScales.width (k+1) (1/4))
    (word : 60*logWidth r (k+1) ≤ w) (reportGap : parameters.privateGap=(k+1)^2)
    (capacity : ℕ) (supplyLimit : ∀ c : Fin cells,suppliedSize net (B).cell c≤capacity)
    (storage : ∀ (f : Fin (deliveries).entries → Fin cells) (c : Fin cells) (g x : ℕ), g≤(k+1)^2 → x≤capacity →
      x+g+(∑ j, if f j=c then (deliveries).description else 0)≤3*(r*(k+1))^2+1) :
    SiteIntervals opened.cells (deliveries).description (arena).cellStride ∧
      ∀ c∈opened.cells, c.privateWires+c.supplied+c.tailWidth<2^w := by
  have same := plan.signedDirectory_source_on_return p fit W position code sites edges ports table words
    good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin
    v u opened
  have physicalBounds := plan.signedReportIntervals p fit W position code sites edges ports table words
    good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin
    v u ix boxes ids owner bound hr hm he word reportGap capacity supplyLimit storage
  exact same.physicalRoom physicalBounds.1 physicalBounds.2

open CellSparse Packing.InheritedBank
local notation3 (prettyPrint := false) "coreBundles" => fun j : Fin (deliveries).entries =>
  W.seedCoreBundle position code sites edges ports ((bundleIdx j).2) (sourceSlot j) (boxStart j) copies

/-- The published scale already bounds the selected source for each returned
route. No independently chosen team, cell assignment or accepted report
is needed to apply these bounds to the current directory. -/
theorem signedDirectory_intervals_at_scale (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1)) {w : ℕ}
    (opened : opening(v,u,w))
    (positive : 0 < m) (batch : 1≤r) (short : seedBlock ≤ link)
    (gadgets : 0<parameters.report.gadgets) (dictionary : ∀ z, num (pos z) ≤ parameters.report.gadgets-1)
    (word : 60*logWidth r (k+1) ≤ w) (reportGap : parameters.privateGap=(k+1)^2) {limit : ℕ}
    (capacity : ℕ) (supplyLimit : ∀ c : Fin cells,suppliedSize net (B).cell c≤capacity)
    (storage : ∀ (f : Fin (deliveries).entries → Fin cells) (c : Fin cells) (g x : ℕ), g≤(k+1)^2 → x≤capacity →
      x+g+(∑ j, if f j=c then (deliveries).description else 0)≤3*(r*(k+1))^2+1) :
    let size := S.publicProgramFactor^T*mass
    let coeff := (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
    SignedReceivedScale (TeamScales.width (k+1) (1/5)) (TeamScales.width (k+1) (1/4)) parameters.report.countWidth
      parameters.report.gadgets size (max (tableLimit e) (max 8 seedCap)) (signedMarkedLimit copies seedCap coeff size) limit →
    SiteIntervals opened.cells (deliveries).description (arena).cellStride ∧
      ∀ c∈opened.cells, c.privateWires+c.supplied+c.tailWidth<2^w := by
  intro size coeff scale
  let owner := fun i : Fin (B).siteRows => if h : ∃ a, (B).siteID a=i then ((B).cell h.choose).val else 0
  have agrees (a) : owner ((B).siteID a)=((B).cell a).val := by
    have present : ∃ z, (B).siteID z=(B).siteID a := ⟨a,rfl⟩
    rw [show owner ((B).siteID a)=((B).cell present.choose).val by dsimp only [owner]; rw [dite_eq_left present]]
    exact congrArg (fun z => ((B).cell z).val) ((B).siteID.injective present.choose_spec)
  have bound := plan.signedReceivedRows_bounds p fit W position code sites edges ports table words
    good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin
    positive batch short gadgets dictionary v owner agrees scale
  exact plan.signedDirectory_intervals_on_return p fit W position code sites edges ports table words
    good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin
    v u opened original coreBundles
    (fun c => BundleDirectory.sourceRows home c.val) owner bound batch le_rfl le_rfl word reportGap capacity supplyLimit storage

/-- The single-threshold frozen report budget bounds this local execution
on every public seed word and routed declaration. The byte and storage
bounds come from the selected site's real directory and packet sizes. -/
theorem signedDirectory_intervals_at_frozen_budget (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1)) {w : ℕ}
    (opened : opening(v,u,w)) {exponent : ℕ}
    (positive : 0 < m) (loads : plan.SewnCellLoads count link)
    (paid : FrozenIntervalBudget S (k+1) r d T copies header link w exponent parameters)
    (dictionary : ∀ z, num (pos z) ≤ parameters.report.gadgets-1) :
    SiteIntervals opened.cells (deliveries).description (arena).cellStride ∧
      ∀ c∈opened.cells, c.privateWires+c.supplied+c.tailWidth<2^w := by
  have supplied := plan.supplied_width_on_source_words p fit W position code sites edges ports table words good
    free count loads q number
  exact plan.signedDirectory_intervals_at_scale p fit W position code sites edges ports table words
    good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin
    v u opened positive paid.batch paid.short paid.gadgets dictionary paid.word paid.gap
    (TeamScales.width (k+1) (1/5)) supplied (fun f c g x hg hx => paid.storage f c g x hg hx) paid.scale

open VPVNP.BurstRAM VPVNP.VerifierNetwork Packing.CellAddressCircuit Packing.CellAddressPhysical
open RoutingOutputs GeometryFrameEncoding ParseBatchSort DiagonalResidueRAM

/-- The two width columns required on the local original prefix are the words
actually published after private placement on the selected packet. -/
theorem signedDirectory_publishedWidths (u : Fin (R+1)) {levels ownerWidth field restWords next w₀ : ℕ} {σ : Type} [Fintype σ]
    (edgeID : (net).Edge ↪ Fin (arena).cables)
    (fields : Fields (B).siteRows (arena).cables (B).portRows cells levels ownerWidth field σ)
    {x : σ → Bool} {profile placedMem : Memory w₀} (pp lp : ℕ → ℕ × ℕ)
    (image : RoutingOutputs.Image fields ((B).siteID ∘ original) (port ∘ live ∘ finProdFinEquiv.symm) x
      (origin u) (readings profile))
    (physical : Packing.CellAddressPhysical.Represents net (B).cell charges (B).siteID edgeID port fields x)
    (names : ∀ c, (fields.cells c).val=c.val)
    (fits : ∀ c, guessedSize net (B).cell c+siteSize net (B).cell c charges+suppliedSize net (B).cell c<2^field)
    (placement : (privateLayout (frame u) (origin u) (arena).cables cells (deliveries).entries desc gap).Image
      (readings profile) (deliveries).entries (readings placedMem))
    (below : frame u+112≤next) (reserved : next+7*(deliveries).candidates≤origin u)
    (rest : Frame σ (Outputs restWords field)) (bitsFit : field≤w₀)
    (serialized : ∀ i : Fin ((cells+((deliveries).entries+cells))+restWords),
      profile (origin u+(arena).cables*3+RoutingOutputs.count (arena).cables cells (deliveries).entries ((R+1)*tiles)+i.val)=
        word w₀ (value fun j => (withPrivateViews fields ((B).siteID ∘ original) rest).eval x (.inl (i,j)))) :
    let written := readings (Directory.ISA.publish placedMem (frame u) next ((deliveries).directory pp lp))
    ∀ c : Fin cells, written ((tbl u).ends+2*(arena).cables+c.val)=supply c.val ∧
      written ((tbl u).livePairs+2*((R+1)*tiles)+c.val)=wire c.val := by
  intro published c
  have read := image.published_reportWidths net (B).cell charges (B).siteID edgeID port fields deliveries original
    (live ∘ finProdFinEquiv.symm) pp lp physical names fits placement below reserved rest bitsFit serialized c
  obtain ⟨guessed,privateWires,supplied⟩ := Merged.CellKey.bankSizes net (B).cell Fin.valEmbedding c (fun t => ((B).programs t).program)
  exact ⟨read.1.trans supplied.symm,read.2.trans (congrArg₂ Nat.add guessed privateWires).symm⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
