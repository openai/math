import OAI.Computability.BorderVNP.DiagonalLocalSelectedReportIntervals

/-! # Source-side report widths and intervals for the actual replay bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open Packing.BottomReports

/-- The report tail uses the number of real copies, independently of the
bits read from their banks. Its quarter-power bound pays the square gap. -/
theorem physicalBankCharge {J : Type} (rows : List J) (header : J → BundleHeader)
    (body factors : J → List CellSparse.Factor) (bank : J → ℕ → Bool) (k g w supplied : ℕ)
    (bound : supplied+(g*w+weightedCopies (rows.map fun j =>
      physicalBundle (header j) (body j) (factors j) (fun _ => false))) ≤ TeamScales.width (k+1) (1/4)) :
    g*w+weightedCopies (rows.map fun j => physicalBundle (header j) (body j) (factors j) (bank j)) ≤ (k+1)^2 := by
  have eq : weightedCopies (rows.map fun j => physicalBundle (header j) (body j) (factors j) (bank j)) =
      weightedCopies (rows.map fun j => physicalBundle (header j) (body j) (factors j) (fun _ => false)) := by
    simp only [weightedCopies,List.map_map,Function.comp_def]
    rfl
  have quarter : TeamScales.width (k+1) (1/4) ≤ k+1 := Nat.floor_le_of_le (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k) : (1:ℝ) ≤ ((k+1:ℕ):ℝ)) (by norm_num : (1/4:ℝ) ≤ 1))
  exact (Nat.add_le_add_left eq.le _).trans ((Nat.le_add_left _ _).trans
    (bound.trans (quarter.trans (Nat.le_self_pow (by decide) _))))

end DiagonalTallyCellReports

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

local notation3 (prettyPrint := false) "atReport(" f ")" => f
  (D:=D) (m:=m) (K:=K) (Gadget:=Gadget) (e:=e) (S:=S) (R:=R) (r:=r) (pins:=pins)
  (link:=link) (k:=k) (d:=d) (a:=a) (regs:=regs) (rw:=rw) (ec:=ec) (width:=width) (s:=s)
  (copies:=copies) (T:=T) (header:=header) (work:=work) (order:=order) (ns:=ns) (ne:=ne) (np:=np)
  (F:=F) (cells:=cells)
local notation3 (prettyPrint := false) "B" => atReport(signedCoreDirectory) plan p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number gap

variable (arenaBase profileBits : ℕ)
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "home" => fun j : Fin (deliveries).entries => (B).cell (original j)
local notation3 (prettyPrint := false) "charges" => placedSize net (B).programs
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

open Packing.BottomReports CellSparse DiagonalTallyCellReports
open scoped BigOperators
attribute [local irreducible] Nat.clog UniversalMachine.programPrefix TeamTapeInput.digits VPVNP.BurstRAM.wordBits
set_option autoImplicit false
local notation3 (prettyPrint := false) "hdr" => fun j : Fin (deliveries).entries =>
  W.seedUseHeader position ((bundleIdx j).2) (sourceSlot j) (boxStart j) copies
local notation3 (prettyPrint := false) "stored" => fun j : Fin (deliveries).entries =>
  W.seedStored position code sites edges ports ch gp ((bundleIdx j).2)
local notation3 (prettyPrint := false) "nativeFactors" => fun j : Fin (deliveries).entries =>
  W.nativeFactors position code sites edges ports ((bundleIdx j).2)

local notation3 (prettyPrint := false) "bankBundle(" bank "," j ")" =>
  physicalBundle (hdr (j)) (stored (j)) (nativeFactors (j)) ((bank) (j))
local notation3 (prettyPrint := false) "core" => fun j : Fin (deliveries).entries =>
  W.seedCoreBundle position code sites edges ports ((bundleIdx j).2) (sourceSlot j) (boxStart j) copies

/-- The bundle constructed by the report continuation reads the selected
bank at the genuine work base of each original copy. -/
theorem signedReplay_bundle (bank : Fin (deliveries).entries → ℕ → Bool) (j : Fin (deliveries).entries) :
    bankBundle(bank,j) =
      W.seedUseBundle position code sites edges ports ch gp ((bundleIdx j).2) (sourceSlot j) (boxStart j)
        copies (bank j) := rfl

/-- The frozen task's supplement, mark and use reserves hold on arbitrary
returned banks, including different banks on each processing team. -/
theorem signedReplay_inventory {extra exponent dlog Q A B₀ depthIndex H reserve ceiling outputs field : ℕ}
    {scale : EpochScales S (cube.pred+1) extra}
    (sched : JointSchedule.{0} scale (exponent+1) dlog Q A B₀ depthIndex)
    (initial : TeamContraction.ProcessorSlots.StartupArena) (dirs : SignedTaskArena.GeometryDirectories)
    (length : r=stretch sched.ρ (k+1)) (chart : CoverScale.initialDepth (Cube D) r (k+1)=d+1)
    (history : T=epochs scale.τ (k+1)) (team : R=sched.physical.teamsPred (k+1))
    (bank : Fin (R+1) → Fin (deliveries).entries → ℕ → Bool) (u : Fin (R+1)) :
    let sa := sched.frozenSignedTask cube (k+1) k s H initial deliveries reserve ceiling outputs field dirs
    (∀ c : Fin cells, supplementWords ((BundleDirectory.sourceRows home c.val).map (fun j => bankBundle(bank u,j))) ≤
      sa.p.report.supplementStride) ∧
      (∀ j, (bankBundle(bank u,j)).positions.length ≤ sa.p.report.marked) ∧
      (∑ j, (bankBundle(bank u,j)).useCount) = sa.p.report.uses := by
  let orig := (bundleIdx).trans (Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2)))
  exact sched.frozenReportBundle_room cube (copies:=copies) W position orig code sites edges ports ch gp
    sourceSlot boxStart (bank u) initial deliveries H reserve ceiling outputs field dirs length chart
    (by rw [history]; rfl) (count.trans (congrArg (·+1) team)) home

variable (frame origin : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "reportSource" => atReport(signedReportSources) plan p fit W position code sites edges ports table
  words good seeds free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin

section
attribute [local irreducible] BundleDirectory.sourceRows Finset.univ
include frame origin in
/-- The private report gap covers the exact unary uses of this original
directory on every possible returned bank. -/
theorem signedReplay_charge {word exponent : ℕ} (hm : 0 < m)
    (paid : FrozenIntervalBudget S (k+1) r d T copies header link word exponent parameters)
    (dictionary : ∀ t, num (pos t) ≤ parameters.report.gadgets-1)
    (v : Routed (b:=cube.b) (s:=cube.width) (B).owners)
    (bank : Fin (R+1) → Fin (deliveries).entries → ℕ → Bool) (u : Fin (R+1)) (c : Fin cells) :
    parameters.report.gadgets*parameters.report.countWidth+
      weightedCopies ((BundleDirectory.sourceRows home c.val).map (fun j => bankBundle(bank u,j))) ≤ parameters.privateGap := by
  have size := atReport(signedReceivedRows_supply) (level:=TeamScales.width (k+1) (1/5)) (limit:=(logWidth r (k+1)+1)^exponent) plan p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin hm paid.batch paid.short
    paid.gadgets dictionary v paid.scale c
  exact (physicalBankCharge (BundleDirectory.sourceRows home c.val) hdr stored nativeFactors (bank u) k
    parameters.report.gadgets parameters.report.countWidth (suppliedSize net (B).cell c) size).trans paid.gap.symm.le

end

/-- Supplied wires and the report gap fit in the physical receive bank of
every cell at the same length that pays for the original descriptions. -/
theorem signedReplay_allocation {word exponent : ℕ} (loads : plan.SewnCellLoads count link)
    (paid : FrozenIntervalBudget S (k+1) r d T copies header link word exponent parameters) (c : Fin cells) :
    suppliedSize net (B).cell c+parameters.privateGap ≤ (arena).cellStride := by
  have supplied := plan.supplied_width_on_source_words p fit W position code sites edges ports table words good
    free count loads q number
  have cap := paid.storage (fun _ => c) c parameters.privateGap (suppliedSize net (B).cell c) paid.gap.le (supplied c)
  exact (Nat.le_add_right _ _).trans cap

/-- Typed original report rows and every original descriptor interval fit
the selected physical word and stride, before any private use bits are read. -/
theorem signedReplay_sourceRoom {word exponent : ℕ} (hm : 0 < m) (loads : plan.SewnCellLoads count link)
    (paid : FrozenIntervalBudget S (k+1) r d T copies header link word exponent parameters)
    (dictionary : ∀ t, num (pos t) ≤ parameters.report.gadgets-1)
    (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1)) :
    SiteIntervals ((reportSource).cells v u) (deliveries).description (arena).cellStride ∧
      ∀ c∈(reportSource).cells v u, c.privateWires+c.supplied+c.tailWidth<2^word := by
  let owner := fun i : Fin (B).siteRows => if h : ∃ a, (B).siteID a=i then ((B).cell h.choose).val else 0
  have agrees (a) : owner ((B).siteID a)=((B).cell a).val := by
    have present : ∃ z, (B).siteID z=(B).siteID a := ⟨a,rfl⟩
    rw [show owner ((B).siteID a)=((B).cell present.choose).val by dsimp only [owner]; rw [dite_eq_left present]]
    exact congrArg (fun z => ((B).cell z).val) ((B).siteID.injective present.choose_spec)
  have bound := plan.signedReceivedRows_bounds p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin
    hm paid.batch paid.short paid.gadgets dictionary v owner agrees paid.scale
  have supplied := plan.supplied_width_on_source_words p fit W position code sites edges ports table words good free count loads q number
  exact plan.signedReportIntervals p fit W position code sites edges ports table words good seeds free count pos num hp q
    cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u original core
    (fun c => BundleDirectory.sourceRows home c.val) owner bound paid.batch le_rfl le_rfl paid.word paid.gap
    (TeamScales.width (k+1) (1/5)) supplied (fun f c g x hg hx => paid.storage f c g x hg hx)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
