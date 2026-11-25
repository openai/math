import OAI.Computability.BorderVNP.DiagonalReplayReportStages
import OAI.Computability.BorderVNP.DiagonalSignedReplayReportSources
import OAI.Computability.BorderVNP.PackedReportCableTransport
import OAI.Computability.BorderVNP.DiagonalPrefixFinishCalibration

/-! # The selected replay's native report capacity at the original frozen layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

/-- The allocated descriptor base and parameter count are readable as machine words
whenever the end of the actual residue reader fits. -/
theorem Layout.reportCapacityAddresses (t : Layout) {w a k l : ℕ}
    (fit : t.endAddress w a k l < 2^w) : t.after.descriptors < 2^w ∧ t.p.parameters < 2^w := by
  have localEnd : t.after.localBase ≤ t.endAddress w a k l := by
    dsimp only [Layout.endAddress,Layout.entry,DiagonalResidueRAM.gateBase,Layout.valuation,Layout.tallyBits]
    omega
  have address : t.after.descriptors ≤ t.after.localBase := by
    unfold DiagonalTallyAllocation.AfterTasks.localBase DiagonalTallyAllocation.AfterTasks.fresh
    omega
  exact ⟨address.trans_lt (localEnd.trans_lt fit),
    (Nat.le_add_right t.p.parameters t.p.report.gadgets).trans_lt (t.finish_word_room fit).2.1⟩

end RoutingISA.SignedTaskArena

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

open RoutingISA.Transmission RoutingISA.LocalRow TeamContraction.JointHeader VPVNP.BurstRAM CellAddressPhysical CellAddressCircuit
open BorderVNP.Cube
local notation3 (prettyPrint := false) "task" => SignedTaskArena.Layout.mk arena (cube.cubeID e) parameters
local notation3 (prettyPrint := false) "allRows" => calibrated G₀ lit order position W code sites edges ports table words good
local notation3 (prettyPrint := false) "demandRows" => RoutingOutputs.NativeDemands.rows net cell edge port deliveries original live gap
local notation3 (prettyPrint := false) "recv" => RoutingOutputs.NativeDemands.receiver net cell edge port deliveries original live gap (allRows).choose
local notation3 (prettyPrint := false) "weight" => fun i : Fin (demandRows).length => (demandRows)[i.val].width
local notation3 (prettyPrint := false) "decl(" w ")" => Prod.mk
  (Fin.ofNat ((arena).n+1) (readCode ((arena).n+1) (w).1))
  (fun (a : Sym2 (Fin (arena).header.d)) (i : Fin ((arena).n+1)) =>
    readCode ((arena).header.cap+1) ((w).2 a i))
local notation3 (prettyPrint := false) "reportEdgeEq" =>
  (atReport(signedReportArena_cables) plan p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits).symm
local notation3 (prettyPrint := false) "selected(" f ")" =>
  atReport(f) plan p fit W position code sites edges ports table words good seeds free count pos num hp q cube α ξ
      calibrated lit hd number parameters arenaBase profileBits

/-- The selected history's charge, supplement, mark and use counts fit for any bank assignment.
The source intervals apply to every later routed selector, while the current selector
supplies the selected schedule's charged gap. -/
noncomputable def signedCandidateReportCapacity
    {mw cb lb polyWord X : ℕ} {σ : Type}
    {pp lp : ℕ → ℕ × ℕ} {representative : ℕ → Fin (R+1)} {group : Fin (arena).header.d → Fin (R+1)}
    {initialBase receiving : ℕ} {pinSites : Fin (R+1) → Pins.Layout}
    {inputFields : (u : Fin (R+1)) → Pins.ProcessorFields (pinSites u)}
    {broadcastFrame : Fin (R+1) → BroadcastFrame} {guess : Fin (R+1) → ℕ → Bool}
    {pub : Fin (R+1) → Arg → Word mw} {mac : Fin (R+1) → TeamOpcode.Macros mw 8}
    {reg : Fin (R+1) → Bank mw} {mem : Fin (R+1) → Memory mw}
    {I : Type*} [Fintype I] {resides : I → Fin cells} {keyID : I ↪ ℕ} {sizes : I → ℕ}
    (raw : Broadcast (arena).n (arena).header.d (arena).header.cap)
    (site : ∀ u, CandidateSite (X:=X) arena deliveries pp lp raw representative (decl(raw)) group initialBase receiving
      (pinSites u) (inputFields u) (broadcastFrame u) (guess u) (pub u) (mac u) (reg u) (mem u)
      resides keyID sizes net cell recv weight)
    (origin : Fin (R+1) → ℕ) (geom : Fields (B).siteRows (B).edgeRows (B).portRows cells cb lb polyWord σ)
    (input : Fin (R+1) → σ → Bool) (bank : Fin (R+1) → Fin (deliveries).entries → ℕ → Bool)
    {extra exponent budgetExp dlog Q A B₀ depthIndex H reserve ceiling outputs field : ℕ}
    {scale : EpochScales S (cube.pred+1) extra}
    (sched : JointSchedule.{0} scale (exponent+1) dlog Q A B₀ depthIndex)
    (initial : TeamContraction.ProcessorSlots.StartupArena) (dirs : SignedTaskArena.GeometryDirectories)
    (length : r=stretch sched.ρ (k+1)) (chart : CoverScale.initialDepth (Cube D) r (k+1)=d+1)
    (history : T=epochs scale.τ (k+1)) (team : R=sched.physical.teamsPred (k+1))
    (sameParameters : parameters =
      (sched.frozenSignedTask cube (k+1) k s H initial deliveries reserve ceiling outputs field dirs).p)
    (hm : 0 < «m») (loads : plan.SewnCellLoads count link)
    (paid : FrozenIntervalBudget S (k+1) r d T copies header link mw budgetExp parameters)
    (dictionary : ∀ t, num (pos t) ≤ parameters.report.gadgets-1)
    (v : Routed (b:=cube.b) (s:=cube.width) (B).owners)
    (inRange : declarationInRange raw)
    (geometryRep : ∀ u, Packing.CellAddressPhysical.Represents net cell charges (B).siteID (B).edgeID (B).portID geom (input u))
    (codes : ∀ c, (geom.cells c).val=c.val)
    (fieldWidths : ∀ c, guessedSize net cell c+siteSize net cell c charges+suppliedSize net cell c<2^polyWord)
    (wordFit : polyWord ≤ mw) (scanner : parameters.siteWidth ≤ mw ∧ parameters.siteWidth+parameters.bodyCap<2^mw)
    {query guesses gates : ℕ} (endFits : (task).endAddress mw query guesses gates<2^mw) :
    CandidateReportCapacity net task cell recv weight raw site origin
      (fun a => ((B).programs a).program) (B).siteID ((B).edgeID.trans (finCongr reportEdgeEq).toEmbedding)
      (B).portID (geom.castRect rfl reportEdgeEq) home hdr stored nativeFactors bank (B).slot
      (x:=input) («gap»:=parameters.privateGap) := by
  have inventory (u : Fin (R+1)) := signedReplay_inventory (H:=H) (reserve:=reserve) (ceiling:=ceiling)
    (outputs:=outputs) (field:=field) plan p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits sched initial dirs length chart history team bank u
  let frame := fun u : Fin (R+1) => (pub u 0).val
  have addr := (task).reportCapacityAddresses endFits
  exact {
    descFit := addr.1
    paramFit := addr.2
    range := inRange
    «net» := fun u => (geometryRep u).castCables reportEdgeEq
    codes := fun c => (congrArg (fun e => (e c).val) (Fields.castRect_cells (F:=geom) reportEdgeEq)).trans (codes c)
    widths := fieldWidths
    fit := wordFit
    allocation := selected(signedReplay_allocation) loads paid
    charge := selected(signedReplay_charge) frame origin hm paid dictionary v bank
    supp := fun u c => ((inventory u).1 c).trans (congrArg (fun p : SignedTaskArena.Parameters => p.report.supplementStride) sameParameters).symm.le
    marked := fun u j => ((inventory u).2.1 j).trans (congrArg (fun p : SignedTaskArena.Parameters => p.report.marked) sameParameters).symm.le
    uses := fun u => ((inventory u).2.2.trans (congrArg (fun p : SignedTaskArena.Parameters => p.report.uses) sameParameters).symm).le
    siteWidth := scanner.1
    bodyFit := scanner.2
    a := query
    k := guesses
    l := gates
    endFit := endFits
    sourceRoom := selected(signedReplay_sourceRoom) frame origin hm loads paid dictionary
  }

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
