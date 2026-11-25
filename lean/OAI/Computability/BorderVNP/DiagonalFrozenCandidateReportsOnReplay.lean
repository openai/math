import OAI.Computability.BorderVNP.DiagonalSelectedReportRows
import OAI.Computability.BorderVNP.DiagonalReplayReportAssembly
import OAI.Computability.BorderVNP.PackedNamedEndpointTransport

/-! # Coordinates of the selected report continuation on a replayed signed frame -/

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

open BorderVNP.Cube RoutingISA.Transmission Routing TeamContraction.JointHeader
open VPVNP.BurstRAM Packing.CellAddressCircuit GeometryFrameEncoding
open scoped BigOperators
attribute [local irreducible] Nat.clog UniversalMachine.programPrefix TeamTapeInput.digits VPVNP.BurstRAM.wordBits
set_option autoImplicit false

local notation3 (prettyPrint := false) "decl(" w ")" => Prod.mk
  (Fin.ofNat ((arena).n+1) (readCode ((arena).n+1) (w).1))
  (fun (a : Sym2 (Fin (arena).header.d)) (j : Fin ((arena).n+1)) =>
    readCode ((arena).header.cap+1) ((w).2 a j))
local notation3 (prettyPrint := false) "reportEdgeEq" =>
  (plan.signedReportArena_cables p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits).symm
local notation3 (prettyPrint := false) "hdr" => fun j : Fin (deliveries).entries =>
  W.seedUseHeader position ((bundleIdx j).2) (sourceSlot j) (boxStart j) copies
local notation3 (prettyPrint := false) "stored" => fun j : Fin (deliveries).entries =>
  W.seedStored position code sites edges ports ch gp ((bundleIdx j).2)
local notation3 (prettyPrint := false) "nativeFactors" => fun j : Fin (deliveries).entries =>
  W.nativeFactors position code sites edges ports ((bundleIdx j).2)

/-- The private report continuation on the selected signed public history.
Its field operands and sparse cable map both use the allocated cable rectangle.
The count is the native demand-directory length before the distinct-pair records. -/
noncomputable abbrev signedCandidateReportsOnReplay
    {mw cb lb polyWord dictionary outputs X : ℕ} {σ : Type} [Fintype σ]
    {L : WireLayout (R+1) r link} {broadcastHeader : List Bool} {pin : Fin pins → Bool}
    {pub : HeaderExterior L broadcastHeader → Fin (R+1) → Arg → Word mw}
    {mac : HeaderExterior L broadcastHeader → Fin (R+1) → TeamOpcode.Macros mw 8}
    {reg : HeaderExterior L broadcastHeader → Fin (R+1) → Bank mw}
    {mem : HeaderExterior L broadcastHeader → Fin (R+1) → Memory mw}
    {pp lp : ℕ → ℕ × ℕ} {representative : ℕ → Fin (R+1)}
    {group : Fin (arena).header.d → Fin (R+1)} {initialBase receiving : ℕ}
    {pinSites : Fin (R+1) → Pins.Layout}
    {inputFields : HeaderExterior L broadcastHeader → (u : Fin (R+1)) → Pins.ProcessorFields (pinSites u)}
    {broadcastFrame : Fin (R+1) → BroadcastFrame} {guess : Fin (R+1) → ℕ → Bool}
    {I : Type*} [Fintype I] {resides : I → Fin cells} {keyID : I ↪ ℕ} {sizes : I → ℕ}
    (fixed : Block (R+1)) (raw : Broadcast (arena).n (arena).header.d (arena).header.cap)
    (site : ∀ z u, CandidateSite (X:=X) arena deliveries pp lp raw representative (decl(raw)) group initialBase receiving
      (pinSites u) (inputFields z u) (broadcastFrame u) (guess u) (pub z u) (mac z u) (reg z u) (mem z u)
      resides keyID sizes net cell recv weight)
    (frame : PreparationFrame G₁ L arena (decl(raw)) broadcastHeader pin pub mac reg mem)
    (origin : Fin (R+1) → ℕ)
    (geom : Fields (B).siteRows (B).edgeRows (B).portRows cells cb lb polyWord σ)
    (input : HeaderExterior L broadcastHeader → Fin (R+1) → σ → Bool) : Prop :=
  frame.CandidateReportsOnReplay (b:=dictionary) («gap»:=parameters.privateGap) (outputs:=outputs)
    fixed task net cell recv weight raw hd site ((task).lookupFrame 0) (demandRows).length origin
    (fun v => ((B).programs v).program) (B).siteID ((B).edgeID.trans (finCongr reportEdgeEq).toEmbedding)
    (B).portID (geom.castRect rfl reportEdgeEq) input (fun j => original j)
    (fun i => live (finProdFinEquiv.symm i)) home hdr stored nativeFactors (B).slot

set_option maxHeartbeats 3600000 in
/-- On the selected directory the checked report replay supplies precisely
the continuation after ownership. The scanner population contains the native
demands, and the frozen original bundles are read at the common public frame. -/
theorem signedCandidateReports_afterOwned
    {mw cb lb polyWord dictionary outputs X : ℕ} {σ : Type} [Fintype σ]
    {L : WireLayout (R+1) r link} {broadcastHeader : List Bool} {pin : Fin pins → Bool}
    {pub : HeaderExterior L broadcastHeader → Fin (R+1) → Arg → Word mw}
    {mac : HeaderExterior L broadcastHeader → Fin (R+1) → TeamOpcode.Macros mw 8}
    {reg : HeaderExterior L broadcastHeader → Fin (R+1) → Bank mw}
    {mem : HeaderExterior L broadcastHeader → Fin (R+1) → Memory mw}
    {pp lp : ℕ → ℕ × ℕ} {representative : ℕ → Fin (R+1)}
    {group : Fin (arena).header.d → Fin (R+1)} {initialBase receiving : ℕ}
    {pinSites : Fin (R+1) → Pins.Layout}
    {inputFields : HeaderExterior L broadcastHeader → (u : Fin (R+1)) → Pins.ProcessorFields (pinSites u)}
    {broadcastFrame : Fin (R+1) → BroadcastFrame} {guess : Fin (R+1) → ℕ → Bool}
    {I : Type*} [Fintype I] {resides : I → Fin cells} {keyID : I ↪ ℕ} {sizes : I → ℕ}
    (fixed : Block (R+1)) (raw : Broadcast (arena).n (arena).header.d (arena).header.cap)
    (site : ∀ z u, CandidateSite (X:=X) arena deliveries pp lp raw representative (decl(raw)) group initialBase receiving
      (pinSites u) (inputFields z u) (broadcastFrame u) (guess u) (pub z u) (mac z u) (reg z u) (mem z u)
      resides keyID sizes net cell recv weight)
    (frame : PreparationFrame G₁ L arena (decl(raw)) broadcastHeader pin pub mac reg mem)
    (origin : Fin (R+1) → ℕ)
    (geom : Fields (B).siteRows (B).edgeRows (B).portRows cells cb lb polyWord σ)
    (input : HeaderExterior L broadcastHeader → Fin (R+1) → σ → Bool)
    (reached : plan.signedCandidateReportsOnReplay (dictionary:=dictionary) (outputs:=outputs)
      p fit W position code sites edges ports table words good seeds free count pos num hp q cube α ξ calibrated
      lit hd number parameters arenaBase profileBits fixed raw site frame origin geom input) :
    frame.AfterOwned task fixed (packed).label recv weight ((task).lookupFrame 0) (demandRows).length
      (plan.signedReportSources p fit W position code sites edges ports table words good seeds free count pos num hp
        q cube α ξ calibrated lit hd number parameters arenaBase profileBits (fun _ => initialBase) origin) := by
  exact frame.afterOwnedFromSites (b:=dictionary) («gap»:=parameters.privateGap) (outputs:=outputs)
    fixed task net cell recv weight raw hd site ((task).lookupFrame 0) (demandRows).length origin
    (fun v => ((B).programs v).program) (B).siteID ((B).edgeID.trans (finCongr reportEdgeEq).toEmbedding)
    (B).portID (geom.castRect rfl reportEdgeEq) input (fun j => original j)
    (fun i => live (finProdFinEquiv.symm i)) home hdr stored nativeFactors (B).slot reached

/-- A single independent report observation at the selected source numbering. -/
noncomputable abbrev signedCandidateReportTest
    {mw cb lb polyWord dictionary outputs X : ℕ} {σ : Type} [Fintype σ]
    {L : WireLayout (R+1) r link} {broadcastHeader : List Bool} {pin : Fin pins → Bool}
    {pub : HeaderExterior L broadcastHeader → Fin (R+1) → Arg → Word mw}
    {mac : HeaderExterior L broadcastHeader → Fin (R+1) → TeamOpcode.Macros mw 8}
    {reg : HeaderExterior L broadcastHeader → Fin (R+1) → Bank mw}
    {mem : HeaderExterior L broadcastHeader → Fin (R+1) → Memory mw}
    {pp lp : ℕ → ℕ × ℕ} {representative : ℕ → Fin (R+1)}
    {group : Fin (arena).header.d → Fin (R+1)} {initialBase receiving : ℕ}
    {pinSites : Fin (R+1) → Pins.Layout}
    {inputFields : HeaderExterior L broadcastHeader → (u : Fin (R+1)) → Pins.ProcessorFields (pinSites u)}
    {broadcastFrame : Fin (R+1) → BroadcastFrame} {guess : Fin (R+1) → ℕ → Bool}
    {I : Type*} [Fintype I] {resides : I → Fin cells} {keyID : I ↪ ℕ} {sizes : I → ℕ}
    (fixed : Block (R+1)) (raw : Broadcast (arena).n (arena).header.d (arena).header.cap)
    (site : ∀ z u, CandidateSite (X:=X) arena deliveries pp lp raw representative (decl(raw)) group initialBase receiving
      (pinSites u) (inputFields z u) (broadcastFrame u) (guess u) (pub z u) (mac z u) (reg z u) (mem z u)
      resides keyID sizes net cell recv weight)
    (frame : PreparationFrame G₁ L arena (decl(raw)) broadcastHeader pin pub mac reg mem)
    (origin : Fin (R+1) → ℕ)
    (geom : Fields (B).siteRows (B).edgeRows (B).portRows cells cb lb polyWord σ)
    (input : HeaderExterior L broadcastHeader → Fin (R+1) → σ → Bool) (stage : TeamContraction.CandidateReportStage) : Prop :=
  frame.ReportTest (b:=dictionary) («gap»:=parameters.privateGap) (outputs:=outputs)
    fixed task net cell recv weight raw hd site ((task).lookupFrame 0) (demandRows).length origin
    (fun v => ((B).programs v).program) (B).siteID ((B).edgeID.trans (finCongr reportEdgeEq).toEmbedding)
    (B).portID (geom.castRect rfl reportEdgeEq) input (fun j => original j)
    (fun i => live (finProdFinEquiv.symm i)) home hdr stored nativeFactors (B).slot stage

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
