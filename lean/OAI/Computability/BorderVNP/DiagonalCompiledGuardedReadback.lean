import OAI.Computability.BorderVNP.DiagonalCompiledGuardedHistory

/-! # Original wires and cube path of the selected signed execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.CoreDirectory

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs Diagonal.CellEntries
open scoped Classical

variable {D n d blocks b h K s r : ℕ} {P J Param Gadget Hidden : Type} [Fintype P] {bits : P → ℕ}
    {N : Network D P bits} (B : CoreDirectory N n d blocks b h K r)
    (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (widths : ∀ j, (B.programs (host j)).birth.work = mult j*(slabs j).stride)
    (hidden : BottomChoices slabs mult ≃ Hidden) (table : Hidden → N.Tables (Entry Param Gadget))
    (x : Ports bits) (pos : TableEntry n b h K s → Gadget)
    {Q : Hidden → Type} (view : ∀ z, B.Passing (table z) x pos ≃ Q z)

/-- Read the original and physical coordinates of a passing result through
the equivalence that presents each passing fiber to its consumer. -/
def ReadsThrough (decode : {u : B.Route s × B.Bank // B.Guard x u} ≃ Sigma Q)
    (v : {u : B.Route s × B.Bank // B.Guard x u}) : Prop :=
  let out := decode v
  B.Reads host slabs mult widths hidden v.val out.1 ((view out.1).symm out.2).val

/-- Changing the presentation of each passing fiber preserves the extracted
hidden bits and the native path in the originating bank. -/
theorem guardedPathEquiv_readsThrough (num : Gadget ↪ ℕ)
    (model : ∀ z, TagModels N B.edgeID B.portID B.programs (table (hidden z)) num
      (carryPred host (birthPredicate slabs mult z)))
    (legal : ∀ t, (B.programs t).birth.Local ∧ (B.programs t).program.Schema ∧ (B.programs t).program.RelativeBoxes)
    (v : {u : B.Route s × B.Bank // B.Guard x u}) :
    B.ReadsThrough host slabs mult widths hidden table x pos view
      ((B.guardedPathEquiv host slabs mult widths num hidden table model legal x pos).trans (Equiv.sigmaCongrRight view)) v := by
  let f := B.guardedPathEquiv host slabs mult widths num hidden table model legal x pos
  change B.Reads host slabs mult widths hidden v.val (f v).1 ((view (f v).1).symm (view (f v).1 (f v).2)).val
  rw [Equiv.symm_apply_apply]
  exact B.guardedPathEquiv_reads host slabs mult widths num hidden table model legal x pos v

end Cube.Physical.NativeAssignments.CoreDirectory

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
local notation3 (prettyPrint := false) "hidden" => W.bottomChoicesEquiv position edges (copies:=copies) slabs (fun _ => rfl)

open BorderVNP.Cube (TableEntry)
open BorderVNP.Cube.Physical Packing.CellAddresses Packing.BottomReports
open BorderVNP.Packing.RoutingOutputs.NativeDemands

variable {F : Type} [Field F] (cube : FixedCube F) (α ξ : ℝ)
    (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells) (gap : ℕ)

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

-- Pass the frozen dimensions directly when selecting the named circuit.
local notation3 (prettyPrint := false) "atSeed(" f ")" => f
  (D:=D) (m:=m) (K:=K) (Gadget:=Gadget) (e:=e) (S:=S) (R:=R) (r:=r) (pins:=pins)
  (link:=link) (k:=k) (d:=d) (a:=a) (regs:=regs) (rw:=rw) (ec:=ec) (width:=width) (s:=s)
  (copies:=copies) (T:=T) (header:=header) (work:=work) (order:=order) (ns:=ns) (ne:=ne) (np:=np)
  (F:=F) (cells:=cells)

local notation3 (prettyPrint := false) "B" => atSeed(signedCoreDirectory) plan p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "terms" => EnrichedTape.tags (D:=D) (m:=m) (K:=K) (E:=E)
  (Gadget:=Gadget) (e:=e) (S:=S) (start:=d+1) (T:=T) (R:=R) (r:=r) (pins:=pins) (link:=link)
  (k:=k) («axes»:=Fintype.card (Cube D)) (gridDepth:=d) (a:=a) (regs:=regs) (rw:=rw) (ec:=ec)
  (width:=width) (s:=s) (copies:=copies) (order:=order) (good:=goodState) p fit W position free count M leaf rfl y hy pos hp.block q
local notation3 (prettyPrint := false) "guards" => signedSewn_wellFormed W position code sites edges ports table C words good seeds key
  (num ∘ pos) G₁ count hp rfl q

attribute [local instance] signedCoreBatchFinite
-- Keep the stored program and its binary count width symbolic during conversion.
attribute [local irreducible] CoreDirectory.ReadsThrough UniversalMachine.programPrefix Nat.clog
local notation3 (prettyPrint := false) "widthAt" => atSeed(signedCore_widths) plan p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "present" => atSeed(signedCore_passing) plan p fit W position code sites edges ports table
  words good seeds free count y hy pos num hp q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "decode" => atSeed(signedPinnedPaths) plan p fit W position code sites edges ports table
  words good seeds free count y hy pos num hp q cube α ξ calibrated lit hd number gap

local notation3 (prettyPrint := false) "originalBits" => Fin ((fan S)^T) → Fin copies → W.Hidden position

set_option maxHeartbeats 600000 in
/-- The change of presentation from the guarded cell predicate to the passing
subtype of the actual packet on this history. -/
noncomputable abbrev signedCorePassingView (z : originalBits)
    (cubePos : TableEntry cube.pred cube.b cube.h cube.copies cube.width → Gadget)
    (pin : Ports (fun _ : FreeBlock R (GridHosts.tileCount (Fintype.card (Cube D)) d) =>
      GridHosts.inputBlockWidth r (k+1) (Fintype.card (Cube D)) d)) :
    (B).Passing (terms z).tags pin cubePos ≃ (packed).Passing (terms z) pin cubePos :=
  Equiv.cast (present z cubePos pin)

local notation3 (prettyPrint := false) "actualView" => atSeed(signedCorePassingView) plan p fit W position code
  sites edges ports table words good seeds free count y hy pos num hp q cube α ξ calibrated lit hd number gap

/-- The checked presentation fixes the target fiber on the prewired network. -/
private abbrev presentedFiber {A Q : Type} (_ : A ≃ Q) := Q

set_option maxHeartbeats 1600000 in
/-- The inverse counting argument uses the same original hidden cable bits
and the same routed, shared and local path as the physical positive program. -/
theorem signedPinnedPaths_reads
    (cubePos : TableEntry cube.pred cube.b cube.h cube.copies cube.width → Gadget)
    (pin : Ports (fun _ : FreeBlock R (GridHosts.tileCount (Fintype.card (Cube D)) d) =>
      GridHosts.inputBlockWidth r (k+1) (Fintype.card (Cube D)) d))
    (v : {u : (B).Route cube.width × (B).Bank // (B).Guard pin u}) :
    (B).ReadsThrough (D:=D) (P:=FreeBlock R tiles)
      (bits:=fun _ => GridHosts.inputBlockWidth r (k+1) axes d) (N:=net)
      (n:=cube.pred) (d:=BorderVNP.Cube.alphabet α (k+1)) (blocks:=(packed).blocks) (b:=cube.b)
      (h:=cube.h) (K:=cube.copies) (s:=cube.width) (r:=R) (Param:=PairedParameters k s) (Gadget:=Gadget)
      (J:=Fin ((fan S)^T) × (Fin axes → Deck (d+2)))
      (Q:=fun z : originalBits => presentedFiber (actualView z cubePos pin))
      (Hidden:=Fin ((fan S)^T) → Fin copies → W.Hidden position) host slabs (fun _ => copies) widthAt hidden
      (fun z : originalBits => (terms z).tags) pin cubePos (fun z : originalBits => actualView z cubePos pin) (decode cubePos pin) v := by
  unfold signedPinnedPaths signedCorePassingView
  apply CoreDirectory.guardedPathEquiv_readsThrough

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
