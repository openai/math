import OAI.Computability.BorderVNP.DiagonalSelectedIssuedOwnerTables
import OAI.Computability.BorderVNP.DiagonalSelectedIssuedSaved
import OAI.Computability.BorderVNP.DiagonalNativeReportSlot
import OAI.Computability.BorderVNP.DiagonalCanonicalFragmentPlacements

/-! # The selected wired witness and the true source RAM of its signed report prefix -/

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

open VPVNP.BurstRAM RoutingISA.Transmission BorderVNP.Routing CellMacro.Generator
open FiniteEvaluator Cube.HostAddress Cube.Scatter Cube.NativeIntervals
open Packing.CellAddressCircuit Packing.CellAddressPhysical RoutingOutputs Packing.Directory
open Diagonal.ExternalSew.Fragments CompactMachine
open Cube.Tally Cube.Scatter.Assignment DiagonalTallyPacketEmit
open TeamContraction.JointHeader

local notation3 (prettyPrint := false) "allRows" => calibrated G₀ lit order position W code sites edges ports table words good
local notation3 (prettyPrint := false) "nativeRows" => NativeDemands.rows net cell edge port deliveries original live gap
local notation3 (prettyPrint := false) "receiver" => NativeDemands.receiver net cell edge port deliveries original live gap (allRows).choose
local notation3 (prettyPrint := false) "weights" => fun j : Fin (nativeRows).length => (nativeRows)[j.val].width
local notation3 (prettyPrint := false) "publicCodes" =>
  meanPackedLabel net cell receiver weights (List.finRange cells) cube.pred (BorderVNP.Cube.alphabet α (k+1)) hd
local notation3 (prettyPrint := false) "privateRows" => NativeDemands.privatePair net cell edge port deliveries original live gap
local notation3 (prettyPrint := false) "liveRows" => NativeDemands.livePair net cell edge port deliveries original live gap
local notation3 (prettyPrint := false) "rosterOf" =>
  plan.signedReceivedRows p fit W position code sites edges ports table words good seeds free count pos num hp q cube α ξ
    calibrated lit hd number parameters arenaBase profileBits frame origin

/-- The sparse cable rank of the selected history and the allocated hardware census
agree after converting the enumerated bottom tiles to the cover's site count. -/
theorem issuedReportCableCount : (B).edgeRows=(arena).cables := by
  change _+4*(R+1)*tiles = _+4*((R+1)*CoverScale.sites (Cube D) (d+1))
  rw [seedPortCount d,Nat.mul_assoc]

omit [NeZero D] in
/-- All free bits of this selected wired witness fit in its bottom-grid blocks. -/
theorem issuedReportFreeRoom :
    r*(2*((G₁).program.length+(TeamContraction.cutWidth (k+1)+a))+R*link)≤tiles*seedBlock := by
  have source : 2*((G₁).program.length+(TeamContraction.cutWidth (k+1)+a))+R*link≤k+1 := by
    change 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+R*link≤k+1
    exact (Nat.le_add_right _ _).trans fit
  exact (Nat.mul_le_mul_left r source).trans ((ceilDiv_le_iff_le_mul (show 0<tiles by exact Fintype.card_pos)).mp le_rfl)

/-- The actual report's supplied-count column is bounded by the original description
slot on the selected signed wire history, including its reserved gap. -/
theorem issuedPrivateAfter (out : ℕ → ℕ) (base : ℕ)
    (counts : ∀ c : Fin cells,out (base+c.val)=suppliedSize net (B).cell c) (j : Fin (deliveries).entries) :
    out (base+(privateRows j.val).1)+gap≤(privateRows j.val).2 :=
  private_after_returned_supply net cell edge port deliveries original live gap out base counts j

/-- Every canonical live entry, including one in an unused packet bin, reads the true
supplied owner and the offset in this selected history's emitted physical directory. -/
theorem issuedLivePlacement {levels ownerWidth word machineWord : ℕ} {σ : Type} [Fintype σ]
    (fields : Fields (B).siteRows (B).edgeRows (B).portRows cells levels ownerWidth word σ)
    (x : σ → Bool) (before after : ℕ → ℕ) (head base : ℕ)
    (geom : Packing.CellAddressPhysical.Represents net cell (placedSize net (B).programs) (B).siteID edge port fields x)
    (ids : ∀ c,(fields.cells c).val=c.val)
    (wordRoom : ∀ c,guessedSize net cell c+siteSize net cell c (placedSize net (B).programs)+suppliedSize net cell c<2^word)
    (image : Image fields ((B).siteID ∘ original) (port ∘ finProdFinEquiv.symm) x base before)
    (run : (privateLayout head base (arena).cables cells (deliveries).entries desc gap).Image before (deliveries).entries after)
    (room : (privateLayout head base (arena).cables cells (deliveries).entries desc gap).Fits machineWord before) :
    LivePlacement net cell edge port liveRows := by
  have census := plan.issuedReportCableCount p fit W position code sites edges ports table words good seeds free count pos num hp q
    cube α ξ calibrated lit hd number parameters arenaBase profileBits
  rw [←census] at run room
  exact canonical_live_placement (r:=r) (w:=(G₁).program.length+(TeamContraction.cutWidth (k+1)+a)) (link:=link)
    net cell edge port original gap (placedSize net (B).programs) (B).siteID fields x geom ids wordRoom head base before after image run room

/-- The team decoder for the original selected history is the greedy group owner that the
native chooser computes at these very signed delivery widths. -/
theorem issuedReportOwnerMap :
    (B).owners=greedyOwner (blocks:=(arena).header.blocks) (K:=cube.copies) (h:=cube.h)
      R cube.b cube.width publicCodes receiver weights := by
  unfold signedCoreDirectory checkedDirectory
  rfl

/-- The emitted selected cube and the returned packet family use exactly the same directed
crossing-bit injection, down to the coordinate within each padded bank. -/
theorem issuedReportSlot
    (bound : ∀ j, load (cablePair (NativeDemands.cableOrder net cell edge) (crossSrc net cell) (crossDst net cell) publicCodes)
      (crossWidth net cell ∘ (NativeDemands.cableOrder net cell edge).symm) j ≤ (arena).header.blocks*(cube.h*cube.b)) :
    packedSlotEmbedding net cell (NativeDemands.cableOrder net cell edge) publicCodes (arena).header.blocks
      (cube.h*cube.b) bound = (B).slot := by
  exact checkedDirectory_host_slot (r:=R) net cell (lastState).rows.site edge port (B).programs deliveries original live gap
    (allRows).choose cube hd ((allRows).choose_spec q number edge port gap) bound

/-- The chosen finite roster of this history places every compact ordinal at
the team given by its own participating signed selector. -/
theorem issuedReportRosterOwner (v : Routed (b:=cube.b) (s:=cube.width) (B).owners)
    (u : Fin (R+1)) (i : Fin (((rosterOf) v).cells u).length) :
    (B).owners v.1 (publicCodes (((rosterOf) v).order ⟨u,i⟩) (chosen cube.b cube.width v.1))=u := by
  exact routedReceivedRows_owner arena (B).owners (packed).label _ _ _ _ _ v u i

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
