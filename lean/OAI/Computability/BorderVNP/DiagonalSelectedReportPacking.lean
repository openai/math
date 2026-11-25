import OAI.Computability.BorderVNP.PackedCableOrderCast
import OAI.Computability.BorderVNP.DiagonalSelectedReportSourceSlots

/-! # The original signed history fits in its rounded physical cable blocks -/

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
variable (arenaBase profileBits : ℕ)
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
open Packing.CellAddressCircuit Packing.CellAddressPhysical RoutingOutputs Packing.Directory

local notation3 (prettyPrint := false) "allRows" => calibrated G₀ lit order position W code sites edges ports table words good
local notation3 (prettyPrint := false) "nativeRows" => NativeDemands.rows net cell edge port deliveries original live gap
local notation3 (prettyPrint := false) "receiver" => NativeDemands.receiver net cell edge port deliveries original live gap (allRows).choose
local notation3 (prettyPrint := false) "weights" => fun j : Fin (nativeRows).length => (nativeRows)[j.val].width
local notation3 (prettyPrint := false) "publicCodes" =>
  meanPackedLabel net cell receiver weights (List.finRange cells) cube.pred (BorderVNP.Cube.alphabet α (k+1)) hd

/-- The cell labels printed for the original history, using the widths
and receivers of its own delivered records. -/
noncomputable def issuedReportLabels : Fin cells → BorderVNP.Cube.Label (cube.pred+1) (BorderVNP.Cube.alphabet α (k+1)) :=
  publicCodes

local notation3 (prettyPrint := false) "labels" => plan.issuedReportLabels p fit W position code sites edges ports
  table words good free count hp q cube α ξ calibrated lit hd number parameters

/-- For each directed pair of chosen cell labels, the actual crossing widths
in sparse cable order fit in the allocated report blocks at this history. -/
theorem issuedReportPacking (j : BorderVNP.Cube.Label (cube.pred+1) (BorderVNP.Cube.alphabet α (k+1)) ×
    BorderVNP.Cube.Label (cube.pred+1) (BorderVNP.Cube.alphabet α (k+1))) :
    load (cablePair (NativeDemands.cableOrder net cell edge) (crossSrc net cell) (crossDst net cell) labels)
      (crossWidth net cell ∘ (NativeDemands.cableOrder net cell edge).symm) j ≤ (arena).header.blocks*(cube.h*cube.b) := by
  let capacity := (allRows).choose_spec q number edge port gap
  exact load_le_blocks (NativeDemands.cableOrder net cell edge) (crossSrc net cell) (crossDst net cell)
    (crossWidth net cell) publicCodes (fun e => e.property) ((Nat.cast_nonneg _).trans capacity.dataVolume)
    cube.block_pos (pow_pos hd _) (meanPackedLoads net cell receiver weights (List.finRange cells)
      (List.nodup_finRange cells) (by ext; simp) cube.pred (BorderVNP.Cube.alphabet α (k+1)) hd capacity).1 j

local notation3 (prettyPrint := false) "issuedB" => plan.signedCoreDirectory p fit W position code sites edges ports table
  words good seeds free count pos num hp q cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "cableCensus" =>
  (plan.signedReportArena_cables p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits).symm

/-- The physical opening of the selected sparse cable table uses the issued
slot of each crossing bit. Its owner labels are computed on the hardware's
own transported row and receiver tables. -/
theorem issuedOpeningSlots :
    let hardware := (issuedB).edgeID.trans (finCongr cableCensus).toEmbedding
    let rows := NativeDemands.rows net (issuedB).cell hardware (issuedB).portID deliveries original live gap
    let recv := NativeDemands.receiver net (issuedB).cell hardware (issuedB).portID deliveries original live gap
      (allRows).choose
    let label := meanPackedLabel net (issuedB).cell recv (fun i : Fin rows.length => rows[i.val].width)
      (List.finRange cells) cube.pred (BorderVNP.Cube.alphabet α (k+1)) hd
    let ord := NativeDemands.cableOrder net (issuedB).cell hardware
    ∃ pack : ∀ g, load (cablePair ord (crossSrc net (issuedB).cell) (crossDst net (issuedB).cell) label)
        (crossWidth net (issuedB).cell ∘ ord.symm) g ≤ (arena).header.blocks*(cube.h*cube.b),
      packedSlotEmbedding net (issuedB).cell ord label (arena).header.blocks (cube.h*cube.b) pack = (issuedB).slot := by
  let pack := plan.issuedReportPacking p fit W position code sites edges ports table words good free count hp q cube α ξ
    calibrated lit hd number parameters arenaBase profileBits
  exact NativeDemands.existsOpenedSlot_cast_cables net cell edge cableCensus port deliveries original live gap
    (allRows).choose cube.pred (BorderVNP.Cube.alphabet α (k+1)) hd (arena).header.blocks (cube.h*cube.b)
    (issuedB).slot pack (plan.issuedReportSlot p fit W position code sites edges ports table words good seeds free count
      pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits pack)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
