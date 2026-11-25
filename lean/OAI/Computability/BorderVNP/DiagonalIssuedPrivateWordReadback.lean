import OAI.Computability.BorderVNP.PackedReportPrivateWords
import OAI.Computability.BorderVNP.PackedFrozenRoutingNames
import OAI.Computability.BorderVNP.PackedTerminalSignedHeaderDepth
import OAI.Computability.BorderVNP.DiagonalFrozenCandidateReportsOnReplay
import OAI.Computability.BorderVNP.PackedFrozenEnrichedPacketGeometry

/-! # The geometry and private words read from the original frozen packet -/

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

variable {SeedInput : Type} [Fintype SeedInput] (x : SeedInput → Bool)
local notation3 (prettyPrint := false) "words" => ((plan.execute G₀ order position SeedInput).choose).eval x
local notation3 (prettyPrint := false) "good" => (plan.frozenLeaf G₀ order position W code sites edges ports table x).property
variable (seeds : ∀ h, ∀ i : Fin S.rounds,
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
    (q : (packHistory (plan.frozenLeaf (tapeTemplate p fit pins) order position W code sites edges ports table x)
      plan.compiled.machine.epoch T).Index)
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
local notation3 (prettyPrint := false) "original" => originalDescriptionRows M leaf q deliveries rfl order
local notation3 (prettyPrint := false) "live" => (Equiv.refl (FreeBlock R tiles)).toEmbedding
local notation3 (prettyPrint := false) "B" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number gap

variable (arenaBase profileBits : ℕ)
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
open BorderVNP.Cube VPVNP.BurstRAM VPVNP.VerifierNetwork
open Packing.RoutingOutputs Packing.CellAddressCircuit GeometryFrameEncoding DiagonalResidueRAM

variable {mw reserve cellBits : ℕ}
    (wr : WidthRanges S (d+1) T (60*logWidth r (k+1))) (hm : 0 < «m»)
    (widths : ℕ → ℕ)
    (ord : ∀ j, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r (k+1)) j ≃ Fin (widths j))
    (bf : broadcastWidth (fan S) widths T ≤ reserve)
    (vf : (boundaryShape S (d+1) T).sites ≤ 2^(60*logWidth r (k+1)))
    (cf : cells ≤ 2^cellBits) (extend : 60*logWidth r (k+1) ≤ «mw»)
    (sitePos : 0 < (boundaryShape S (d+1) T).sites)
    (origin : ℕ) (mem : Memory mw)

local notation3 (prettyPrint := false) "data" => plan.frozenIssuedReportGeometry G₀ order position W code sites edges ports table x
  wr hm widths ord bf G₁ number vf cf extend q
local notation3 (prettyPrint := false) "rawPins" => @TerminalCells.originalPins ((fan S)^T) tiles _ sitePos
  (RowTrace.flatOffset (RowTrace.compiledOffset S (d+1)) T)
local notation3 (prettyPrint := false) "reportEdgeEq" =>
  (plan.signedReportArena_cables p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits).symm
local notation "rest" => Frame.initial (fun _ : Outputs 0 mw => Sum.inr false)

set_option maxRecDepth 9000 in
set_option maxHeartbeats 4000000 in
/-- The geometry image and private words of the attained terminal packet are precisely
those of the numbered sites, ports and cable rectangle read by the report program.
Its empty output tail contributes no extra words. -/
theorem frozenCandidateReportFieldWords
    (issued : Image (data).1 rawPins (id : Fin ((R+1)*tiles) → Fin ((R+1)*tiles)) (data).2 origin (readings mem) ∧
      ∀ i : Fin (cells+((deliveries).entries+cells)),
        readings mem (origin+(B).edgeRows*3+RoutingOutputs.count (B).edgeRows cells (deliveries).entries ((deliveries).teams*(deliveries).sites)+i.val) =
          ParseBatchSort.value (fun j => (privateViews (data).1 rawPins).eval (data).2 (i,j))) :
    Image ((data).1.castRect rfl reportEdgeEq) ((B).siteID ∘ original) ((B).portID ∘ live ∘ finProdFinEquiv.symm)
        (data).2 origin (readings mem) ∧
      ∀ i : Fin (((arena).cells+((deliveries).entries+(arena).cells))+0),
        mem (origin+(arena).cables*3+RoutingOutputs.count (arena).cables (arena).cells (deliveries).entries ((deliveries).teams*(deliveries).sites)+i.val) =
          word mw (ParseBatchSort.value fun j => (withPrivateViews ((data).1.castRect rfl reportEdgeEq)
            ((B).siteID ∘ original) rest).eval (data).2 (.inl (i,j))) := by
  have named : rawPins=(B).siteID ∘ original :=
    plan.frozen_original_pins G₀ order position W code sites edges ports table x q deliveries sitePos
  constructor
  · apply Image.castCables
    exact plan.frozen_routing_image G₀ order position W code sites edges ports table x q deliveries sitePos
      (data).1 (data).2 origin (readings mem) issued.1
  · apply castCables_privateWords reportEdgeEq
    apply privateWords_without_tail
    intro i
    exact (issued.2 i).trans (congrArg
      (fun pins => ParseBatchSort.value (fun j => (privateViews (data).1 pins).eval (data).2 (i,j))) named)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
