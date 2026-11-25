import OAI.Computability.BorderVNP.PackedFrozenSignedEmitter

/-! # Fixing the emitted gate list before the physical literals are chosen -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.PreparedBins
open Packing.PhysicalEpochs
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales VPVNP.VerifierNetwork
open TerminalCells FieldExport GridHosts Diagonal.ExternalSew.RowTrace Packing.CellAddressCircuit Packing.SewnField
open scoped Classical BorderVNP.Epoch.Cube
open CellPacketGeometry CellPacketGeometry.History CellPacketGeometry.History.Native CellPacketGeometry.LiveWords
open Packing.CellAddresses Packing.CellAddressPhysical Packing.RoutingOutputs CellSparse.Packet
open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator ParseBatchSort
attribute [local instance] portFintype
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {n r d T copies : ℕ}
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (σ : Type) [Fintype σ] {reserve : ℕ}
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d

local notation "w" => 60*logWidth r n
local notation "sh" => boundaryShape S (d+1) T
local notation "fmt" => Boundary.seedFormat G order position copies
local notation3 (prettyPrint := false) "epochFmt" => ProgramSchemas.epoch S (d+1) w fmt T
local notation "offs" => flatOffset (compiledOffset S (d+1)) T
local notation "J" => (fan S)^T * tiles
local notation "g₁" => inputBlockWidth r n axes d
variable {R rTime rPins ell rInner : ℕ} {Wire : Type}
    (actual : Wiring R r rTime rPins ell rInner n Wire) (count : (fan S)^T*copies=R+1)
    {cells k packetWidth : ℕ} (cellNumber : (Cube D → Deck (EnrichedOuter.depth S (d+1) T+1)) ≃ Fin cells)
    (vf : (boundaryShape S (d+1) T).sites ≤ 2^(60*logWidth r n)) (cf : cells ≤ 2^k)
    (hg : 0 < inputBlockWidth r n (Fintype.card (Cube D)) d) (short : inputBlockWidth r n (Fintype.card (Cube D)) d ≤ ell)
    (extend : 60*logWidth r n ≤ packetWidth)
    (dir : Directory.Layout) (number : e.Entry → ℕ) (sitePos : 0 < (boundaryShape S (d+1) T).sites)
    (ownerFits : k ≤ packetWidth)
local notation3 (prettyPrint := false) "publicDir" => {dir with sites := tiles, entries := J}
local notation3 (prettyPrint := false) "boxes₁" => scheduledBoxes publicDir rfl number sitePos
local notation3 (prettyPrint := false) "old₁" => (originalPins sitePos offs : Fin J → Fin (sh).sites)
local notation3 (prettyPrint := false) "schema₁" => (epochFmt).schema.append (Sewn.schema (2*(sh).edges+6*(R+1)*tiles) w)
local notation3 (prettyPrint := false) "final₁" => FinalTies.tieSchema ((sh).edges+4*(R+1)*tiles) ((R+1)*tiles) packetWidth

variable {qbits tagCap control : ℕ} (arena stride gap desc gadgets digits : ℕ) (controls : Fin control → Fin (2^packetWidth))
    (hs : ∀ j, (((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))).tags j).length≤tagCap) (hf : ∀ j, ((FinalTies.tieSchema ((boundaryShape S (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth).tags j).length≤tagCap)
    (keyFits : 60*logWidth r n≤qbits) (sitesFit : (boundaryShape S (d+1) T).sites<2^qbits)
    (keysFit : cells+1<2^k) (sw : ∀ j, ((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))).width j≤packetWidth)
    (pad : (roster (boundaryShape S (d+1) T).sites ((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))) (FinalTies.tieSchema ((boundaryShape S (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth)).length<2^qbits) (dest hdr : ℕ)

local notation3 (prettyPrint := false) "emitter" G' => frozenPacketEmitter (reserve := reserve) S G order position σ G'
  count cellNumber vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls
  hs hf keyFits sitesFit keysFit sw pad dest hdr

omit [Fintype Edge] in
/-- Every gate and output pin of the emitter is fixed before the late wiring is
filled. Changing its literal bits, pin alphabet or interior wire data preserves
the public program as long as the common validator prefix is the same. -/
theorem frozenPacketEmitter_congr_program {rPins' rInner' : ℕ} {Wire' : Type}
    (other : Wiring R r rTime rPins' ell rInner' n Wire') (same : other.program=actual.program) :
    (emitter other) = (emitter actual) := by
  cases actual with
  | mk program₁ literal₁ interior₁ fit₁ =>
    cases other with
    | mk program₂ literal₂ interior₂ fit₂ =>
      change program₂=program₁ at same
      subst program₂
      rfl

variable (bankLayout : CellBanks.Layout) (bundleBits : ℕ)
    (shapes : Fin ((fan S)^T*GridHosts.tileCount (Fintype.card (Cube D)) d) → BottomReports.BundleSort.Shape)
local notation3 (prettyPrint := false) "allWords" G' => frozenPacketWithBundles (reserve := reserve) S G order position σ G'
  count cellNumber vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls
  hs hf keyFits sitesFit keysFit sw pad dest hdr bankLayout bundleBits shapes

omit [Fintype Edge] in
/-- Both appended sorted banks and the primary cell program can be frozen
before filling any task or valuation literal. The pin alphabet and the type
of private wires may also change when the final wiring is deployed. -/
theorem frozenPacketWithBundles_congr_program {rPins' rInner' : ℕ} {Wire' : Type}
    (other : Wiring R r rTime rPins' ell rInner' n Wire') (same : other.program=actual.program) :
    (allWords other) = (allWords actual) := by
  cases actual with
  | mk program₁ literal₁ interior₁ fit₁ =>
    cases other with
    | mk program₂ literal₂ interior₂ fit₂ =>
      change program₂=program₁ at same
      subst program₂
      rfl

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
