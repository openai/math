import OAI.Computability.BorderVNP.PackedFrozenSignedEmitter
import OAI.Computability.BorderVNP.PackedFrozenPacketDirectories

/-! # Reading all original bundle words from the installed signed output -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open Crossing Packing Packing.BottomReports RoutingISA VPVNP VPVNP.VerifierNetwork VPVNP.BurstRAM
open RoutingISA.Evaluator GeometryFrameEncoding ParseBatchSort Packing.CellAddressCircuit
set_option maxHeartbeats 800000
set_option maxRecDepth 4200

variable {X Y V Z : Type} [Fintype X] [Fintype Y] [Fintype V] [Fintype Z]
    {reserve active o w J s m n d k b : ℕ} (hist : Frame (X ⊕ Y) (V ⊕ Unit)) (ord : Y ≃ Fin active)
    (fit : active≤reserve) (x : X → Bool) (word : Fin reserve → Bool)
    (first : Frame ((X ⊕ Fin reserve) ⊕ V) (Fin o × Fin w)) (src : Frame ((X ⊕ Fin reserve) ⊕ V) Z)
    (banks : CellBanks.Layout) (F : Fields s m n banks.cells d k w Z)
    (old : Fin J → Fin s) (desc gap : ℕ) (shape : Fin J → BundleSort.Shape) (valid : Frame Z Unit)

local notation3 (prettyPrint := false) "bankWords" => (BundleSort.headerBanks banks F b old desc gap shape valid).subst src
local notation3 (prettyPrint := false) "both" => Retained.appendWords first bankWords
local notation3 (prettyPrint := false) "input" => Retained.branch hist ord fit x word
local notation3 (prettyPrint := false) "prepared" => BundleSort.source banks.cells b
  (BundleSort.geometryHeaders F old desc (BundleSort.bankConfig banks gap valid) shape)

/-- The original-bundle payload and inverse ranks are read solely from
the actual words at the destination. Either sorted bank can be inspected
without any assumption on the execution that produced those words. -/
theorem headerBanks_of_returned_words (ram : ℕ → ℕ) (dest payload : ℕ) (start : payload=dest+o)
    (written : ∀ i, ram (dest+i.val)=emittedWords hist ord fit both x word i) :
    ∀ i : Fin (2^b+2^b), ram (payload+i.val)=value (fun t =>
      (CellPacketGeometry.geometry prepared).eval (src.eval input) (.inl (i,t))) := by
  intro i
  rw [start]
  simpa only [emittedWords,Fin.val_natAdd,Retained.appendWords_second,Frame.subst_eval,BundleSort.headerBanks,
    Frame.select_eval,Retained.branch,Nat.add_assoc] using written (Fin.natAdd o i)

end PackedHistoryCircuit.Retained

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

local notation3 (prettyPrint := false) "priv₁" => FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "reports₁" => FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "tpl₁" => template schema₁ final₁ boxes₁ hs hf priv₁ reports₁

local notation3 (prettyPrint := false) "first" => frozenPacketEmitter (reserve := reserve) S G order position σ actual count
  cellNumber vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls hs hf keyFits sitesFit keysFit
  sw pad dest hdr
local notation3 (prettyPrint := false) "o₁" => signedGridOutputCount ((sh).edges+4*(R+1)*tiles) cells J ((R+1)*tiles)
  control (Total (tpl₁).publicDepth (tpl₁).chunkDepth)
local notation3 (prettyPrint := false) "pre" => TerminalCells.fields (Move := allowedMoves (Cube D) S.budget) (q := axes)
  (d := EnrichedOuter.depth S (d+1) T) (E := (sh).edges) vf cf (@groupRow ((fan S)^T) tiles offs) (fun _ => copies*g₁)
local notation3 (prettyPrint := false) "raw" => FieldExport.fields pre (fieldSewParams actual axes d) (attachedName offs copies)
local notation3 (prettyPrint := false) "route₀" => Retained.Terminal.route (X := σ) (reserve := reserve) epochFmt
local notation3 (prettyPrint := false) "extent₀" => Retained.Terminal.width (X := σ) (reserve := reserve) epochFmt true
local notation3 (prettyPrint := false) "primary" => withSewnFields (boundFrame (factorEnum D) cellNumber cf route₀ extent₀)
local notation3 (prettyPrint := false) "signedSource" => stagedSource raw primary
local notation3 (prettyPrint := false) "signedFields" => Fields.widenWidths (stagedFields raw) extend (Sum.inr false)

variable (bankLayout : CellBanks.Layout) (bundleBits : ℕ)
    (shapes : Fin ((fan S)^T*GridHosts.tileCount (Fintype.card (Cube D)) d) → BottomReports.BundleSort.Shape)
local notation3 (prettyPrint := false) "banks" => ({ bankLayout with cells := cells } : CellBanks.Layout)
local notation3 (prettyPrint := false) "valid" => VPVNP.VerifierNetwork.Frame.initial (fun _ : Unit => Sum.inr true)
local notation3 (prettyPrint := false) "headers" => BottomReports.BundleSort.headerBanks banks signedFields bundleBits old₁
  desc gap shapes valid

omit [Fintype Edge] in
/-- At the absolute published directory of the frozen chronological emitter,
the two original-bundle arrays equal the true sorted source at every index.
The assertion only asks for wordwise readback at that emitter's destination. -/
theorem frozen_bundle_words_at {Y : Type} [Fintype Y] {active : ℕ}
    (hist : Frame (σ ⊕ Y) ((epochFmt).Output (Boundary.Pins S (d+1) (boundaryShape S (d+1)) w T) (sh).sites w w ⊕ Unit))
    (ord : Y ≃ Fin active) (fit : active≤reserve) (x : σ → Bool) (word : Fin reserve → Bool)
    (fixed : control=37) (ram : ℕ → ℕ)
    (written : ∀ i, ram (dest+i.val)=emittedWords hist ord fit
      (frozenPacketWithBundles (reserve:=reserve) S G order position σ actual count cellNumber vf cf hg short extend
        dir number sitePos ownerFits arena stride gap desc gadgets digits controls hs hf keyFits sitesFit keysFit sw pad dest hdr
        bankLayout bundleBits shapes) x word i) :
    let dirs := frozenPacketDirectories tpl₁ dest ((sh).edges+4*(R+1)*tiles) J ((R+1)*tiles) bundleBits
    let read := Retained.branch hist ord fit x word
    let source := BottomReports.BundleSort.source cells bundleBits (BottomReports.BundleSort.geometryHeaders
      signedFields old₁ desc (BottomReports.BundleSort.bankConfig banks gap valid) shapes)
    ∀ i : Fin (2^bundleBits+2^bundleBits), ram (dirs.bundlePayload+i.val) =
      value (fun z => (CellPacketGeometry.geometry source).eval ((signedSource).eval read) (.inl (i,z))) := by
  intro dirs read source
  have start : dirs.bundlePayload = dest+o₁ := by
    have h := (frozenPacketDirectories_locations tpl₁ dest ((sh).edges+4*(R+1)*tiles) J ((R+1)*tiles) bundleBits).2.2.2.1
    exact h.trans (congrArg (fun c : ℕ => dest+signedGridOutputCount ((sh).edges+4*(R+1)*tiles) cells J ((R+1)*tiles) c
      (Total (tpl₁).publicDepth (tpl₁).chunkDepth)) fixed.symm)
  exact Retained.headerBanks_of_returned_words hist ord fit x word first signedSource banks signedFields old₁ desc gap
    shapes valid ram dest dirs.bundlePayload start written

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
