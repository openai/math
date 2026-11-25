import OAI.Computability.BorderVNP.PackedTerminalSignedGridEmitterCost
import OAI.Computability.BorderVNP.PackedSignedBundleOutput
import OAI.Computability.BorderVNP.PackedTerminalGroupedHosts
import OAI.Computability.BorderVNP.PackedFrozenSeedInitial
import OAI.Computability.BorderVNP.PackedHistoryBoxErasure
import OAI.Computability.BorderVNP.FiniteCandidateSewnRows

/-! # The fixed public signed terminal packet for the selected cover and copy counts -/

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

local notation3 (prettyPrint := false) "priv₁" => FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "reports₁" => FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "tpl₁" => template schema₁ final₁ boxes₁ hs hf priv₁ reports₁

open private oldWire from OAI.Computability.BorderVNP.PackedTerminalStagedFields

/-- The complete signed terminal emitter before choosing private verifier
assignments, a chart, a history index or any return from the native RAM.
Original ports use their static row ordinals, the spare cell is the default
owner, and each original key points to its signed descriptor-address column. -/
noncomputable abbrev frozenPacketEmitter :
    Frame ((σ ⊕ Fin reserve) ⊕ (epochFmt).Output (Boundary.Pins S (d+1) (boundaryShape S (d+1)) w T) (sh).sites w w)
      (Fin (signedGridOutputCount ((sh).edges+4*(R+1)*tiles) cells J ((R+1)*tiles) control
        (Total (tpl₁).publicDepth (tpl₁).chunkDepth)) × Fin packetWidth) :=
  signedGridEmitter (X := σ) (reserve := reserve) (Move := allowedMoves (Cube D) S.budget)
    actual (show 0 < tiles from Fintype.card_pos) count hg short sh (factorEnum D) cellNumber cf epochFmt id
    vf (@groupRow ((fan S)^T) tiles offs) (fun _ => copies*g₁) (attachedName offs copies) FinalTies.routePresent
    extend ownerFits old₁ controls boxes₁ arena stride gap desc gadgets digits
    (fun i => oldWire (FinalTies.sewnPresent (fieldSewParams actual axes d) FinalTies.routePresent i))
    (fun _ => true) (.inr true) hs hf keyFits sitesFit (Nat.lt_trans (Nat.lt_succ_self cells) keysFit)
    sw (fun _ => le_rfl) (fun _ => Fin.last cells) (fun j => .inl (.inr j)) pad
    (Retained.packetBase dest ((sh).edges+4*(R+1)*tiles) cells J ((R+1)*tiles) control) hdr

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

/-- The complete geometry output consumed by the signed public preparation.
The existing cell packet keeps every address. The following two contiguous
banks give the native six-word bundle scanner its sorted payload and inverse
marker ranks. Their shape and their inputs are fixed before the public guess. -/
noncomputable abbrev frozenPacketWithBundles :
    Frame ((σ ⊕ Fin reserve) ⊕ (epochFmt).Output (Boundary.Pins S (d+1) (boundaryShape S (d+1)) w T) (sh).sites w w)
      (Fin (o₁+(2^bundleBits+2^bundleBits)) × Fin packetWidth) :=
  Retained.appendWords first ((headers).subst signedSource)

omit [Fintype Edge] in
/-- The native table can be compiled with the all-zero literal wiring before
its own emitted addresses are installed. Replacing the literal and the
interior wire map at this arity leaves the entire emitted frame equal. -/
theorem frozenPacketWithBundles_program
    (next : Wiring R r rTime rPins ell rInner n Wire) (program : next.program=actual.program) :
    frozenPacketWithBundles (reserve := reserve) S G order position σ next count cellNumber vf cf hg short
      extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls hs hf keyFits sitesFit keysFit sw
      pad dest hdr bankLayout bundleBits shapes =
    frozenPacketWithBundles (reserve := reserve) S G order position σ actual count cellNumber vf cf hg short
      extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls hs hf keyFits sitesFit keysFit sw
      pad dest hdr bankLayout bundleBits shapes := by
  cases actual
  cases next
  cases program
  rfl

omit [Fintype Edge] in
/-- Every complete native return retains the signed cell packet at its old
addresses and publishes the two actual stable header sort banks directly
after the packet's last word. Reading these arrays also applies when later
private cells reject. -/
theorem frozenPacketWithBundles_paths {Y : Type} [Fintype Y] {active guess time₂ hw : ℕ}
    (hist : Frame (σ ⊕ Y) ((epochFmt).Output (Boundary.Pins S (d+1) (boundaryShape S (d+1)) w T) (sh).sites w w ⊕ Unit))
    (ord : Y ≃ Fin active) (fit : active≤reserve) (x : σ → Bool) (word : Fin reserve → Bool)
    {code : Code} {pub : Arg → Word hw} {mac : TeamOpcode.Macros hw 8}
    {bank : RoutingISA.Bank hw} {mem : Memory hw} {ok : Prop} {resident : (Fin guess → Bool) → Memory hw → Prop}
    (paths : ProfilePaths code guess pub mac bank mem ok time₂ dest (emittedWords hist ord fit
      (frozenPacketWithBundles (reserve:=reserve) S G order position σ actual count cellNumber vf cf hg short extend
        dir number sitePos ownerFits arena stride gap desc gadgets digits controls hs hf keyFits sitesFit keysFit sw pad dest hdr
        bankLayout bundleBits shapes) x word) resident) :
    ProfilePaths code guess pub mac bank mem ok time₂ dest (emittedWords hist ord fit first x word) resident ∧
      ∀ (run : Returns code pub mac bank mem) (i : Fin (2^bundleBits+2^bundleBits)),
        let out := Retained.branch hist ord fit x word
        let headerInput := BottomReports.BundleSort.source cells bundleBits (BottomReports.BundleSort.geometryHeaders
          signedFields old₁ desc (BottomReports.BundleSort.bankConfig banks gap valid) shapes)
        readings run.val.2.2 (Retained.packetBase dest ((sh).edges+4*(R+1)*tiles) cells J ((R+1)*tiles) control+
          Total (tpl₁).publicDepth (tpl₁).chunkDepth + i.val) =
            value (fun z => (CellPacketGeometry.geometry headerInput).eval ((signedSource).eval out) (.inl (i,z))) := by
  obtain ⟨ordinary,headersOut⟩ := ProfilePaths.split_headerBanks hist ord fit x word first signedSource banks signedFields
    old₁ desc gap shapes valid paths
  refine ⟨ordinary,fun run i => ?_⟩
  have addr : Retained.packetBase dest ((sh).edges+4*(R+1)*tiles) cells J ((R+1)*tiles) control+
      Total (tpl₁).publicDepth (tpl₁).chunkDepth = dest+o₁ := by
    dsimp only [signedGridOutputCount,Retained.packetBase,RoutingOutputs.controlsBase,RoutingOutputs.bases,RoutingOutputs.count]
    omega
  rw [addr]
  exact headersOut run i

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
