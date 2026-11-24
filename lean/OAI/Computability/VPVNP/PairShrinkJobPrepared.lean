import OAI.Computability.VPVNP.PairShrinkJobOperands
import OAI.Computability.VPVNP.PairShrinkCallABI

/-!
# Starting the installed map writer after a concrete party gather

The selected local record determines the grouped entry. The parent node
provides its independent output half, and its child packets and absorbed
guesses provide the other input indices. The old external term and demand
tables supply the published word widths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM BurstRAM.PrivateRAM Compression Compression.State Compression.PackingData
open Compression.ShrinkMotif Compression.ShrinkEnergy MotifBlocks MotifGrid MotifConversion
open MotifEntry NetworkKernel CompressorRecords CompressorRecords.ShrinkSlots
open CompressorRecords.ShrinkSliceSweep

variable {a b g w p r t n limit endAddr : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K}
variable (B : S.Templates) (degree : ℕ) (ord : B.Entry → Fin t)
variable {δ : ℝ} (X : State a (packingLaneBits a g))
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) (sel : X.ShrinkSelection B.shrink)
variable (m : X.packingData.Motif) (j : Fin 6) (J : Job X B.shrink ready sel m j w)
/-- Classical equality on old base vertices used to identify this party's selected map inputs. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X B.shrink sel
local notation "sub" => SlotLevel.Shape.subdivisions (levelShape (b := b) X)
local notation "slots" => X.shrinkStateIndex ready (side)
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "BW" => ShrinkPreparedCall.widthsDemand X m
local notation "idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)
local notation "cd" => ShrinkCallDemandCells.cdBase X m J.arena J.nodes
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel))
  (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) m j))

/-- The selected map row is the actual entry of the resident's local polynomial. -/
noncomputable def Job.entryInput : LocalHistory.EntryInput B.shrink :=
  ShrinkPreparedCall.input B.shrink X sel (side) (sub) (slots) ready.count_pos
    m j J.old hidden J.parent

local notation "call" => Job.entryInput B X ready sel m j J hidden
local notation "family" => ShrinkCallABI.family B degree a ord
local notation "L" => MapHandlerOperand.layout (family) demandMass_pos (call)
local notation "D" => demandBits demandSource demandTarget j
  (LocalHistory.EntryInput.demandBits (call))
local notation "W" => MotifSelector.mapHalf supply (fun _ ↦ inputBits)
  (LocalHistory.EntryInput.supplyBits (call))
variable (ok : ShrinkCallFields.Fits (w := w) (n := n) (limit := limit) (t := t)
  (u := repetitions B.shrink (ShrinkPreparedCall.widthsDemand X m)) B.shrink
  (ShrinkPreparedCall.widthsDemand X m) (sel m).val J.scratch (ShrinkMotifOrder.stateNumber X m).val
  (ShrinkCallDemandCells.cdBase X m J.arena J.nodes))

/-- The map-handler workspace built from this party's demand and supply bits, selected term,
and fitted scratch addresses. -/
noncomputable abbrev Job.mapWorkspace :
    MapHandlerOperand.Workspace (w := w) (family) demandMass_pos (call) :=
  ShrinkCallFields.workspace B.shrink (MapInline.callProgram (L)) (BW) (sel m).val
    (D) (W) J.scratch idx (side) (cd) ok

variable (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (common : Fin 24 ↪ Fin r)
variable (cfg : Config w p r) (mem : Memory w)

set_option maxHeartbeats 1400000 in
-- The typed entry and the branch-selected shrink index appear at several fiber coordinates.
/-- The actual interval gather, original packet arena and selected term record
establish every input obligation of the installed private map interpreter. -/
theorem Job.prepared_after_gather (before : Word w → Word w)
    (stage : J.Assembled before cfg.privateMem)
    (children : J.ChildWords before endAddr)
    (ends : ∀ u, J.arena.base (J.nodes u) + J.arena.stride ≤ J.scratch.staging)
    (guessed : ShrinkCallSupplyCells.Absorbed X (side) (widths) m j J.scratch hidden before)
    (T : IncidenceDirectory w) (origin : ℕ) (level : Word w)
    (tables : J.OldPublished (ShrinkCallABI.operands degree) (ShrinkCallABI.pub cfg common)
      (ShrinkCallABI.state cfg common) mem level T origin)
    (two : 2 < 2 ^ w) (termRoom : ShrinkInput.termEnd X origin 10 < 2 ^ w)
    (pairs : ShrinkTermInputs.statePairs X (ShrinkInput.demandHead X origin) mem)
    (terms : TermRecordScan.Fields B.shrink ShrinkSliceArrays.supplyRoles demandMass_pos
      (BW) (sel m).val (ShrinkTermSelection.rowBase X (ShrinkInput.termHead X origin) 10 m) mem) :
    MapHandlerOperand.Prepared (family) demandMass_pos (call) dfs saved common cfg mem
      (Job.mapWorkspace B degree ord X ready sel m j J hidden ok) := by
  apply ShrinkPreparedCall.prepared B degree ord X sel (side) (sub) (slots) ready.count_pos
    m j J.old hidden J.parent J.scratch J.arena J.nodes ok dfs saved common cfg mem before
  · exact Job.Assembled.demandFields J stage children ends
  · exact Job.Assembled.hiddenFields J hidden stage guessed ok.ordinal
      (fun t ↦ ok.supply (!side, t))
  · exact stage.retained
  · intro arg
    have h := ShrinkCallHeader.fields_eval X B.shrink sel m (ShrinkCallABI.operands degree)
      (ShrinkCallABI.pub cfg common) (ShrinkCallABI.state cfg common) level mem J.arena T
      origin J.older J.pitch J.first J.scratch.hidden J.scratch.stride J.scratch.hist
      tables.levelData tables.live tables.tables tables.space two termRoom pairs terms j arg
    have heap : ShrinkCallHeader.scratch X J.scratch.hidden J.scratch.stride J.scratch.hist =
        J.scratch := by
      unfold ShrinkCallHeader.scratch
      rw [← tables.motifCount]
    rw [heap] at h
    exact h

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
