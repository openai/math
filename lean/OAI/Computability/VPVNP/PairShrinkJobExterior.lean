import OAI.Computability.VPVNP.PairShrinkGatherExterior
import OAI.Computability.VPVNP.PairShrinkResidentMemory
import OAI.Computability.VPVNP.PairShrinkVertexImage

/-!
# Exterior scratch of a scheduled shrinking job

The actual descriptor pointer comes from the retained level. The selected
workspace fixes the histogram and all private write intervals. The pure
gathered action preserves each exterior word for every incoming scratch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif MotifEntry
open MotifBlocks MotifGrid MotifConversion NetworkKernel CompressorRecords
open CompressorRecords.ShrinkSlots NodeArguments ShrinkMapImage.Registers

variable {w g packetEnd endAddr t n limit : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K}
variable (B : S.Templates) (ord : B.Entry → Fin t) (i : Fin S.steps)
local notation "degree" => slotDegree S
local notation "family" => ShrinkVertexImage.matrixFamily B ord i
local notation "gathers" => ShrinkVertexImage.gatherFamily B ord i
variable (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (sel : X.ShrinkSelection B.shrink)
variable (m : X.packingData.Motif) (party : Fin 6)
variable (J : Job X B.shrink (S.shrink i) sel m party w)
/-- Classical decidable equality on the compression state’s base vertices for the
exterior-memory bounds of a scheduled shrink job. -/
noncomputable local instance stepBaseDecidable : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X B.shrink sel
local notation "BW" => ShrinkPreparedCall.widthsDemand X m
local notation "idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)
local notation "cd" => ShrinkCallDemandCells.cdBase X m J.arena J.nodes
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel))
  (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) m party))
local notation "call" => Job.entryInput B X (S.shrink i) sel m party J hidden
local notation "L" => MapHandlerOperand.layout family demandMass_pos call
variable (ok : ShrinkCallFields.Fits (w := w) (n := n) (limit := limit) (t := t)
  (u := repetitions B.shrink (ShrinkPreparedCall.widthsDemand X m)) B.shrink
  (ShrinkPreparedCall.widthsDemand X m) (sel m).val J.scratch (ShrinkMotifOrder.stateNumber X m).val
  (ShrinkCallDemandCells.cdBase X m J.arena J.nodes))
local notation "W" => Job.mapWorkspace B degree ord X (S.shrink i) sel m party J hidden ok
variable (hw : MapConstants.widthThreshold B.shrink ≤ w)
variable (P : Fin 5 → Word w) (state : Word w) (mem : Memory w)
local notation "ptr" => PhaseRecipe.Expr.eval P state mem (ShrinkCallFields.Inputs.descriptor
  (ShrinkCallHeader.Operands.inputs (ShrinkCallABI.operands degree) (S.degreeExponent i.castSucc)))

set_option maxHeartbeats 1400000 in
-- Align the selected job input, workspace and gathered action at the same schedule index.
/-- A genuine map at this substep preserves every word below staging that
lies outside the histogram, on an arbitrary incoming logical scratch. -/
theorem Job.gathered_preserves (saved : DFS.Scratch w endAddr)
    {baseline : Word w → Word w} (packets : J.Packets packetEnd baseline)
    (histEnd : J.scratch.hist + t ≤ J.scratch.hidden)
    {level : Word w} {T : IncidenceDirectory w} {origin : ℕ}
    (old : J.OldPublished (ShrinkCallABI.operands degree) P state mem level T origin)
    {events : List (Event w)} {out : DFS.Scratch w endAddr}
    (got : gatheredAction family gathers call J hw P state mem W saved = some (events, out)) :
    ∀ q : Word w, q.val < J.scratch.staging →
      (q.val < J.scratch.hist ∨ J.scratch.hist + t ≤ q.val) →
        rawScratch out q = rawScratch saved q := by
  have address := Job.descriptor_address B degree X (S.shrink i) sel m party J P state mem old
  have descFit : (ptr).val + Fintype.card ShrinkCallFields.Arg ≤ 2 ^ w := by
    rw [address]
    have h := ok.room.trans_lt ok.capacity.room
    unfold ShrinkCallFields.Scratch.target ShrinkCallFields.Scratch.source at h
    exact (Nat.add_le_add_right (Nat.mod_le ..) _).trans (by omega)
  have outside := gathered_exterior family gathers call J hw P state mem W saved packets descFit got
  exact ShrinkCallFields.resident_exterior B.shrink (L).core ((L).corePC (L).locations)
    BW (sel m).val
    (demandBits demandSource demandTarget party (LocalHistory.EntryInput.demandBits call))
    (MotifSelector.mapHalf supply (fun _ ↦ inputBits) (LocalHistory.EntryInput.supplyBits call))
    J.scratch idx side cd ok histEnd address outside

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
