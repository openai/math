import OAI.Computability.VPVNP.PairSimulationShrinkRowHistogram
import OAI.Computability.VPVNP.PairShrinkResidentMemory
import OAI.Computability.VPVNP.PairShrinkVertexImage

/-!
# Histogram effect of a scheduled shrinking job

The old level header locates the descriptor. The concrete job places the histogram
before staging and the directory after it, so every bin counts the occurrences of
its parameter in the selected entry.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif MotifEntry
open MotifBlocks MotifGrid MotifConversion NetworkKernel CompressorRecords
open CompressorRecords.ShrinkSlots NodeArguments ShrinkMapImage.Registers
open scoped Fin.CommRing

variable {w g packetEnd endAddr t n limit : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K}
variable (B : S.Templates) (ord : B.Entry → Fin t) (i : Fin S.steps)
local notation "degree" => slotDegree S
local notation "family" => ShrinkVertexImage.matrixFamily B ord i
local notation "gathers" => ShrinkVertexImage.gatherFamily B ord i
variable (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (sel : X.ShrinkSelection B.shrink)
variable (m : X.packingData.Motif) (party : Fin 6)
variable (J : Job X B.shrink (S.shrink i) sel m party w)
private noncomputable local instance histogramJobBase : DecidableEq X.Base := Classical.decEq _
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
local notation:max "bin" l:max => ((J.scratch.hist + Fin.val (l : Fin t) : ℕ) : Word w)

set_option maxHeartbeats 1800000 in
-- Align the dependent schedule, party and workspace indices for the gathered action.
/-- A successful gathered map of the selected job adds its entry's multiplicity at every bin. -/
theorem Job.gathered_histogram (saved : DFS.Scratch w endAddr)
    {baseline : Word w → Word w} (packets : J.Packets packetEnd baseline)
    (floor : endAddr ≤ J.scratch.hist) (histEnd : J.scratch.hist + t ≤ J.scratch.hidden)
    {level : Word w} {T : IncidenceDirectory w} {origin : ℕ}
    (old : J.OldPublished (ShrinkCallABI.operands degree) P state mem level T origin)
    {events : List (Event w)} {out : DFS.Scratch w endAddr}
    (got : gatheredAction family gathers call J hw P state mem W saved = some (events, out)) :
    ∀ l : Fin t, rawScratch out (bin l) = rawScratch saved (bin l) +
      (((MapHandlerOperand.names family demandMass_pos call).getD []).count l : Word w) := by
  have room := ok.room.trans_lt ok.capacity.room
  unfold ShrinkCallFields.Scratch.target ShrinkCallFields.Scratch.source at room
  have descRoom : J.scratch.descriptor < 2 ^ w := by omega
  have ptrVal : (ptr).val = J.scratch.descriptor := by
    rw [Job.descriptor_address B degree X (S.shrink i) sel m party J P state mem old]
    exact Nat.mod_eq_of_lt descRoom
  have below : J.scratch.hist + t ≤ J.scratch.staging := histEnd.trans (Nat.le_add_right ..)
  have beforeDir : J.scratch.hist + t ≤ J.scratch.directory := below.trans (Nat.le_add_right ..)
  have binVal (l : Fin t) : (bin l).val = J.scratch.hist + l.val :=
    Nat.mod_eq_of_lt ((Nat.add_lt_add_left l.isLt _).trans_le (W).histogramFit)
  apply ShrinkMapImage.Registers.gathered_histogram family gathers X sel mem call J hw P W saved
    state packets floor _ below _ _ got
  · change (ptr).val + Fintype.card ShrinkCallFields.Arg ≤ 2 ^ w
    rw [ptrVal]
    omega
  · intro l
    left
    change (bin l).val < (ptr).val
    rw [binVal, ptrVal]
    exact (Nat.add_lt_add_left l.isLt _).trans_le (beforeDir.trans (Nat.le_add_right ..))
  · intro l k eqn
    have len := MapPortAgreement.ports_length_le supply party (L).core.edgeOrder
    have card : 2 * Fintype.card (Bool × Fin 4) = 16 := by simp
    rw [card] at len
    have dirFit : J.scratch.directory + k.val < 2 ^ w :=
      (Nat.add_lt_add_left (k.isLt.trans_le len) _).trans descRoom
    have val := congrArg Fin.val eqn
    change (bin l).val = ((J.scratch.directory : Word w) + (k.val : Word w)).val at val
    rw [binVal, ← Nat.cast_add, show ((J.scratch.directory + k.val : ℕ) : Word w).val =
      J.scratch.directory + k.val from Nat.mod_eq_of_lt dirFit] at val
    have := l.isLt
    omega

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
