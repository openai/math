import OAI.Computability.VPVNP.PairShrinkCallABI
import OAI.Computability.VPVNP.PairShrinkCallPublished
import OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders
import OAI.Computability.VPVNP.CompressorShrinkScheduledRetention
import OAI.Computability.VPVNP.CompressorShrinkTailReadback
import OAI.Computability.VPVNP.CompressorSelectedPayloadHistory

/-!
# Resident shrinking headers from the native publication groups

The old level's descriptor and term words are read in the memory reached
after the three terminal groups. The length word and directory pointers
are retained with that level through the subsequent selected passes.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkResidentHeaders

open BurstRAM Compression CompressorRecords DescriptorSpace BlockPlanner PhaseRecipe Schedule
open ShrinkBlockInputs ShrinkScheduledTail SourceOnline SourceTransport
open scoped Fin.CommRing

variable {K : Type*} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
variable {w g : ℕ} {base : Word w} {positions blocks t cap : ℕ} {i : Fin S.steps}
variable {X : State (a i) (packingLaneBits (a i) g)} {sel : SelectedScore.Selection B X}
variable {m : Memory w} {T : IncidenceDirectory w}
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "first" => Script.levelsPerBlock prog * t
local notation "cur" => first + i.val
local notation "head" => levelStart L cur
local notation "nxt" => levelStart L (first + (i.val + 1))
local notation "tab" => (fun j : Fin 6 ↦ tableBase L cur j)
local notation "pt" => Workspace.ports (arity (Script.catalog prog)) base
local notation "pub" => Ports.data pt
local notation "st" => (levelStart L first : Word w)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "step" => (10 : Word w)
local notation "score" => SelectedArena.origin X term step + 2
local notation "layer" => Fin.val (m (head + 14))

variable {ms ps : List (SourceOnline.Packet (BlockProgram.script B) w)}
variable (tail : Result B base positions blocks t cap i X m ms ps)

private theorem header_gap : head + 66 ≤ nxt := by
  have sz : levelHeaderWords L = 66 := rfl
  rw [← Nat.add_assoc]
  simp only [levelStart, Nat.succ_mul, levelWords, sz]
  omega

include tail in
/-- All the old fields consumed by a party are recovered from the actual
metadata and head publications, including the selected score cell. -/
theorem oldLevel (live : t < blocks) (size : X.positions ≤ positions) (fit : endAddress L < 2 ^ w)
    (header : ShrinkHeaderReads.Header i X T (tab 0) L first m)
    (bank : PortRefresh.TraversalHeaders.HeadBank L cur (DemandRAM.oldCount X) m)
    (pitch : m (pub 1 - 1).val = (levelWords L : Word w))
    (read : ShrinkOutput.ScheduledReadbacks B i X sel base positions blocks t T m) :
    ShrinkCallHeader.Level X B.shrink sel (head : Word w) (post m ps) T (tab 0) layer
      (B.recordLimit + 2) (tab 1) := by
  have gap : head + 66 ≤ nxt := header_gap
  have hc : head + 66 ≤ 2 ^ w := PublishedHeads.level_room B base positions blocks t i.val live
    i.isLt.le fit
  have keep (j : ℕ) (hj : j ≤ 65) (outside : j < 15 ∨ 27 ≤ j) :
      post m ms (head + j) = m (head + j) :=
    tail.baseFields.outside _ (by omega) (by omega) (by omega)
  have hdr : ShrinkHeaderReads.Header i X T (tab 0) L first (post m ms) :=
    ⟨header.room, (keep 0 (by decide) (by decide)).trans header.vertices,
     (keep 1 (by decide) (by decide)).trans header.degree,
     (keep 2 (by decide) (by decide)).trans header.lanes,
     (keep 3 (by decide) (by decide)).trans header.residual,
     fun j ↦ (keep _ (by have := j.isLt; omega) (.inr (by omega))).trans (header.incidence j),
     (keep 60 (by decide) (by decide)).trans header.scratch⟩
  have firstRoom := (levelStart_mono L (Nat.zero_le cur)).trans_lt (by omega : head < 2 ^ w)
  have low := Window.lowCells (A := prog) L base rfl rfl firstRoom
  have prior : (pub 1 - 1).val < head :=
    low.2.trans_le (levelStart_mono L (Nat.zero_le cur))
  have entry : LevelFields.Entry L first pub st (post m ms) :=
    ⟨rfl, (tail.baseFields.outside _ (by omega) (by omega) (by omega)).trans pitch⟩
  have sp := ShrinkOutput.table_space B i X base positions blocks t live size fit
  have termRoom := sp.termRoom
  let N := ShrinkTermSelection.bundles X * ShrinkTermSelection.ranks (a i)
  change ShrinkInput.stop X (tab 0) + 2 * N + N * 10 < 2 ^ w at termRoom
  have word : (term).val = ShrinkInput.stop X (tab 0) + 2 * N := Nat.mod_eq_of_lt (by omega)
  have ten : (step).val = 10 := Nat.mod_eq_of_lt (by omega : (10 : ℕ) < 2 ^ w)
  have matchScore : score = ShrinkInput.termEnd X (tab 0) 10 + 2 := by
    change (term).val + ShrinkTermInputs.motifCount X * (step).val + 2 = _
    rw [word, ten, ShrinkTermSelection.motifCount_eq]
    rfl
  have afterHead : head + 66 ≤ tab 0 := by
    change head + 66 ≤ head + 66 + 6 * slotCapacity L + 0 * tableWords L
    omega
  have pastHead : head + 66 ≤ score := by
    have h := afterHead.trans (ScorePackets.start_le_term i X (tab 0) sp.termRoom)
    unfold SelectedArena.origin
    omega
  have beforeNext : score < nxt := by
    have bound := (ShrinkOutput.old_bounds i X term step).2.2.trans_le sp.selectedWithin
    have hi := tableEnd_le_nextLevel L cur (0 : Fin 6)
    rw [Nat.add_assoc] at hi
    exact bound.trans_le hi
  have sfit : score < 2 ^ w := by
    have h := PublishedHeads.level_room B base positions blocks t (i.val+1) live i.isLt fit
    omega
  have recorded : post m ms (((ShrinkInput.termEnd X (tab 0) 10 + 2 : ℕ) : Word w)).val =
      ((X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth sel).toNat :
        Word w) := by
    rw [← matchScore, Fin.val_natCast, Nat.mod_eq_of_lt sfit]
    exact (tail.baseFields.outside _ (by omega) (by omega) (by omega)).trans read.resident.chosen
  have stride : post m ms (head + 15) = ((B.recordLimit + 2 : ℕ) : Word w) :=
    tail.baseFields.payload 0
  have oldBase : post m ms (head + 14) = (layer : Word w) :=
    (keep 14 (by decide) (by decide)).trans (by simp)
  have table : post m ms (head + 61) = (tab 1 : Word w) :=
    (keep 61 (by decide) (by decide)).trans (bank.tables (1 : Fin 6))
  have planRoom : (ShrinkInput.plan X (tab 0)).stop < 2 ^ w := by
    change ShrinkInput.widthBase X (tab 0) + _ + _ + _ + _ < 2 ^ w at termRoom
    change ShrinkInput.widthBase X (tab 0) < _
    omega
  rw [tail.image]
  exact ShrinkCallHeader.Level.of_publications B i X sel T (tab 0) L first pub st (post m ms)
    layer (B.recordLimit + 2) (tab 1) hdr entry (by omega) ⟨oldBase, stride⟩ recorded (by omega)
    table planRoom tail.published.termGroup.source tail.published.dataGroup.source

include tail in
/-- The original length, copied into metadata cell 17, survives the term
and data publishers which follow that copy. -/
theorem lengthWord (n : ℕ) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (firstRoom : levelStart L 0 + 29 < 2 ^ w) (initial : m (levelStart L 0 + 29) = (n : Word w)) :
    post m ps (head + 17) = (n : Word w) :=
  (tail.metaCell _ (.inl (by omega))).trans
    (ShrinkCallABI.length_published n B base positions blocks t i.val .shrink
      (BlockMetadata.shrinkFields B i) tail.baseFields rows firstRoom initial)

end PairSimulation.ShrinkResidentHeaders

end

end VPVNP
end Computability
end OAI
