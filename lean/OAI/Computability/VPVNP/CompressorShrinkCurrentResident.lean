import OAI.Computability.VPVNP.CompressorShrinkHistoryDirectory
import OAI.Computability.VPVNP.CompressorShrinkScheduledTail
import OAI.Computability.VPVNP.CompressorBlockMetadataShrinkReadback
import OAI.Computability.VPVNP.CompressorBlockMetadataGraphFrame
import OAI.Computability.VPVNP.CompressorSelectedDirectoryEmission
import OAI.Computability.VPVNP.CompressorCurrentResident

/-!
# The resident boundary after a shrinking pass

The three final publication groups install the old-level directory operands
and successor DFS fields. Their writes leave the canonical successor
incidence columns, previously recorded levels and original cursor frame
available to the next calendar interval.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledTail

open BurstRAM Compression DescriptorSpace BlockPlanner SourceOnline BlockHeaderRun
open SelectedDirectoryHistory PairSimulation.TraversalRows PairSimulation.TraversalRoles
open PairSimulation.LocalHistory
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
variable {f : B.Entry → R} {hf : B.IsSolution f} {i : Fin S.steps} {w g : ℕ}
variable {X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g)}
variable {sel : SelectedScore.Selection B X} {tape : List Bool}
variable {workspace : Word w} {positions blocks t cap n : ℕ} {m : Memory w}
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B workspace.val positions blocks
local notation "first" => Script.levelsPerBlock scr * t
local notation "cur" => first + i.val
local notation "head" => levelStart L cur
local notation "nxt" => levelStart L (cur + 1)
local notation "start" => tableBase L cur (0 : Fin 6)
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "pt" => Workspace.ports (Schedule.arity (Script.catalog scr)) workspace
local notation "v" => shrinkLevel B f hf i X sel tape
variable {ms ps : List (Packet (BlockProgram.script B) w)}
variable (r : Result (g := g) B workspace positions blocks t cap i X m ms ps)

private theorem room_between : head + 66 ≤ nxt := by
  have size : levelHeaderWords L = 66 := rfl
  simp only [levelStart, Nat.succ_mul, levelWords, size]
  omega

/-- The exact operand vector at offsets 21, 22, 24, 25 and 26 agrees
with the bank used to collect this pass's child directory. -/
def Result.emission (T : IncidenceDirectory w)
    (d : LevelDirectory v m nxt) (shr : Fin 14 → Word w)
    (bank : d.pub = SelectedFinish.params X term 10 shr) (lower : head + 54 ≤ (d.pub 1).val)
    (header : ShrinkHeaderReads.Header i X T start L first m)
    (pitch : m ((pt).directory - 1).val = (levelWords L : Word w))
    (termFit : ShrinkInput.termEnd X start 10 < 2 ^ w)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (length : m (levelStart L 0 + 29) = (n : Word w)) :
    Emission L cur v m (post m ps) := by
  have oldCount : (v).input.positions = ShrinkPreimages.oldCount X := by
    change X.positions = _
    rw [State.positions, Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv _),
      Fintype.card_fin]
  have p : BlockMetadata.Published B workspace positions blocks t i.val
    (BlockMetadata.producingRole (v).origin)
      (BlockMetadata.shrinkFields B i) m (v).input.positions
        (ms.flatMap SourceWalk.Packet.reports) :=
    oldCount.symm ▸ r.baseFields
  have payload := r.baseFields.shrink_payload B i X T start workspace positions blocks t
    header ⟨rfl, pitch⟩ termFit rows n length
  have values : PlacementWords (fun j => post m ms (head + 15 + j.val)) d.pub := by
    rw [bank]
    exact ⟨payload 6, payload 7, payload 9, payload 10, payload 11⟩
  let emitted := Emission.ofPublished p d (by omega) values
  have gap : head + 66 ≤ nxt := room_between
  have pubEq : emitted.dir.pub = d.pub := by
    unfold emitted Emission.ofPublished
    rcases values with ⟨_, _, _, _, _⟩
    rfl
  apply emitted.transfer
  · intro x hx
    rw [pubEq] at hx
    have lo := (Directory.cells_interval d hx).1
    exact (r.metaCell x (.inr (lower.trans lo))).symm
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    exact r.metaCell _ (.inl (by omega))
  · intro o _
    exact r.metaCell _ (.inr (by omega))

include r

/-- The final 21 packets retain the scalar and pointer fields of the new
graph together with the first-level counts and original eight inputs. -/
theorem Result.graph_frame (x : ℕ)
    (hx : CurrentGraph.graphCell L (cur + 1) x ∨ CurrentGraph.startupCell L x
      ∨ CurrentGraph.frameCell L x) :
    post m ps x = m x := by
  have floor := levelStart_mono L (Nat.zero_le cur)
  have gap : head + 66 ≤ nxt := room_between
  have tail : x < head + 36 ∨ head + 54 ≤ x := by
    rcases hx with g | s | h
    · rcases g with h | h <;> exact .inr (by omega)
    · obtain ⟨j, hj, rfl⟩ := s
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      exact .inl (by omega)
    · unfold CurrentGraph.frameCell at h
      exact .inl (by omega)
  apply (r.metaCell x tail).trans
  rcases hx with h|h|h
  · exact r.baseFields.graphFrame x (.inr (.inl h))
  · exact r.baseFields.graphFrame x (.inr (.inr h))
  · exact r.baseFields.cursorFrame x h

/-- Extend the selected history in the native post-memory. The pre-tail
frame permits writes to the six old-level resident heads at offsets 30–35
and to the new incidence columns installed by the slot stage. -/
theorem Result.advance {initial : TaggedLayer} {initialFrame : Fin 8 → Word w}
    {past : List (SelectedLevel B f hf)}
    {before : Memory w} (old new : Fin (L).levels) (atOld : old.val = cur)
    (next : old.val + 1 = new.val)
    (index : past.length = old.val)
    (stored : CurrentResident.resident B f hf initial L (endAddress L) n initialFrame past X before)
    (sub : Substep v L old new (by change 6 ≤ 54; decide) before)
    (fit : endAddress L < 2 ^ w)
    (slots : IncidenceDirectory.slotCount ((v).pass.next (v).term) ≤ slotCapacity L)
    (columns : (packedIncidence L w new
      (IncidenceDirectory.slotCount ((v).pass.next (v).term))).Represents
      ((v).pass.next (v).term) m)
    (emitted : Emission L cur v m (post m ps))
    (throughSlots : ∀ x, levelStart L 0 ≤ x → x < head + 30 ∨ CurrentGraph.graphCell L (cur + 1) x →
      m x = finalMemory v L old new before x) :
    CurrentResident.resident B f hf initial L (endAddress L) n initialFrame (past ++ [v])
      ((v).pass.next (v).term) (post m ps) := by
  have newAt : new.val = cur + 1 := by omega
  have ix : past.length = cur := index.trans atOld
  have gap : head + 66 ≤ nxt := room_between
  have floor := levelStart_mono L (Nat.zero_le cur)
  have nextEq : levelStart L (first + (i.val + 1)) = nxt := by rw [Nat.add_assoc]
  have headEq : levelStart L old = head := congrArg _ atOld
  have newEq : levelStart L new = nxt := congrArg _ newAt
  have keepOld (j : ℕ) (hj : j = 14 ∨ j = 27) : m (head + j) = before (head + j) := by
    apply (throughSlots _ (by omega) (.inl (by omega))).trans
    apply sub.outside <;> first | exact .inr (by omega) | exact .inl (by omega)
  apply CurrentResident.append_substep old new index next stored (by change 30 ≤ 54; decide) fit sub
  · rw [ix]
    exact emitted.prepend (keepOld 14 (.inl rfl)) (keepOld 27 (.inr rfl))
  · apply CurrentGraph.incidence_keep L new _ fit slots columns
    intro x lo _
    have h : incidenceStart L new = nxt + 66 := by rw [newAt]; rfl
    exact r.next_data x (by omega)
  · intro x hx
    rw [newAt] at hx
    apply (r.graph_frame x hx).trans
    rcases hx with h|⟨j, hj, rfl⟩|h
    · have ge : nxt ≤ x := by rcases h with h|h <;> omega
      exact throughSlots x (by omega) (.inr h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      exact throughSlots _ (by omega) (.inl (by omega))
    · unfold CurrentGraph.frameCell at h
      exact throughSlots _ (by omega) (.inl (by omega))
  · intro x lo hi
    rw [ix] at hi
    have floor' : levelStart L 0 ≤ x := by
      simpa only [levelStart, Nat.zero_mul, Nat.add_zero] using lo
    exact (r.earlier x hi).trans
      ((throughSlots x floor' (.inl (by omega))).trans (sub.before v next x (by omega)))

end CompressorRecords.ShrinkScheduledTail

end

end VPVNP
end Computability
end OAI
