import OAI.Computability.VPVNP.CompressorShrinkSlotPacketGroup
import OAI.Computability.VPVNP.CompressorShrinkSlotWindow
import OAI.Computability.VPVNP.CompressorShrinkOutputAccess

/-! # Memory outside the installed shrinking slot group

The selected construction writes in its slot workspace, then copies six
incidence columns to the next level. The same frame holds for the global
packet list whenever its concatenated worker reports are those two runs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlotCalendar

open BurstRAM BlockPlanner DescriptorSpace SourceTransport Compression ShrinkSlots SlotLevel

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
variable (sel : X.ShrinkSelection B.shrink) (term : Word w) (stride role retained slotStart : ℕ)
variable (L : Layout) (level : Fin L.levels)
local notation "sh" => levelShape (b := ShrinkBlockInputs.b i) X
local notation "heads" => ShrinkOutput.heads sh role slotStart
local notation "slotEnd" => finish sh heads
local notation "count" => actualCount sh
local notation "copyBase" => incidenceStart L level

/-- Every cell outside both physical write intervals retains its value from
the input memory of the slot group. -/
theorem packet_group_frame_of_space {initial raw : Memory w} {r : Build.Construction w}
    (c : ShrinkOutput.Constructed X B.shrink (S.shrink i) sel term stride role retained initial raw r slotStart)
    (sp : Build.Space sh heads (ShrinkOutput.widthBase X term.val stride role retained) w)
    (room : endAddress L < 2^w) (capacity : count ≤ slotCapacity L)
    (apart : slotEnd ≤ copyBase ∨ copyBase+6*count ≤ targetsHead sh heads)
    (ps : List (SourceOnline.Packet (BlockProgram.script B) w)) :
    let Y := X.shrinkNext B.shrink (S.shrink i) sel
    let copies := CopyIncidence.reports Y (directory sh heads w) (packedIncidence L w level count)
      CopyIncidence.allColumns (after raw (eventLog r.all))
    ps.flatMap SourceWalk.Packet.reports = r.all++copies →
    ∀ x, (x < slotStart ∨ slotEnd ≤ x) → (x < copyBase ∨ copyBase+6*count ≤ x) →
      SourceOnline.post raw ps x = raw x := by
  intro Y copies reports x outsideSlot outsideCopy
  have walk := (c.sources_of_space X B.shrink (S.shrink i) sel term stride role retained slotStart sp
    (plan B i) L level room capacity apart).1
  rw [SourceOnline.post,reports]
  apply (walk.with_invariant (I := fun m ↦ m x = raw x) rfl ?_).2
  intro j mem logs hs input
  refine (after_outside mem hs.2.2 ?_).trans input
  rintro (slot | copy) <;> omega

/-- Specialization to the separate allocation certified by the selected width sweep. -/
theorem packet_group_frame {initial raw : Memory w} {r : Build.Construction w}
    (c : ShrinkOutput.Constructed X B.shrink (S.shrink i) sel term stride role retained initial raw r slotStart)
    (hw : ShrinkOutput.FitsWords (b := ShrinkBlockInputs.b i) X B.shrink term stride role retained)
    (gap : (ShrinkOutput.slotHeads (b := ShrinkBlockInputs.b i) X term.val stride role retained).role ≤ slotStart)
    (endFit : slotEnd < 2^w) (room : endAddress L < 2^w) (capacity : count ≤ slotCapacity L)
    (apart : slotEnd ≤ copyBase ∨ copyBase+6*count ≤ targetsHead sh heads)
    (ps : List (SourceOnline.Packet (BlockProgram.script B) w)) :
    let Y := X.shrinkNext B.shrink (S.shrink i) sel
    let copies := CopyIncidence.reports Y (directory sh heads w) (packedIncidence L w level count)
      CopyIncidence.allColumns (after raw (eventLog r.all))
    ps.flatMap SourceWalk.Packet.reports = r.all++copies →
    ∀ x, (x < slotStart ∨ slotEnd ≤ x) → (x < copyBase ∨ copyBase+6*count ≤ x) →
      SourceOnline.post raw ps x = raw x :=
  packet_group_frame_of_space B i X sel term stride role retained slotStart L level c
    (hw.slot_space_at X B.shrink term stride role retained slotStart gap endFit) room capacity apart ps

end CompressorRecords.ShrinkSlotCalendar

end VPVNP
end Computability
end OAI
