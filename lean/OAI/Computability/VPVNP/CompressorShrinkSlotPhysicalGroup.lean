import OAI.Computability.VPVNP.CompressorShrinkSlotOnlineGroup
import OAI.Computability.VPVNP.CompressorShrinkSlotGroupIndices
import OAI.Computability.VPVNP.CompressorShrinkSlotGroupFrame
import OAI.Computability.VPVNP.CompressorShrinkSlotPacketSpace
import OAI.Computability.VPVNP.CompressorShrinkSlotPhysicalSpace
import OAI.Computability.VPVNP.CompressorShrinkSlotReference

/-!
# Executing the slot group of an allocated shrinking block

The preceding width reports fix the input memory for these 22 packets.
The selected score, level headers and published column addresses determine
each launch. The six final copies populate the next level's incidence rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkSlotCalendar

open BurstRAM BlockPlanner Compression DescriptorSpace PhaseRecipe Schedule ShrinkBlockInputs
open ShrinkSlots SlotLevel
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (base : Word w) (positions blocks t : ℕ)
local notation "A" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog A)) base
local notation "pub" => Schedule.Ports.data pt
local notation "first" => Script.levelsPerBlock A*t
local notation "old" => first+i.val
local notation "next" => first+(i.val+1)
local notation "st" => (levelStart L first : Word w)
local notation "head" => (fun j : Fin 6 => tableBase L old j)
local notation "term" => ShrinkInput.termHead (w := w) X (head 0)
local notation "step" => (10 : Word w)
local notation "role" => SelectedArena.roleBase X term step
local notation "s" => levelShape (b := b i) X
local notation "h" => ShrinkOutput.heads s role (head 3)
local notation "dst" => packedIncidence L w next (actualCount s)
local notation "W" => BlockGroups.shrink B i 8

set_option maxHeartbeats 1500000 in
/-- The selected slots and canonical copies occupy the actual eighth
shrinking part. The reports agree with the output of the preceding
construction, including its post-width memory. -/
theorem physical_group (T : IncidenceDirectory w) (sel : SelectedScore.Selection B X)
    (abs : Word w) (I : ShrinkABSliceRecipe.Inputs) (ref m : Memory w) (fuel : ℕ) (r : ShrinkOutput.TablesRun w)
    (live : t < blocks) (sitesFit : X.positions ≤ positions) (room : endAddress L < 2^w)
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (header : ShrinkHeaderReads.Header i X T (head 0) L first m) (oldRows : ℕ)
    (currentHeads : PortRefresh.TraversalHeaders.HeadBank L old oldRows m)
    (nextHeads : PortRefresh.TraversalHeaders.HeadBank L next (actualCount s) m)
    (resident : ShrinkOutput.Resident B i X sel term step abs T (head 0) (head 2) m)
    (run : ShrinkOutput.CompleteTables B i X (S.shrink i) sel term step abs (head 0)
      I pub st ref (head 1) (head 2) (head 3) fuel m r)
    (cap : ℕ) (clock : SourceOnline.scanCap A 49 ≤ cap) :
    let Y := X.shrinkNext B.shrink (S.shrink i) sel
    let raw := r.remainder.postWidths
    let native := r.remainder.slots
    let copies := CopyIncidence.reports Y (directory s h w) dst CopyIncidence.allColumns
      (after raw (eventLog native.all))
    ∃ ps : List (SourceOnline.Packet A w),
      SourceOnline.Group A L base cap ((A).initial.length+t*(A).block.length+(W).before.length)
        (directoryRows L) raw ps ∧
      ps.map (fun p => p.stage.phase) = (W).indices ∧
      ps.flatMap SourceWalk.Packet.reports = native.all++copies ∧
      (dst).Represents Y (SourceOnline.post raw ps) ∧
      ∀ x, (x < head 3 ∨ finish s h ≤ x) →
        (x < incidenceStart L next ∨ incidenceStart L next+6*actualCount s ≤ x) →
        SourceOnline.post raw ps x = raw x := by
  intro Y raw native copies
  have currentLive : old < (L).levels := by
    have many := Nat.mul_le_mul_left (S.steps+1) live
    rw [Nat.mul_succ] at many
    have hi := i.isLt
    change (S.steps+1)*t+i.val < 1+(S.steps+1)*blocks
    omega
  have nextLive : next < (L).levels := by
    have many := Nat.mul_le_mul_left (S.steps+1) live
    rw [Nat.mul_succ] at many
    have hi := i.isLt
    change (S.steps+1)*t+(i.val+1) < 1+(S.steps+1)*blocks
    omega
  let cur : Fin (L).levels := ⟨old,currentLive⟩
  let nxt : Fin (L).levels := ⟨next,nextLive⟩
  have geometry : Boundary A L base t i.val role (head 3) (finish s h) (incidenceStart L next)
      (SelectedArena.origin X term step+2) := physical_boundary B i X base positions blocks t live sitesFit room
  obtain ⟨sp,count,_,width⟩ := physical_space B i X base.val positions blocks cur rfl sitesFit room
  have size : X.positions*ShrinkLevelSpace.tableFactor S ≤ tableWords L := by
    change _ ≤ positions*(L).shape.slots*(L).shape.fields
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul sitesFit (BlockProgram.field_rates B base.val positions blocks).1
  have bank0 : head 0 = arrayBase L old := by
    change arrayBase L old+0*tableWords L = _
    rw [Nat.zero_mul,Nat.add_zero]
  have bank1 : head 1 = head 0+tableWords L := by
    change arrayBase L old+1*tableWords L = head 0+tableWords L
    rw [bank0,one_mul]
  have bank2 : head 2 = head 0+2*tableWords L := by rw [bank0]; rfl
  have bank3 : head 3 = head 0+3*tableWords L := by rw [bank0]; rfl
  have headerLow : levelStart L old+66 ≤ head 0 := by rw [bank0]; exact Nat.le_add_right ..
  have dataLow := (levelStart_mono L (Nat.zero_le old)).trans ((Nat.le_add_right _ 66).trans headerLow)
  have lowPitch := geometry.pitchBefore.trans_le dataLow
  have lowRows := geometry.rowsBefore.trans_le dataLow
  have entry : LevelFields.Entry L first pub st m := ⟨rfl,pitch⟩
  obtain ⟨values,low,_⟩ := values_at_slots_framed B i X T (head 0) L first pub st m sel (S.shrink i)
    abs I ref (head 1) (head 2) (head 3) fuel r cur nxt rfl rfl oldRows rfl rfl bank0 bank1 bank2
    bank3 size room lowPitch header entry currentHeads nextHeads resident run
  have ends := ShrinkLevelSpace.packed_ends S i X (head 0) (head 1) (head 2) (head 3) w
  have limit := tableStop_lt L cur (0 : Fin 6) size room
  have postHeader := header.keep_below (by omega : levelStart L old+60 < head 0) low
  have postPitch := (low _ lowPitch).trans pitch
  have postEntry : LevelFields.Entry L first pub st raw := ⟨rfl,postPitch⟩
  have score := (reference_heads B i X T (head 0) L first pub st raw postHeader postEntry
    (ends.2.1.trans_lt limit) (ends.2.2.1.trans limit.le)).2.1
  rw [← score] at geometry
  change Build.Space s h (head 2) w at sp
  change ShrinkOutput.widthBase X (term).val (step).val role (head 2) = head 2 at width
  rw [← width] at sp values
  obtain ⟨ps,labels,reports,group,rep⟩ := packet_group B i X sel term (step).val role (head 2)
    (head 3) L base t nxt run.remainder.construction sp room count ((low _ lowRows).trans rows)
    postPitch values geometry cap clock
  rw [part_eight_before] at group
  refine ⟨ps,group,?_,reports,rep,?_⟩
  · have phases := congrArg (List.map (fun (v : SourceOnline.Visit A w) => v.phase)) labels
    simpa only [List.map_map,Function.comp_def] using phases.trans (part_eight_indices B i _ _ _ _ _)
  · apply packet_group_frame_of_space B i X sel term (step).val role (head 2) (head 3) L nxt
      run.remainder.construction sp room count _ ps reports
    exact .inl (geometry.slotBefore.trans ((Nat.le_add_right _ 66).trans geometry.headerBefore))

end CompressorRecords.ShrinkSlotCalendar

end

end VPVNP
end Computability
end OAI
