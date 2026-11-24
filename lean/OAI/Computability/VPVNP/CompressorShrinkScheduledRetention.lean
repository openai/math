import OAI.Computability.VPVNP.CompressorSourceGroups
import OAI.Computability.VPVNP.CompressorShrinkOldFieldTransfer
import OAI.Computability.VPVNP.CompressorShrinkReadbackTransfer
import OAI.Computability.VPVNP.CompressorShrinkSlotPhysicalSpace
import OAI.Computability.VPVNP.CompressorShrinkTablesPhysical
import OAI.Computability.VPVNP.CompressorSlotCopiedTables
import OAI.Computability.VPVNP.CompressorShrinkResidentFinal

/-! # Readbacks after the shrinking slot packets and the canonical incidence copy

The six copy workers write at the next level. The current level retains the
old demand and selected terms in table zero, the two slice directories in
tables one and two, the ordered endpoint table in table three and both
resident directories in table five.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkOutput

open BurstRAM BlockPlanner Compression DescriptorSpace Schedule ShrinkBlockInputs
open ShrinkSlots SlotLevel SourceOnline
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (base : Word w) (positions blocks t : ℕ)
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog prog)) base
local notation "blockStart" => Script.levelsPerBlock prog*t
local notation "old" => blockStart+i.val
local notation "nxt" => blockStart+(i.val+1)
local notation "st" => (levelStart L blockStart : Word w)
local notation "tab" => (fun j : Fin 6 => tableBase L old j)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "ids" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X (tab 0)) w
local notation "step" => (10 : Word w)
local notation "role" => SelectedArena.roleBase X term step
local notation "keepEnd" => SelectedFinish.stop X term step
local notation "sh" => levelShape (b := b i) X
local notation "h" => heads sh role (tab 3)
local notation "side" => SelectedFinish.chosen B X sel
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "dst" => packedIncidence L w nxt (actualCount sh)
local notation "hiddenBank" => ShrinkResidentLayout.layout X (tab 5)
local notation "pub" => Ports.data pt
local notation "P" => SourceOnline.Packet prog w

/-- The six public words and both ordered lists of residents of a packed site. -/
structure HiddenReadbacks (out : Memory w) : Prop where
  heads : ∀ j : Fin 6, out (levelStart L old+(30+j.val)) =
    (ShrinkResidentsPlan.headValues hiddenBank j : Word w)
  directories : ∀ maps : Bool, ShrinkHistoryRows.Directory (ShrinkResidentDirectory.oldOrder X maps)
    (ShrinkHistoryRows.packedOrder X) (ShrinkResidentDirectory.place X maps side)
    (ShrinkResidentRun.outputBank X (tab 5) maps) out

/-- All shrinking directories in the packet memory immediately following Part 8. -/
structure ScheduledReadbacks (T : IncidenceDirectory w) (out : Memory w) : Prop where
  resident : Resident B i X sel term step ids T (tab 0) (tab 2) out
  slices : SliceReadbacks B i X sel term step (tab 1) (tab 2) out
  ordered : Build.OrderedTables X (S.shrink i) side h out
  hidden : HiddenReadbacks B i X sel base positions blocks t out
  incidence : (dst).Represents Y out

/-- The six copies preserve every address outside the canonical incidence columns. -/
private theorem copy_frame (level : Fin (L).levels) (atNext : level.val = nxt) (r : TablesRun w)
    (ps : List P) (fit : finish sh h < 2^w) (room : endAddress L < 2^w)
    (capacity : actualCount sh ≤ slotCapacity L)
    (logs : ps.flatMap SourceWalk.Packet.reports = r.remainder.slots.all ++
      CopyIncidence.reports Y (directory sh h w) dst CopyIncidence.allColumns
        (after r.remainder.postWidths (eventLog r.remainder.slots.all))) :
    ∀ x, (x < incidenceStart L nxt ∨ incidenceStart L nxt+6*actualCount sh ≤ x) →
      post r.remainder.postWidths ps x = r.final x := by
  let mid := after r.remainder.postWidths (eventLog r.remainder.slots.all)
  let copies := CopyIncidence.reports Y (directory sh h w) dst CopyIncidence.allColumns mid
  have counts := next_counts X B.shrink (S.shrink i) sel
  have src := CopyIncidence.shrink_column_bounds Y sh h counts.1 counts.2 fit
  have target := CopyIncidence.packed_column_bounds Y sh L level counts.2 room capacity
  have endRoom := packed_incidence_room L room level capacity
  rw [atNext] at target endRoom
  have write := ((CopyIncidence.reports_run Y (directory sh h w) dst CopyIncidence.allColumns mid).footprint
    (fun c => (src c).2.trans fit.le) (fun c => (target c).2.trans endRoom.le)).2
  intro x outside
  have empty : ¬ CopyIncidence.ColumnCell Y dst x := by
    rintro ⟨c,lo,hi⟩
    have v : ((dst).column c).val = incidenceStart L nxt+c.val*actualCount sh ∧
      ((dst).column c).val+CopyIncidence.rows Y c ≤ incidenceStart L nxt+6*actualCount sh := target c
    omega
  have keep : after mid (eventLog copies) x = r.final x :=
    (SourceTransport.after_outside mid write empty).trans (congrFun (r.remainder.slots.final_eq r.remainder.postWidths).symm x)
  simpa only [post,logs,mid,copies,eventLog,List.flatMap_append,after,List.foldl_append] using keep

set_option maxHeartbeats 1200000 in
/-- Every cell outside the interval tables, the ordered-slot workspace and
the successor's six incidence columns agrees with the post-resident memory.
This includes all old scalar publications, selected placement, low controller
words and the entire successor header. -/
theorem scheduled_frame (I : ShrinkABSliceRecipe.Inputs) (ref m : Memory w) (cap : ℕ)
    (r : TablesRun w) (ps : List P) (live : t < blocks) (sites : X.positions ≤ positions)
    (room : endAddress L < 2^w)
    (run : CompleteTables B i X (S.shrink i) sel term step ids (tab 0) I pub st ref
      (tab 1) (tab 2) (tab 3) cap m r)
    (logs : ps.flatMap SourceWalk.Packet.reports = r.remainder.slots.all ++
      CopyIncidence.reports Y (directory sh h w) dst CopyIncidence.allColumns
        (after r.remainder.postWidths (eventLog r.remainder.slots.all))) :
    ∀ x, (x < tab 1 ∨ finish sh h ≤ x) →
      (x < incidenceStart L nxt ∨ incidenceStart L nxt+6*actualCount sh ≤ x) →
      post r.remainder.postWidths ps x = m x := by
  have nextLive : nxt < (L).levels := by
    change (S.steps+1)*t+(i.val+1) < 1+(S.steps+1)*blocks
    have upper := Nat.mul_le_mul_left (S.steps+1) live
    rw [Nat.mul_succ] at upper
    have hi := i.isLt
    omega
  let level : Fin (L).levels := ⟨old,by omega⟩
  let next : Fin (L).levels := ⟨nxt,nextLive⟩
  have space := table_space B i X base positions blocks t live sites room
  obtain ⟨_,count,_,_⟩ := ShrinkSlotCalendar.physical_space (w := w) B i X base.val positions blocks level rfl sites room
  have width : tab 2 ≤ widthBase X (term).val (step).val role (tab 2) :=
    retained_room X term (step).val role (tab 2)
  have slots : widthBase X (term).val (step).val role (tab 2) ≤ tab 3 :=
    (width_le_slots (b := b i) X term (step).val role (tab 2)).trans space.slotAfter
  have last : tab 3 ≤ finish sh h := by
    unfold finish widthHead inHead outHead inverseBaseHead stopAddress shiftsHead targetsHead inverseHead rowsHead heads
    dsimp only
    omega
  intro x outside copy
  have native := copy_frame B i X sel base positions blocks t next rfl r ps space.slotRoom room count logs x copy
  apply native.trans
  apply (run.remainder.construction.frame x (outside.imp
    (fun hx => hx.trans_le (((Nat.le_add_right _ _).trans space.widthAfter).trans width)) id)).trans
  exact run.abFrame x (outside.imp id (fun hx => space.widthAfter.trans (width.trans (slots.trans (last.trans hx)))))

set_option maxHeartbeats 1800000 in
/-- A three-table run followed by its actual slot packets retains the current
level's selected tables and its two previously published resident directories. -/
theorem scheduled_readbacks (T : IncidenceDirectory w) (I : ShrinkABSliceRecipe.Inputs)
    (ref m : Memory w) (cap : ℕ) (r : TablesRun w) (ps : List P)
    (live : t < blocks) (sites : X.positions ≤ positions) (room : endAddress L < 2^w)
    (resident : Resident B i X sel term step ids T (tab 0) (tab 2) m)
    (hidden : HiddenReadbacks B i X sel base positions blocks t m)
    (run : CompleteTables B i X (S.shrink i) sel term step ids (tab 0) I pub st ref
      (tab 1) (tab 2) (tab 3) cap m r)
    (logs : ps.flatMap SourceWalk.Packet.reports = r.remainder.slots.all ++
      CopyIncidence.reports Y (directory sh h w) dst CopyIncidence.allColumns
        (after r.remainder.postWidths (eventLog r.remainder.slots.all)))
    (incidence : (dst).Represents Y (post r.remainder.postWidths ps)) :
    ScheduledReadbacks B i X sel base positions blocks t T (post r.remainder.postWidths ps) := by
  have nextBound : nxt < (L).levels := by
    change (S.steps+1)*t+(i.val+1) < 1+(S.steps+1)*blocks
    have e := Nat.mul_le_mul_left (S.steps+1) live
    rw [Nat.mul_succ] at e
    have hi := i.isLt
    omega
  let level : Fin (L).levels := ⟨old,by omega⟩
  let next : Fin (L).levels := ⟨nxt,nextBound⟩
  have space := table_space B i X base positions blocks t live sites room
  obtain ⟨sp,count,_,width⟩ := ShrinkSlotCalendar.physical_space B i X base.val positions blocks level rfl sites room
  obtain ⟨_,endTerm,endSelected,_,_,_,endSlots,_,endResidents⟩ :=
    BlockLevelFit.shrink (w := w) B base.val positions blocks level rfl i X sites room
  have oldNext : level.val+1 = nxt := by dsimp [level]; omega
  have nextHead : levelStart L (level.val+1) ≤ incidenceStart L nxt :=
    oldNext ▸ Nat.le_add_right _ _
  have slotEnd := endSlots.next.trans nextHead
  have hiddenEnd := endResidents.next.trans nextHead
  have earlier (x : ℕ) (hx : x < incidenceStart L nxt) :=
    copy_frame B i X sel base positions blocks t next rfl r ps endSlots.word room count logs x (.inl hx)
  have oldFrame := scheduled_frame B i X sel base positions blocks t I ref m cap r ps live sites room run logs
  have ten : 10 < 2^w := by
    have hv : levelStart L old+66 ≤ tab 0 := by
      change levelStart L old+66 ≤ levelStart L old+66+6*slotCapacity L+0*tableWords L
      omega
    have htab : tab 0 < 2^w := tableStop_lt L level (0 : Fin 6) (Nat.zero_le _) room
    omega
  have stepVal : (step).val=10 := Nat.mod_eq_of_lt ten
  have termRoom : ShrinkInput.termEnd X (tab 0) (step).val < 2^w := stepVal ▸ endTerm.word
  have slotStartBound : tab 3 ≤ incidenceStart L nxt :=
    (Nat.le_add_right _ _).trans ((tableEnd_le_nextLevel L level (3 : Fin 6)).trans nextHead)
  have selectedKeep (x : ℕ) (hx : x<keepEnd) : post r.remainder.postWidths ps x = m x :=
    oldFrame x (.inl (hx.trans_le space.abAfter)) (.inl (hx.trans_le (endSelected.next.trans nextHead)))
  have packed := resident.below B i X sel T (tab 0) endTerm.word ten selectedKeep
  have sf := run.slice_transfer (T := T) termRoom space.fresh space.widthAfter space.slotAfter
    (tableStop_lt L level (3 : Fin 6) (Nat.zero_le _) room) stepVal.ge space.packedRoom
    (fun x hx => earlier x (hx.trans_le slotStartBound))
  rw [← width] at sp
  let native := run.remainder.construction
  have sorted := Build.retained_tables X B.shrink (S.shrink i) sel h _ r.remainder.postWidths r.remainder.slots
    sp native.inputRoles native.slots
  have kept := Build.retained_after_copy X B.shrink (S.shrink i) sel h r.remainder.postWidths r.remainder.slots L
    next room endSlots.word count sorted (.inl slotEnd)
  refine ⟨packed,sf,?_,⟨?_,?_⟩,incidence⟩
  · rw [post,logs]
    exact kept
  · intro j
    have start : levelStart L old+66 ≤ tab 1 := by
      change levelStart L old+66 ≤ levelStart L old+66+6*slotCapacity L+1*tableWords L
      omega
    have lo : levelStart L old+(30+j.val) < tab 1 := by have := j.isLt; omega
    have before := (Nat.le_add_right (tab 1) (tableWords L)).trans ((tableEnd_le_nextLevel L level (1 : Fin 6)).trans nextHead)
    exact (oldFrame _ (.inl lo) (.inl (lo.trans_le before))).trans (hidden.heads j)
  · intro maps
    apply ShrinkResidentRun.transfer X (tab 5) side maps (hidden.directories maps) endResidents.word
    intro x lo hi
    have slotBefore := endSlots.within.trans (tableEnd_le_tableBase L level (show (3 : Fin 6) < 5 by decide))
    exact oldFrame x (.inr (slotBefore.trans lo)) (.inl (hi.trans_le hiddenEnd))

end CompressorRecords.ShrinkOutput

end

end VPVNP
end Computability
end OAI
