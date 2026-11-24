import OAI.Computability.VPVNP.CompressorShrinkScheduledTail
import OAI.Computability.VPVNP.CompressorShrinkScheduledRetention
import OAI.Computability.VPVNP.CompressorShrinkSliceInterval
import OAI.Computability.VPVNP.CompressorCurrentGraph

/-! # Physical shrinking readbacks after the terminal publication rows

Parts nine through eleven publish the DFS metadata and all term and slice
pointers. The six header words for the resident directories and every old
data table retain their values. The successor incidence arrays begin after
its header and also retain their six packed columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledTail

open BurstRAM Compression BlockPlanner DescriptorSpace Schedule ShrinkBlockInputs
open ShrinkSlots SlotLevel SourceOnline ShrinkOutput
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {w g : ℕ} {i : Fin S.steps} {X : State (a i) (packingLaneBits (a i) g)}
variable {base : Word w} {positions blocks t cap : ℕ} {m : Memory w}
local notation "prog" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "firstLevel" => Script.levelsPerBlock prog*t
local notation "old" => firstLevel+i.val
local notation "nxt" => firstLevel+(i.val+1)
local notation "oldHead" => levelStart L old
local notation "nextHead" => levelStart L nxt
local notation "tab" => (fun j : Fin 6 => tableBase L old j)
local notation "term" => ShrinkInput.termHead (w := w) X (tab 0)
local notation "step" => (10 : Word w)
local notation "keepEnd" => SelectedFinish.stop X term step
local notation "sh" => levelShape (b := b i) X
variable {ms ps : List (SourceOnline.Packet (BlockProgram.script B) w)}

private theorem table_after (j : Fin 6) : oldHead+66 ≤ tab j := by
  change oldHead+66 ≤ oldHead+66+6*slotCapacity L+j.val*tableWords L
  omega

private theorem table_before (j : Fin 6) : tab j+tableWords L ≤ nextHead := by
  have next : old+1=nxt := by omega
  rw [← next]
  exact tableEnd_le_nextLevel L old j

theorem Result.table_data (tail : ShrinkScheduledTail.Result B base positions blocks t cap i X m ms ps) (j : Fin 6) (x : ℕ) (lo : tab j ≤ x) (hi : x < tab j+tableWords L) : post m ps x=m x := by
  have floor : oldHead+66 ≤ tab j := table_after j
  have top : tab j+tableWords L ≤ nextHead := table_before j
  exact tail.old_data x (by omega) (hi.trans_le top)

/-- The old resident head words occupy the gap between the metadata and
the term-pointer publication ranges. -/
theorem Result.residentHeads (tail : ShrinkScheduledTail.Result B base positions blocks t cap i X m ms ps) (j : Fin 6) : post m ps (oldHead+(30+j.val)) = m (oldHead+(30+j.val)) := by
  have sep : oldHead+66 ≤ nextHead :=
    (table_after (B := B) (base := base) (positions := positions) (blocks := blocks) (t := t) (i := i) 0).trans
      ((Nat.le_add_right ..).trans (table_before 0))
  have := j.isLt
  apply tail.outside <;> omega

private theorem levels (live : t < blocks) : old < (L).levels ∧ nxt < (L).levels := by
  have h := Nat.mul_le_mul_left (S.steps+1) live
  rw [Nat.mul_succ] at h
  have hi := i.isLt
  change (S.steps+1)*t+i.val < 1+(S.steps+1)*blocks ∧ (S.steps+1)*t+(i.val+1) < 1+(S.steps+1)*blocks
  omega

/-- The selected native placement bank still contains all four actual
columns for every old vertex. The word-base addition is within table zero. -/
theorem Result.placement (tail : ShrinkScheduledTail.Result B base positions blocks t cap i X m ms ps) (sel : Bool) (p₀ : Fin 14 → Word w) (bit : Word w)
    (before : ShrinkRAM.PlacementColumns X.slots X.baseIndex (SelectedArena.shrinkWords X term step p₀ bit) sel m)
    (live : t < blocks) (size : X.positions ≤ positions) (room : endAddress L < 2^w) :
    ShrinkRAM.PlacementColumns X.slots X.baseIndex (SelectedArena.shrinkWords X term step p₀ bit) sel (post m ps) := by
  let level : Fin (L).levels := ⟨old,(levels (B := B) (base := base) (positions := positions) (i := i) live).1⟩
  have space := table_space B i X base positions blocks t live size room
  have startLe := ScorePackets.start_le_term i X (tab 0) space.termRoom
  have endFit := tableStop_lt L level (0 : Fin 6) le_rfl room
  have last : keepEnd ≤ tab 0+tableWords L := space.selectedWithin
  have within : SelectedArena.endAddr X term step ≤ keepEnd := by
    unfold SelectedFinish.stop SelectedFinish.rowStart SelectedFinish.countStart
    omega
  have fit : SelectedArena.Fits X term step := within.trans_lt (last.trans_lt endFit)
  let p := SelectedArena.shrinkWords X term step p₀ bit
  let place := SelectedArena.placementBase X term step
  let role := SelectedArena.roleBase X term step
  have placeLo : tab 0 ≤ place := by
    change tab 0 ≤ (term).val+SelectedArena.motifs X*(step).val+3
    omega
  have roleEnd : role ≤ keepEnd := (Nat.le_add_right ..).trans within
  constructor
  intro x _
  let idx := ShrinkRAM.word w (Shrink.oldNumber X.baseIndex x)
  have jBound : idx.val < SelectedArena.positions X := by
    change (Shrink.oldNumber X.baseIndex x) % 2^w < _
    rw [← Shrink.oldIndex_val]; exact (Nat.mod_le ..).trans_lt (Fin.isLt _)
  have same (j : Fin 4) : post m ps (ShrinkRAM.outAddr p j idx) = m (ShrinkRAM.outAddr p j idx) := by
    have head := SelectedArena.output_column X term step p₀ bit fit j
    change (p (j.natAdd 10)).val = place+j.val*SelectedArena.positions X at head
    have sep := Nat.mul_le_mul_right (SelectedArena.positions X) j.isLt
    rw [Nat.succ_mul] at sep
    have top : place+j.val*SelectedArena.positions X+idx.val < role := by
      change place+j.val*SelectedArena.positions X+idx.val < place+4*SelectedArena.positions X
      omega
    have addr : ShrinkRAM.outAddr p j idx = place+j.val*SelectedArena.positions X+idx.val := by
      rw [ShrinkRAM.outAddr,Fin.val_add,head,Nat.mod_eq_of_lt (top.trans_le (roleEnd.trans (last.trans endFit.le)))]
    exact tail.table_data 0 _ (addr ▸ placeLo.trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))
      (addr ▸ top.trans_le (roleEnd.trans last))
  change (((post m ps) (ShrinkRAM.outAddr p 0 idx)).val,((post m ps) (ShrinkRAM.outAddr p 1 idx)).val,
    ((post m ps) (ShrinkRAM.outAddr p 2 idx)).val,((post m ps) (ShrinkRAM.outAddr p 3 idx)).val) = _
  rw [same 0,same 1,same 2,same 3]
  exact before.atSite x

/-- Every selected and computed table used by the history reader survives
on the actual post-memory. The word and allocation bounds are derived from
the same fitted block as the native construction. -/
theorem Result.readbacks (tail : ShrinkScheduledTail.Result B base positions blocks t cap i X m ms ps) (sel : SelectedScore.Selection B X) (T : IncidenceDirectory w)
    (before : ScheduledReadbacks B i X sel base positions blocks t T m)
    (live : t < blocks) (size : X.positions ≤ positions) (room : endAddress L < 2^w) :
    ScheduledReadbacks B i X sel base positions blocks t T (post m ps) := by
  obtain ⟨liveOld,liveNext⟩ := levels (B := B) (base := base) (positions := positions) (i := i) live
  let level : Fin (L).levels := ⟨old,liveOld⟩
  let next : Fin (L).levels := ⟨nxt,liveNext⟩
  have space := table_space B i X base positions blocks t live size room
  obtain ⟨_,endTerm,endSelected,_,_,_,endSlots,_,endResidents⟩ :=
    BlockLevelFit.shrink (w := w) B base.val positions blocks level rfl i X size room
  have lo : oldHead+66 ≤ tab 0 := table_after 0
  have ten : 10 < 2^w := by
    have h : tab 0 < 2^w := tableStop_lt L level (0 : Fin 6) (Nat.zero_le _) room
    omega
  have wide : (step).val=10 := Nat.mod_eq_of_lt ten
  have sliced := before.slices.transfer_interval (T := T) (start := tab 0) (S.shrink i)
    (show ShrinkInput.termEnd X (tab 0) (step).val < 2^w by rw [wide]; exact endTerm.word)
    space.fresh space.widthAfter space.slotAfter (tableStop_lt L level (3 : Fin 6) (Nat.zero_le _) room)
    wide.ge space.packedRoom (post := post m ps) (fun x low high => tail.old_data x
      ((show oldHead+54 ≤ tab 1 by have h : oldHead+66 ≤ tab 1 := table_after 1; omega).trans low)
      (high.trans_le ((Nat.le_add_right ..).trans (table_before 3))))
  have ordered := before.ordered.transfer_interval (post := post m ps)
    (fun x low high => tail.table_data 3 x low (high.trans_le endSlots.within))
  refine ⟨before.resident.interval B i X sel T (tab 0) endTerm.word ten endSelected.word.le
    (fun x low high => tail.table_data 0 x low (high.trans_le endSelected.within)),
    sliced,ordered,⟨fun j => (tail.residentHeads j).trans (before.hidden.heads j),?_⟩,?_⟩
  · intro maps
    exact ShrinkResidentRun.transfer X (tab 5) (SelectedFinish.chosen B X sel) maps
      (before.hidden.directories maps) endResidents.word
      (fun x low high => tail.table_data 5 x low (high.trans_le endResidents.within))
  · let Y := X.shrinkNext B.shrink (S.shrink i) sel
    have count := (ShrinkSlotCalendar.physical_space B i X base.val positions blocks level rfl size room).2.1
    have exactCount := (next_counts X B.shrink (S.shrink i) sel).2
    have input := before.incidence
    rw [← exactCount] at input ⊢
    apply CurrentGraph.incidence_keep L next Y room (exactCount.le.trans count) input
    intro x low _
    apply tail.next_data
    change nextHead+66 ≤ x at low
    omega

end CompressorRecords.ShrinkScheduledTail

end

end VPVNP
end Computability
end OAI
