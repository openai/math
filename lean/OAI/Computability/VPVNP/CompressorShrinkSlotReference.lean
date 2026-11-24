import OAI.Computability.VPVNP.CompressorShrinkSlotLaunch
import OAI.Computability.VPVNP.CompressorShrinkSlotFrame
import OAI.Computability.VPVNP.CompressorShrinkSlotFixedOperands
import OAI.Computability.VPVNP.CompressorShrinkSelectedReadback
import OAI.Computability.VPVNP.CompressorShrinkBranchResident
import OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders

/-!
# Physical entry values of the selected slot calendar

The planner reads the old level's header and its computed score bit, the two
separate width and slot table heads, and the next level's six canonical
incidence heads. The address of the score is inside the selected prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkSlotCalendar

open BurstRAM Compression DescriptorSpace PhaseRecipe ShrinkBlockInputs
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w)
variable (start : ℕ) (L : Layout) (first : ℕ) (pub : Fin 5 → Word w) (st : Word w)
variable (m : Memory w)

local notation "ev" => Expr.eval pub st m
local notation "old" => levelStart L (first + i.val)
local notation "new" => levelStart L (first + (i.val + 1))
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "step" => (10 : Word w)
local notation "score" => SelectedArena.origin X (ShrinkInput.termHead (w := w) X start) step + 2
local notation "role" => SelectedArena.roleBase X (ShrinkInput.termHead (w := w) X start) step
local notation "sh" => ShrinkSlots.levelShape (b := b i) X

/-- The layout cell read by the online planner has its natural address in the
input arena and strictly precedes the selected role columns. -/
theorem reference_heads (header : ShrinkHeaderReads.Header i X T start L first m)
    (entry : LevelFields.Entry L first pub st m) (termRoom : ShrinkInput.termEnd X start 10 < 2 ^ w)
    (room : SelectedFinish.stop X term step ≤ 2 ^ w) :
    ev (plan B i).input.oldArc = (role : Word w) ∧
      (ev (SelectedPlan.layoutCell (selected B i))).val = score ∧
      start ≤ score ∧ score < role := by
  have width : 10 < 2 ^ w := by have := header.room; omega
  have read := (SelectedTailPackets.header_values B i X T start pub st m header entry termRoom
    width (fun _ => True) trivial (fun _ _ => trivial)).1
  have roles := SelectedPlan.roles_head _ X _ T term pub st m read
  have scored := SelectedPlan.score_head _ X _ T term pub st m read
  have endScore := (ShrinkOutput.old_bounds i X term step).2.2
  have hword : score < 2 ^ w := endScore.trans_le room
  have cell : (ev (SelectedPlan.layoutCell (selected B i))).val = score := by
    change (ev (SelectedPlan.scoreBase (selected B i)) + 2).val = _
    rw [scored,← (Nat.cast_ofNat (R := Word w) (n := 2)),← Nat.cast_add,
      Fin.val_natCast]
    exact Nat.mod_eq_of_lt hword
  have le := ScorePackets.start_le_term i X start termRoom
  refine ⟨roles,cell,?_,?_⟩
  · unfold SelectedArena.origin; omega
  · unfold SelectedArena.roleBase SelectedArena.placementBase; omega

/-- The shared values needed for all twenty-two native packets, in their reference
memory. The slot and width tables have the addresses published for this level. -/
theorem values (sel : SelectedScore.Selection B X) (width slots : ℕ) (dest : IncidenceDirectory w)
    (header : ShrinkHeaderReads.Header i X T start L first m)
    (entry : LevelFields.Entry L first pub st m) (termRoom : ShrinkInput.termEnd X start 10 < 2 ^ w)
    (room : SelectedFinish.stop X term step ≤ 2 ^ w)
    (chosen : m score = ((SelectedFinish.chosen B X sel).toNat : Word w))
    (widthCell : m (old + 62) = (width : Word w)) (slotCell : m (old + 63) = (slots : Word w))
    (destCells : ∀ c : Fin 6, m (new + (54 + c.val)) = dest.column c)
    (oldRoom : old + 66 ≤ 2 ^ w) (newRoom : new + 66 ≤ 2 ^ w) :
    ShrinkSlotPackets.Values (plan B i) (Fintype.card X.Base) (2 ^ g)
      (ShrinkOutput.heads sh role slots) (SelectedFinish.chosen B X sel) width dest pub st m := by
  have r := header.reads B entry
  obtain ⟨roleAt,layoutAt,_,_⟩ :=
    reference_heads B i X T start L first pub st m header entry termRoom room
  have slotHead : ev (BlockProgram.arena B i.val 3) = (slots : Word w) :=
    (LevelFields.eval_scalar entry i.val 63 (by omega)).trans slotCell
  refine ⟨slotInputs_reads B (space B) i X (origin B i) (BlockProgram.arena B i.val 3)
    pub st m role slots r.vertices r.residual roleAt slotHead,?_,?_,?_⟩
  · change m (ev (SelectedPlan.layoutCell (selected B i))).val = _
    rw [layoutAt]; exact chosen
  · exact (LevelFields.eval_scalar entry i.val 62 (by omega)).trans widthCell
  · intro c
    exact (LevelFields.eval_scalar entry (i.val + 1) (54 + c.val) (by have := c.isLt; omega)).trans
      (destCells c)

/-- Both saved pointer banks determine the two arena heads and the packed
destination columns. `HeadBank.ofNative` supplies these banks at publication. -/
theorem values_of_headBanks (sel : SelectedScore.Selection B X)
    (current next : Fin L.levels) (atCurrent : current.val = first + i.val)
    (atNext : next.val = first + (i.val + 1)) (oldRows : ℕ)
    (scalars : L.shape.scalarFields = 54) (tables : L.shape.tables = 6)
    (fit : endAddress L < 2 ^ w)
    (header : ShrinkHeaderReads.Header i X T start L first m)
    (entry : LevelFields.Entry L first pub st m)
    (termRoom : ShrinkInput.termEnd X start 10 < 2 ^ w)
    (room : SelectedFinish.stop X term step ≤ 2 ^ w)
    (chosen : m score = ((SelectedFinish.chosen B X sel).toNat : Word w))
    (currentHeads : PortRefresh.TraversalHeaders.HeadBank L current oldRows m)
    (nextHeads : PortRefresh.TraversalHeaders.HeadBank L next (ShrinkSlots.actualCount sh) m) :
    let width := arrayBase L current + 2 * tableWords L
    let slots := arrayBase L current + 3 * tableWords L
    let dest := packedIncidence L w next (ShrinkSlots.actualCount sh)
    ShrinkSlotPackets.Values (plan B i) (Fintype.card X.Base) (2 ^ g)
      (ShrinkOutput.heads sh role slots) (SelectedFinish.chosen B X sel) width dest pub st m := by
  intro width slots dest
  have extent (j : Fin L.levels) : levelStart L j + 66 < 2 ^ w := by
    apply lt_of_le_of_lt _ (level_room L fit j)
    have h : 66 ≤ levelWords L := by unfold levelWords levelHeaderWords; omega
    change levelsBase L + j.val * levelWords L + 66 ≤ levelsBase L + (j.val + 1) * levelWords L
    rw [Nat.succ_mul]; omega
  have oldFit := extent current
  have newFit := extent next
  rw [atCurrent] at oldFit; rw [atNext] at newFit
  apply values B i X T start L first pub st m sel width slots dest header entry termRoom room
    chosen _ _ _ oldFit.le newFit.le
  · let col : Fin L.shape.tables := ⟨2,by omega⟩
    have h := currentHeads.tables col
    change m (levelStart L current + L.shape.scalarFields + 6 + 2) =
      ((arrayBase L current + 2 * tableWords L : ℕ) : Word w) at h
    simpa only [scalars,atCurrent,Nat.add_assoc,width,slots] using h
  · let col : Fin L.shape.tables := ⟨3,by omega⟩
    have h := currentHeads.tables col
    change m (levelStart L current + L.shape.scalarFields + 6 + 3) =
      ((arrayBase L current + 3 * tableWords L : ℕ) : Word w) at h
    simpa only [scalars,atCurrent,Nat.add_assoc,width,slots] using h
  · intro c
    have h := nextHeads.incidence c
    rw [show dest = packedIncidence L w next (ShrinkSlots.actualCount sh) from rfl,packed_column]
    simpa only [incidenceHead,scalars,atNext,Nat.add_assoc] using h

section Widths

open ShrinkSliceSweep

variable (sel : SelectedScore.Selection B X)
variable {δ : ℝ} (ready : ShrinkMotif.Ready (2 ^ (a i)) (Shrink.colors (a i)) (2 ^ (b i)) δ)
variable (abs : Word w)
variable (I : ShrinkABSliceRecipe.Inputs) (ref : Memory w) (ab width slots cap : ℕ)
variable (r : ShrinkOutput.TablesRun w)
local notation "alloc" =>
  ShrinkOutput.splitBank (b := b i) X B.shrink sel term (Fin.val (10 : Word w)) role width
local notation "post" => r.remainder.postWidths

/-- Exact reference-memory frame from the beginning of the AB calendar up to
the first native slot packet. It applies to the selected bit and to both headers. -/
theorem before_slots_frame
    (run : ShrinkOutput.CompleteTables B i X ready sel term step abs start
      I pub st ref ab width slots cap m r)
    (fits : (alloc).Fits) {x : ℕ}
    (outsideAB : x < ab ∨ ab + (ShrinkInput.plan X start).B *
      IndexedStarts.capacity (ShrinkBundlePlan.thickCount (a i)) (ShrinkBundlePlan.cap (a i)) ≤ x)
    (outsideSupply : x < (alloc).widthBase ∨ (alloc).last ≤ x) : post x = m x := by
  have frame := run.remainder.sweep.frame
    (fun t _ j => (alloc).rowOutside fits (j,t) x outsideSupply)
  exact frame.trans (run.abFrame x outsideAB)

/-- Recover the chosen bit in the precise post-width memory passed to the
slot program, from the resident chosen readback preceding both slice passes. -/
theorem post_width_chosen
    (resident : ShrinkOutput.Resident B i X sel term step abs T start width m)
    (run : ShrinkOutput.CompleteTables B i X ready sel term step abs start
      I pub st ref ab width slots cap m r)
    (fits : (alloc).Fits) (early : SelectedFinish.stop X term step ≤ ab)
    (widthAfter : SelectedFinish.stop X term step ≤ width) :
    post score = ((SelectedFinish.chosen B X sel).toNat : Word w) := by
  have low := (ShrinkOutput.old_bounds i X term step).2.2
  have wa : width ≤ (alloc).widthBase := ShrinkOutput.retained_room X term (step).val role width
  exact (before_slots_frame B i X start pub st m sel ready abs I ref ab width slots cap r
    run fits (.inl (low.trans_le early)) (.inl (low.trans_le (widthAfter.trans wa)))).trans
      resident.chosen

/-- Read the actual slot operands in the memory reached by the AB calendar and
the four role sweeps. The bound on the number of table words is the uniform
per-position bound from the block layout. -/
theorem values_at_slots_framed
    (current next : Fin L.levels) (atCurrent : current.val = first + i.val)
    (atNext : next.val = first + (i.val + 1)) (oldRows : ℕ)
    (scalars : L.shape.scalarFields = 54) (tables : L.shape.tables = 6)
    (head : start = arrayBase L current) (firstTable : ab = start + tableWords L)
    (widthTable : width = start + 2 * tableWords L)
    (slotTable : slots = start + 3 * tableWords L)
    (size : X.positions * ShrinkLevelSpace.tableFactor S ≤ tableWords L)
    (fit : endAddress L < 2 ^ w) (pitch : (pub 1 - 1).val < start)
    (header : ShrinkHeaderReads.Header i X T start L first m)
    (entry : LevelFields.Entry L first pub st m)
    (currentHeads : PortRefresh.TraversalHeaders.HeadBank L current oldRows m)
    (nextHeads : PortRefresh.TraversalHeaders.HeadBank L next (ShrinkSlots.actualCount sh) m)
    (resident : ShrinkOutput.Resident B i X sel term step abs T start width m)
    (run : ShrinkOutput.CompleteTables B i X ready sel term step abs start
      I pub st ref ab width slots cap m r) :
    ShrinkSlotPackets.Values (plan B i) (Fintype.card X.Base) (2 ^ g)
      (ShrinkOutput.heads sh role slots) (SelectedFinish.chosen B X sel) width
      (packedIncidence L w next (ShrinkSlots.actualCount sh)) pub st post ∧
      (∀ x < start, post x = m x) ∧ (∀ x, new ≤ x → post x = m x) := by
  have ends := ShrinkLevelSpace.packed_ends S i X start ab width slots w
  have nextRoom : new < 2 ^ w :=
    (levelStart_mono L (atNext ▸ next.isLt.le)).trans_lt fit
  have afterTable : width + tableWords L ≤ new := by
    let col : Fin L.shape.tables := ⟨2, by omega⟩
    have h := tableEnd_le_nextLevel L current col
    change arrayBase L current + 2 * tableWords L + tableWords L ≤
      levelStart L (current.val + 1) at h
    rw [← head, ← widthTable, atCurrent, Nat.add_assoc] at h
    exact h
  have abBound := ends.2.2.2.2.1
  have keep : SelectedFinish.stop X term step ≤ ab :=
    ends.2.2.1.trans (firstTable ▸ Nat.add_le_add_left size _)
  have tr : ShrinkInput.termEnd X start 10 < 2 ^ w :=
    ends.2.1.trans_lt (by omega)
  have wa := ShrinkOutput.width_at_eq i X term step width (by omega)
  have last : (alloc).last ≤ new := by
    change ShrinkOutput.slotsBase X
      (ShrinkOutput.widthBase X (term).val (step).val role width) sh ≤ _
    rw [wa]
    exact ends.2.2.2.2.2.1.trans ((Nat.add_le_add_left size _).trans afterTable)
  have small : 10 < 2 ^ w := by have := header.room; omega
  have fits : (alloc).Fits :=
    ⟨(Nat.mod_eq_of_lt small).ge, le_max_left .., ready.count_pos, last.trans_lt nextRoom,
      by omega⟩
  have abLast : ab + (ShrinkInput.plan X start).B *
      IndexedStarts.capacity (ShrinkBundlePlan.thickCount (a i)) (ShrinkBundlePlan.cap (a i))
      ≤ new := by
    apply abBound.trans
    omega
  have left (x : ℕ) (hx : x < start) : post x = m x := by
    apply before_slots_frame B i X start pub st m sel ready abs I ref ab width slots cap r run fits
    · exact .inl (by omega)
    · apply Or.inl
      change x < ShrinkOutput.widthBase X (term).val (step).val role width
      rw [wa]; omega
  have right (x : ℕ) (hx : new ≤ x) : post x = m x :=
    before_slots_frame B i X start pub st m sel ready abs I ref ab width slots cap r
      run fits (.inr (abLast.trans hx)) (.inr (last.trans hx))
  have oldSpan : levelStart L current + levelHeaderWords L ≤ start := by
    rw [head]; exact Nat.le_add_right ..
  have hLen : levelHeaderWords L = 66 := by simp [levelHeaderWords, scalars, tables]
  have oldBefore : old + 60 < start := by rw [atCurrent, hLen] at oldSpan; omega
  have postHeader := header.keep_below oldBefore left
  have postEntry : LevelFields.Entry L first pub st post :=
    ⟨entry.pointer, (left _ pitch).trans entry.pitch⟩
  have postOld := currentHeads.keep (fun n hn => left _ (by omega))
  have postNext := nextHeads.keep (fun n _ => right _ (by rw [atNext]; omega))
  have chosen := post_width_chosen B i X T start pub st m sel ready abs I ref ab width slots cap r
    resident run fits keep (by omega)
  have h := values_of_headBanks B i X T start L first pub st post sel current next atCurrent
    atNext oldRows scalars tables fit postHeader postEntry tr (by omega) chosen postOld postNext
  refine ⟨?_, left, right⟩
  simpa only [slotTable, widthTable, head] using h

/-- The planner values at the first slot packet of the true post-width memory. -/
theorem values_at_slots
    (current next : Fin L.levels) (atCurrent : current.val = first + i.val)
    (atNext : next.val = first + (i.val + 1)) (oldRows : ℕ)
    (scalars : L.shape.scalarFields = 54) (tables : L.shape.tables = 6)
    (head : start = arrayBase L current) (firstTable : ab = start + tableWords L)
    (widthTable : width = start + 2 * tableWords L)
    (slotTable : slots = start + 3 * tableWords L)
    (size : X.positions * ShrinkLevelSpace.tableFactor S ≤ tableWords L)
    (fit : endAddress L < 2 ^ w) (pitch : (pub 1 - 1).val < start)
    (header : ShrinkHeaderReads.Header i X T start L first m)
    (entry : LevelFields.Entry L first pub st m)
    (currentHeads : PortRefresh.TraversalHeaders.HeadBank L current oldRows m)
    (nextHeads : PortRefresh.TraversalHeaders.HeadBank L next (ShrinkSlots.actualCount sh) m)
    (resident : ShrinkOutput.Resident B i X sel term step abs T start width m)
    (run : ShrinkOutput.CompleteTables B i X ready sel term step abs start
      I pub st ref ab width slots cap m r) :
    ShrinkSlotPackets.Values (plan B i) (Fintype.card X.Base) (2 ^ g)
      (ShrinkOutput.heads sh role slots) (SelectedFinish.chosen B X sel) width
      (packedIncidence L w next (ShrinkSlots.actualCount sh)) pub st post :=
  (values_at_slots_framed B i X T start L first pub st m sel ready abs I ref ab width slots cap r
    current next atCurrent atNext oldRows scalars tables head firstTable widthTable slotTable size
    fit pitch header entry currentHeads nextHeads resident run).1

end Widths

end CompressorRecords.ShrinkSlotCalendar

end

end VPVNP
end Computability
end OAI
