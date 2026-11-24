import OAI.Computability.VPVNP.CompressorCalendarTransfers
import OAI.Computability.VPVNP.CompressorHistoryArenaBase

/-!
# Starting the history arena and calendar across pair-linker calls

After the cursor parameters have been copied to the active frame, four native
calls compute the level stride, publish the history arena and traversal
bounds, install the pointer bank, and arm the calendar. The external tag is
updated after each accepting call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CalendarArenaTransfers

open BurstRAM BurstRAM.PrivateRAM CursorBounds DescriptorSpace OnlineCursorStartup
open private closed_call from OAI.Computability.VPVNP.CompressorOnlineCursorStartup
open scoped Fin.CommRing

variable {w : ℕ}

/-- The four startup reports that install the descriptor stride, history arena, scheduler bank
and calendar arm. -/
structure Trace (w : ℕ) where
  /-- Report of the worker that publishes the descriptor stride. -/
  stride : Report w
  /-- Report of the worker that computes the history arena base from the calendar and level
  dimensions. -/
  arena : Report w
  /-- Report of the worker that initializes the scheduler operand bank. -/
  bank : Report w
  /-- Report of the worker that arms the online calendar. -/
  arm : Report w

/-- Memory after applying the stride report and transferring control to stage five. -/
def Trace.postStride (t : Trace w) (tag : Word w) (m : Memory w) := transfer m t.stride tag 5
/-- Memory after publishing the history arena base and transferring control to stage six. -/
def Trace.postArena (t : Trace w) (tag : Word w) (m : Memory w) := transfer (t.postStride tag m) t.arena tag 6
/-- Memory after the scheduler bank is initialized and control advances to stage seven. -/
def Trace.postBank (t : Trace w) (tag : Word w) (m : Memory w) := transfer (t.postArena tag m) t.bank tag 7
/-- Memory after the calendar is armed and the stage tag advances to eight. -/
def Trace.post (t : Trace w) (tag : Word w) (m : Memory w) := transfer (t.postBank tag m) t.arm tag 8

/-- Construct the four startup reports chronologically, using each tagged transfer's output
memory for the next worker. -/
def trace (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (steps : ℕ)
    (pub : Fin 11 → Word w) (tag : Word w) (m : Memory w) : Trace w :=
  let stride := closed (DescriptorStride.report L.shape pub 0 m)
  let arena := closed (HistoryArenaBase.report L.shape D.initialRows D.phaseRows steps pub 0 (transfer m stride tag 5))
  ⟨stride,arena,Workspace.initReport L.shape.arity (pub 2),Workspace.calendarReport d (pub 2)⟩

variable (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (B n a lanes steps : ℕ)
variable (pub : Fin 11 → Word w) (tag : Word w) (m : Memory w)

local notation "tr" => trace D d L steps pub tag m

/-- Each startup worker executes at the specified clock and stage entry, producing the
corresponding report of the trace. -/
structure Runs : Prop where
  callStride : Call (OnlineWorkspace.strideTable L.shape) pub (1+DescriptorStride.cost L.shape) 0 m (tr).stride
  callArena : Call (LiveOneShot.oneShot (HistoryArenaBase.table L.shape D.initialRows D.phaseRows steps)) pub
    (1+HistoryArenaBase.cost L.shape D.initialRows D.phaseRows steps) 0 ((tr).postStride tag m) (tr).arena
  callBank : Call (Workspace.initTable L.shape.arity) pub 42 0 ((tr).postArena tag m) (tr).bank
  callArm : Call (Workspace.calendarStart d) pub 6 0 ((tr).postBank tag m) (tr).arm
  ready : OnlineWorkspace.Ready d L.shape.arity (pub 2) (CalendarRows.rows D n) (levelWords L) ((tr).post tag m)
  saved : Frame.data (DescriptorParameters.saved L w) ((tr).post tag m) =
    DescriptorParameters.outputs L B n a (roundedDown D.p D.q n*lanes) w
  levelWords_after : ∀ x, levelStart L 0 ≤ x → (tr).post tag m x = HistoryArenaBase.install L n m x
  tagged : (tr).post tag m tag.val = 8
  source_below : ∀ x < L.base,
    after m (tr).stride.events x = m x ∧
    after ((tr).postStride tag m) (tr).arena.events x = (tr).postStride tag m x ∧
    after ((tr).postArena tag m) (tr).bank.events x = (tr).postArena tag m x ∧
    after ((tr).postBank tag m) (tr).arm.events x = (tr).postBank tag m x

private theorem install_away (L : Layout) (n : ℕ) (m : Memory w) (fit : levelStart L 0+29 < 2^w)
    (x : ℕ) (a : x ≠ levelStart L 0+14) (b : x ≠ levelStart L 0+28) (c : x ≠ levelStart L 0+29) :
    HistoryArenaBase.install L n m x = m x := by
  simp only [HistoryArenaBase.install, writeMemory, Fin.val_natCast, Nat.mod_eq_of_lt fit,
    Nat.mod_eq_of_lt (show levelStart L 0+14 < 2^w by omega), Nat.mod_eq_of_lt (show levelStart L 0+28 < 2^w by omega),
    a,b,c,↓reduceIte]

/-- At entry, both cursor banks and the natural row count come from the
preceding four linked calls. The layout and word bounds certify every
address used in the history-arena header. -/
theorem run (input : Input D L B n pub) (lower : tag.val < L.base)
    (hL : roundedDown D.p D.q n*lanes ≤ virtualBits B n) (positions : initialPositions B n = L.positions)
    (levels : L.levels = 1+roundedDown D.p D.q n*(steps+1))
    (fit : levelStart L 0+29 < 2^w)
    (cnt : m (pub 2+8).val = (CalendarRows.rows D n : Word w))
    (active : Frame.data (pub 2+9) m = DescriptorParameters.outputs L B n a (roundedDown D.p D.q n*lanes) w)
    (saved : Frame.data (DescriptorParameters.saved L w) m =
      DescriptorParameters.outputs L B n a (roundedDown D.p D.q n*lanes) w) :
    Runs D d L B n a lanes steps pub tag m := by
  let head := levelStart L 0
  let base := pub 2
  let g := L.shape.arity
  let pitch := OnlineWorkspace.gap g base
  let pitched := (tr).postStride tag m
  let staged := (tr).postArena tag m
  have hbase : base.val = L.base := input.base
  have sep : L.base+10+g < head := by
    simp only [head,g,levelStart,levelsBase,directoryBase,plannerTag,frameBase,Nat.zero_mul,Nat.add_zero]
    omega
  change head+29 < 2^w at fit
  have countVal : (base+8).val = L.base+8 := (offset_value base 8 (by omega)).trans (by rw [hbase])
  have pitchVal : pitch.val = L.base+(10+g) :=
    (offset_value base (10+g) (by omega)).trans (by rw [hbase])
  have pos := (position_count hL).trans positions
  have ⟨strideExec,_,strideEffect,_⟩ := DescriptorStride.native L pub 0 m active pos
  have pitchedEq : pitched = writeMemory (writeMemory m pitch (levelWords L)) tag 5 :=
    congrArg (fun z ↦ writeMemory z tag 5) strideEffect
  have pitchAt : pitched pitch.val = (levelWords L : Word w) := by
    rw [pitchedEq, writeMemory, ite_eq_right (by omega : pitch.val ≠ tag.val)]; simp [writeMemory]
  have countAt : pitched (base+8).val = (CalendarRows.rows D n : Word w) := by
    rw [pitchedEq, writeMemory, ite_eq_right (by omega : (base+8).val ≠ tag.val), writeMemory,
      ite_eq_right (by omega : (base+8).val ≠ pitch.val)]
    exact cnt
  have keepPitch (x : ℕ) (hx : head ≤ x) : pitched x = m x := by
    rw [pitchedEq,writeMemory,ite_eq_right (by omega : x ≠ tag.val),writeMemory,ite_eq_right (by omega : x ≠ pitch.val)]
  have entry : DescriptorParameters.Ready L B n D.initialRows D.phaseRows (roundedDown D.p D.q n) pub pitched := by
    refine ⟨input.base,input.length,input.address,?_,?_,input.phase_pos,input.phase_fit⟩
    · rw [countAt,Fin.val_natCast,Nat.mod_eq_of_lt input.rows_fit,CalendarRows.rows,Nat.mul_comm]
    · rw [input.directory,CalendarRows.rows,Nat.mul_comm]
  obtain ⟨arenaExec,arenaEffect,_⟩ := HistoryArenaBase.native entry steps levels pitchAt 0
  have stagedEq : staged = writeMemory (HistoryArenaBase.install L n pitched) tag 6 :=
    congrArg (fun z ↦ writeMemory z tag 6) arenaEffect
  have low (x : ℕ) (lo : tag.val < x) (hi : x < head) : staged x = pitched x := by
    rw [stagedEq,writeMemory,ite_eq_right (ne_of_gt lo)]
    exact install_away L n pitched fit x (by change x ≠ head+14; omega) (by change x ≠ head+28; omega)
      (by change x ≠ head+29; omega)
  obtain ⟨initExec,armExec,armed,keep⟩ := transferred_arm d g pub staged tag
    (CalendarRows.rows D n) (levelWords L) (by omega) (by omega)
    ((low (base+8).val (by omega) (by omega)).trans countAt) ((low pitch.val (by omega) (by omega)).trans pitchAt)
  have allLevels (x : ℕ) (hx : head ≤ x) : (tr).post tag m x = HistoryArenaBase.install L n m x := by
    rw [show (tr).post tag m x = staged x from keep x (by change base.val+8 ≤ x; omega)]
    rw [stagedEq,writeMemory,ite_eq_right (by omega : x ≠ tag.val)]
    simp only [HistoryArenaBase.install,writeMemory,keepPitch x hx]
  have before (x : ℕ) (hx : x < L.base) :
      after m (tr).stride.events x = m x ∧
      after pitched (tr).arena.events x = pitched x ∧
      after staged (tr).bank.events x = staged x ∧
      after ((tr).postBank tag m) (tr).arm.events x = (tr).postBank tag m x := by
    refine ⟨?_,?_,?_,?_⟩
    · change after m (DescriptorStride.report L.shape pub 0 m).events x = m x
      rw [strideEffect,writeMemory]
      apply ite_eq_right
      rw [offset_value _ _ (by change base.val + (10+g) < 2^w; omega)]
      change x ≠ base.val+(10+g)
      omega
    · change after pitched (HistoryArenaBase.report L.shape D.initialRows D.phaseRows steps pub 0 pitched).events x = _
      rw [arenaEffect]
      exact install_away L n pitched fit x (by change x ≠ head+14; omega) (by change x ≠ head+28; omega)
        (by change x ≠ head+29; omega)
    · apply Workspace.init_outside
      intro i
      have hi := i.isLt
      rw [offset_value _ _ (by change base.val+i.val < 2^w; omega)]
      change x ≠ base.val+i.val
      omega
    · change after ((tr).postBank tag m) (Workspace.calendarReport d base).events x = _
      rw [(Workspace.calendar_effect d g base _).1,writeMemory,ite_eq_right]
      have hv : (Workspace.ports g base).tag.val = base.val+6 := offset_value base 6 (by omega)
      omega
  refine ⟨closed_call _ _ _ _ _ _ strideExec, closed_call _ _ _ _ _ _ arenaExec,
    initExec,armExec,armed,?_,allLevels,transfer_tag ..,before⟩
  apply Eq.trans _ saved
  funext j
  have val : (DescriptorParameters.saved L w).val = head+6 := Nat.mod_eq_of_lt (by omega)
  have room : (DescriptorParameters.saved L w).val+8 ≤ 2^w := by omega
  have hj := j.isLt
  rw [Frame.data_at _ _ room, Frame.data_at _ _ room, val, allLevels _ (by omega)]
  exact install_away L n m fit _ (by change head+6+j.val ≠ head+14; omega)
    (by change head+6+j.val ≠ head+28; omega) (by change head+6+j.val ≠ head+29; omega)

end CompressorRecords.CalendarArenaTransfers

end VPVNP
end Computability
end OAI
