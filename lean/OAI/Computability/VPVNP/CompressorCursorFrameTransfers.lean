import OAI.Computability.VPVNP.CompressorCalendarTransfers

/-!
# Cursor-frame startup across external stage transfers

The row-count call, raw parameter writer, framed loader and bank copy enter in
state zero. At each accepting exit the stage linker writes the next stage number
below the workspace. The loader's read transcript uses the memory left by both
the raw writer and its transfer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CursorFrameTransfers

open BurstRAM BurstRAM.PrivateRAM DescriptorSpace CursorBounds OnlineCursorStartup
open scoped Fin.CommRing

variable {w : ℕ}

/-- Reports of the four accepting components before their transfer instructions. -/
structure Trace (w : ℕ) where
  /-- Report computing and storing the descriptor calendar's row count. -/
  row : Report w
  /-- Report writing the raw cursor parameters into the startup workspace. -/
  raw : Report w
  /-- Report loading the raw frame and computing the cursor's derived operands. -/
  loaded : Report w
  /-- Report copying the completed cursor operands into the persistent frame. -/
  copied : Report w

/-- Memory after the row-count report and the transfer to stage one. -/
def Trace.postRow (t : Trace w) (tag : Word w) (m : Memory w) := transfer m t.row tag 1
/-- Memory after the raw cursor parameters are published and control advances to stage two. -/
def Trace.postRaw (t : Trace w) (tag : Word w) (m : Memory w) := transfer (t.postRow tag m) t.raw tag 2
/-- Memory after the parameter loader runs and control advances to stage three. -/
def Trace.postLoad (t : Trace w) (tag : Word w) (m : Memory w) := transfer (t.postRaw tag m) t.loaded tag 3
/-- Memory after the persistent frame copy and the transfer to stage four. -/
def Trace.post (t : Trace w) (tag : Word w) (m : Memory w) := transfer (t.postLoad tag m) t.copied tag 4

/-- Construct the four cursor-frame reports using the memory produced by each preceding tagged
transfer. -/
noncomputable def trace (D : CalendarRows.Spec) (L : Layout) (B n a lanes : ℕ)
    (pub : Fin 11 → Word w) (tag : Word w) (m : Memory w) : Trace w :=
  let row := CalendarRows.report D pub n
  let counted := transfer m row tag 1
  let R := DescriptorParameters.raw L.shape a D.initialRows D.phaseRows lanes
  let raw := closed (R.recipe.report (pub ∘ DescriptorParameters.operand) 0 counted)
  let prepared := transfer counted raw tag 2
  let loaded := closed (DescriptorParameters.loaderReport L B n a (roundedDown D.p D.q n * lanes) pub 0 prepared)
  let published := transfer prepared loaded tag 3
  let copied := closed ((DescriptorParameters.copy L.shape).recipe.report (pub ∘ DescriptorParameters.operand) 0 published)
  ⟨row, raw, loaded, copied⟩

/-- The four calls and the memory passed to the stride calculator. -/
structure Runs (D : CalendarRows.Spec) (L : Layout) (B n a lanes : ℕ)
    (pub : Fin 11 → Word w) (tag : Word w) (m : Memory w) : Prop where
  callRow :
    let t := trace D L B n a lanes pub tag m
    Call (CalendarRows.table D) pub (CalendarRows.ticks D n+2) 0 m t.row
  callRaw :
    let t := trace D L B n a lanes pub tag m
    Call (LiveOneShot.oneShot (DescriptorParameters.table L.shape a D.initialRows D.phaseRows lanes))
      pub ((DescriptorParameters.raw L.shape a D.initialRows D.phaseRows lanes).recipe.code.length+1)
      0 (t.postRow tag m) t.raw
  callLoad :
    let t := trace D L B n a lanes pub tag m
    Call (LiveOneShot.oneShot DescriptorParameters.loader) pub (VirtualParameters.ticks n+43+4*17)
      0 (t.postRaw tag m) t.loaded
  callCopy :
    let t := trace D L B n a lanes pub tag m
    Call (LiveOneShot.oneShot (DescriptorParameters.copyTable L.shape))
      pub ((DescriptorParameters.copy L.shape).recipe.code.length+1) 0 (t.postLoad tag m) t.copied
  saved : Frame.data (DescriptorParameters.saved L w) ((trace D L B n a lanes pub tag m).post tag m) =
    DescriptorParameters.outputs L B n a (roundedDown D.p D.q n * lanes) w
  active : Frame.data (pub 2+9) ((trace D L B n a lanes pub tag m).post tag m) =
    DescriptorParameters.outputs L B n a (roundedDown D.p D.q n * lanes) w
  count : (trace D L B n a lanes pub tag m).post tag m (pub 2+8).val = (CalendarRows.rows D n : Word w)
  reserved : levelStart L 0+14 ≤ levelStart L 0+L.shape.scalarFields
  tagged : (trace D L B n a lanes pub tag m).post tag m tag.val = 4
  source_below : ∀ x < L.base, let t := trace D L B n a lanes pub tag m
    after m t.row.events x = m x ∧
    after (t.postRow tag m) t.raw.events x = t.postRow tag m x ∧
    after (t.postRaw tag m) t.loaded.events x = t.postRaw tag m x ∧
    after (t.postLoad tag m) t.copied.events x = t.postLoad tag m x

private theorem oneShot_call {p r cap : ℕ} {T : Template p r 11} {pub : Fin 11 → Word w}
    {m : Memory w} {out : Report w} (h : Call T pub cap 0 m out) :
    Call (LiveOneShot.oneShot T) pub cap 0 m (closed out) := by
  dsimp only [Call] at h ⊢
  rw [LiveOneShot.execute_oneShot]
  change (execute _ _ ((T.instantiate w pub).program.start 0) m []).map _ = _
  rw [h]
  rfl

/-- From any external memory, the four native components and their transfers
leave both cursor banks populated, the calendar count intact, and stage four selected. -/
theorem run (D : CalendarRows.Spec) (L : Layout) (B n a lanes : ℕ)
    (pub : Fin 11 → Word w) (tag : Word w) (m : Memory w) (input : Input D L B n pub)
    (hw : w = wordBits B n) (hB : 1 ≤ B) (hL : roundedDown D.p D.q n * lanes ≤ virtualBits B n)
    (arity : 7 ≤ L.shape.arity) (scalars : 14 ≤ L.shape.scalarFields)
    (capacity : CursorRAM.ParametersInit.Capacity B n a (roundedDown D.p D.q n * lanes)
      (directoryBase L) 1 (incidenceStart L 0) (levelStart L 0+6)) (lower : tag.val < L.base) :
    Runs D L B n a lanes pub tag m := by
  let t := trace D L B n a lanes pub tag m
  let countAddr := (pub 2+8).val
  let T := roundedDown D.p D.q n
  let out := DescriptorParameters.outputs L B n a (T*lanes) w
  have frameEnd : frameBase L+8 ≤ levelStart L 0+6 := by
    have h := frame_before_directory L
    simp only [levelStart, levelsBase, Nat.zero_mul, Nat.add_zero]
    omega
  have savedFit : levelStart L 0+6+8 < 2^w := hw ▸ capacity.frame_end
  have fit : frameBase L+8 < 2^w := by omega
  have baseFit : L.base+9+8 < 2^w := fit
  have rawBase : (pub 2+9).val = frameBase L := by
    change _ = L.base+9
    have h := offset_value (pub 2) 9 (by rw [input.base]; omega)
    exact h.trans (by rw [input.base])
  have savedBase : (DescriptorParameters.saved L w).val = levelStart L 0+6 :=
    Nat.mod_eq_of_lt (by omega)
  have countVal : countAddr = L.base+8 := by
    have h := offset_value (pub 2) 8 (by rw [input.base]; omega)
    exact h.trans (by rw [input.base])
  have belowRaw : countAddr < frameBase L := by rw [countVal, frameBase]; omega
  have belowSaved : countAddr < levelStart L 0+6 := by omega
  have keepCount (mem : Memory w) (v : Word w) :
      writeMemory mem tag v countAddr = mem countAddr := by
    rw [writeMemory, ite_eq_right (by omega)]
  have keepRaw (mem : Memory w) (v : Word w) :
      (Frame.data (pub 2+9) (writeMemory mem tag v) : Fin 8 → Word w) = Frame.data (pub 2+9) mem :=
    lower_write_frame _ _ _ _ (by rw [rawBase]; omega) (by rw [rawBase]; omega)
  have keepSaved (mem : Memory w) (v : Word w) :
      (Frame.data (DescriptorParameters.saved L w) (writeMemory mem tag v) : Fin 8 → Word w) =
        Frame.data (DescriptorParameters.saved L w) mem :=
    lower_write_frame _ _ _ _ (by rw [savedBase]; omega) (by rw [savedBase]; omega)
  obtain ⟨row, ready⟩ := count_ready D L B n pub 0 m input
  have readyRow : DescriptorParameters.Ready L B n D.initialRows D.phaseRows T pub (t.postRow tag m) :=
    { ready with total := (congrArg Fin.val (keepCount _ _)).trans ready.total }
  obtain ⟨raw, _, rawBank, rawPreserves, _⟩ := DescriptorParameters.prepare readyRow 0 a lanes fit
  have ⟨load, _, published, loadPreserves, _⟩ :=
    DescriptorParameters.publish hw hB hL capacity pub 0 (t.postRaw tag m) ((keepRaw _ _).trans rawBank)
  have countAfterLoad : t.postLoad tag m countAddr = t.postRow tag m countAddr :=
    (keepCount _ _).trans ((loadPreserves _ (Or.inl belowSaved)).trans
      ((keepCount _ _).trans (rawPreserves _ (Or.inl belowRaw))))
  have readyLoad : DescriptorParameters.Ready L B n D.initialRows D.phaseRows T pub (t.postLoad tag m) :=
    { readyRow with total := (congrArg Fin.val countAfterLoad).trans readyRow.total }
  obtain ⟨copy, _, copied, copyPreserves, _⟩ := DescriptorParameters.copy_run readyLoad 0 fit
  have savedLoad : Frame.data (DescriptorParameters.saved L w) (t.postLoad tag m) = out :=
    (keepSaved _ _).trans published
  have savedCopy : (Frame.data (DescriptorParameters.saved L w)
      (after (t.postLoad tag m) t.copied.events) : Fin 8 → Word w) =
      Frame.data (DescriptorParameters.saved L w) (t.postLoad tag m) := by
    have room : (DescriptorParameters.saved L w).val+8 ≤ 2^w := by omega
    funext j
    rw [Frame.data_at _ _ room, Frame.data_at _ _ room]
    exact copyPreserves _ (Or.inr (by omega))
  have before (x : ℕ) (hx : x < L.base) :
      after m t.row.events x = m x ∧
      after (t.postRow tag m) t.raw.events x = t.postRow tag m x ∧
      after (t.postRaw tag m) t.loaded.events x = t.postRaw tag m x ∧
      after (t.postLoad tag m) t.copied.events x = t.postLoad tag m x := by
    have belowCount : x < countAddr := by omega
    refine ⟨?_,rawPreserves x (.inl (by omega)),loadPreserves x (.inl (by omega)),copyPreserves x (.inl (by omega))⟩
    change after m (CalendarRows.report D pub n).events x = m x
    rw [CalendarRows.after_report,writeMemory,ite_eq_right (ne_of_lt belowCount)]
  refine ⟨row, oneShot_call raw, oneShot_call load, oneShot_call copy,
    (keepSaved _ _).trans (savedCopy.trans savedLoad),
    (keepRaw _ _).trans (copied.trans savedLoad), ?_, Nat.add_le_add_left scalars _, transfer_tag .., before⟩
  apply (keepCount _ _).trans
  apply (copyPreserves _ (Or.inl belowRaw)).trans
  apply countAfterLoad.trans
  apply (keepCount _ _).trans
  change after m (CalendarRows.report D pub n).events (pub 2+8).val = _
  rw [CalendarRows.after_report, writeMemory, ite_eq_left rfl]

end CompressorRecords.CursorFrameTransfers

end VPVNP
end Computability
end OAI
