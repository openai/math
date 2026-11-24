import OAI.Computability.VPVNP.CompressorDescriptorCursorFrame
import OAI.Computability.VPVNP.CompressorDescriptorParameterCapacity
import OAI.Computability.VPVNP.CompressorRecordsOnlineWorkspace

/-!
# Chronological startup of the online cursor calendar

The row counter determines the size of the directory before the parameter
publisher computes any level address. The stride and controller setup use the
published cursor parameters and preserve the permanent copy in level zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.OnlineCursorStartup

open BurstRAM BurstRAM.PrivateRAM DescriptorSpace CursorBounds
open scoped Fin.CommRing

variable {w : ℕ}

/-- The public pair inputs and integer operands of the first calendar call. -/
structure Input (D : CalendarRows.Spec) (L : Layout) (B n : ℕ) (pub : Fin 11 → Word w) : Prop where
  base : (pub 2).val = L.base
  length : (pub 6).val = n
  address : (pub 7).val = addressBits B n
  denominator_pos : 0 < D.q
  phase_pos : 0 < D.phaseRows
  phase_fit : D.phaseRows < 2^w
  numerator_fit : D.p < 2^w
  radix_fit : 2^D.q < 2^w
  power_fit : n^D.p < 2^w
  rows_fit : CalendarRows.rows D n < 2^w
  directory : directoryRows L = CalendarRows.rows D n

/-- The count writer is the only prerequisite for the raw parameter producer.
Its output memory meets the producer's entry conditions from arbitrary memory. -/
theorem count_ready (D : CalendarRows.Spec) (L : Layout) (B n : ℕ)
    (pub : Fin 11 → Word w) (s : Word w) (m : Memory w) (h : Input D L B n pub) :
    let P := ((CalendarRows.table D).instantiate w pub).program
    let rep := CalendarRows.report D pub n
    let T := roundedDown D.p D.q n
    execute P (CalendarRows.ticks D n + 2) (P.start s) m [] = some rep ∧
      DescriptorParameters.Ready L B n D.initialRows D.phaseRows T pub (after m rep.events) := by
  refine ⟨CalendarRows.execute_native D pub s m [] n h.denominator_pos h.length h.numerator_fit
    h.radix_fit h.power_fit le_rfl, h.base, h.length, h.address, ?_, ?_, h.phase_pos, h.phase_fit⟩
  · rw [CalendarRows.after_report, writeMemory, ite_eq_left rfl, Fin.val_natCast, Nat.mod_eq_of_lt h.rows_fit]
    exact Nat.add_left_cancel_iff.mpr (Nat.mul_comm ..)
  · rw [h.directory, CalendarRows.rows, Nat.mul_comm]

/-- Tight allocation puts exactly the computed number of directory rows
before the first level. All integer-fit obligations hold eventually for the
same threshold, regardless of the pair's workspace address. -/
theorem eventually_input (D : CalendarRows.Spec) (B : ℕ) (hB : 1 ≤ B)
    (hq : 0 < D.q) (hph : 0 < D.phaseRows) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (L : Layout) (pub : Fin 11 → Word (wordBits B n)),
      (pub 2).val = L.base → (pub 6).val = n → (pub 7).val = addressBits B n →
      Input D (LevelFields.tightDirectory L (CalendarRows.rows D n)) B n pub := by
  filter_upwards [CalendarRows.eventually_fits D B hB,
    CursorRAM.eventual_word_room B hB (PolynomiallyBounded.const D.phaseRows)] with n h hp
  intro L pub base len addr
  exact ⟨base, len, addr, hq, hph, hp, h.1, h.2.1, h.2.2.1, h.2.2.2, LevelFields.tight_rows ..⟩

/-- All writes of the stride and calendar-arming stages lie below level zero. -/
private theorem addresses (L : Layout) (base : Word w) (hb : base.val = L.base)
    (fit : levelStart L 0 < 2^w) :
    (OnlineWorkspace.gap L.shape.arity base).val < levelStart L 0 ∧
      ∀ i : Fin 8, (base + (i.val : Word w)).val < levelStart L 0 := by
  have head : L.base+10+L.shape.arity < levelStart L 0 := by
    simp only [levelStart, levelsBase, directoryBase, plannerTag, frameBase, Nat.zero_mul, Nat.add_zero]
    omega
  have atOffset (j : ℕ) (hj : L.base+j < levelStart L 0) :
      (base+(j : Word w)).val = L.base+j := by
    rw [Fin.val_add, hb, Fin.val_natCast, Nat.mod_eq_of_lt (show j < 2^w by omega),
      Nat.mod_eq_of_lt (hj.trans fit)]
  constructor
  · change (base + ((10+L.shape.arity : ℕ) : Word w)).val < _
    rw [atOffset _ (by omega)]; omega
  · intro i
    rw [atOffset _ (by have := i.isLt; omega)]
    have := i.isLt
    omega

/-- Arming the calendar preserves all persistent descriptor words beginning
at the first level. This includes the cursor operand bank at offsets 6–13. -/
theorem arm_preserves_levels (d : ℕ) (L : Layout) (pub : Fin 11 → Word w)
    (s : Word w) (m : Memory w) (hb : (pub 2).val = L.base) (fit : levelStart L 0 < 2^w)
    {row tag : Word w} {b l a W start : ℕ}
    (frame : Frame.data (pub 2+9) m = CursorRAM.ScheduleInit.inputs row tag b l a W start)
    (positions : (b+l)*2^b*2^l = L.positions) {addr : ℕ} (level : levelStart L 0 ≤ addr) :
    let middle := after m (DescriptorStride.report L.shape pub s m).events
    OnlineWorkspace.armed d L.shape.arity (pub 2) middle addr = m addr := by
  intro middle
  obtain ⟨gap,control⟩ := addresses L (pub 2) hb fit
  have stride := (DescriptorStride.native L pub s m frame positions).2.2.1
  change middle = writeMemory m (OnlineWorkspace.gap L.shape.arity (pub 2)) _ at stride
  rw [OnlineWorkspace.armed, (Workspace.calendar_effect d L.shape.arity ..).1]
  have tagBelow : (Workspace.ports L.shape.arity (pub 2)).tag.val < levelStart L 0 := control 6
  rw [writeMemory, ite_eq_right (by omega : addr ≠ (Workspace.ports L.shape.arity (pub 2)).tag.val),
    Workspace.init_outside _ _ _ _ (fun i ↦ ne_of_gt ((control i).trans_le level)), stride, writeMemory]
  exact ite_eq_right (by omega)

private theorem closed_call {p r : ℕ} (T : Template p r 11) (pub : Fin 11 → Word w)
    (s : Word w) (m : Memory w) (f : ℕ) (rep : Report w)
    (native : let P := (T.instantiate w pub).program
      execute P f (P.start s) m [] = some rep) :
    let P := ((LiveOneShot.oneShot T).instantiate w pub).program
    execute P f (P.start s) m [] = some ⟨rep.events,none⟩ := by
  dsimp only
  rw [LiveOneShot.execute_oneShot]
  change (execute _ _ ((T.instantiate w pub).program.start s) m []).map _ = _
  rw [native]; rfl

/-- The split cursor position count is the position capacity of the native
initial graph, including the boundary case of zero residual base bits. -/
theorem position_count {B n l : ℕ} (hl : l ≤ virtualBits B n) :
    (virtualBits B n-l+l)*2^(virtualBits B n-l)*2^l = initialPositions B n := by
  rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hl, initialPositions, Nat.mul_comm]

/-- A normal pair-ABI entry of one fixed template at its stated fuel cap. -/
def Call {pc r : ℕ} (T : Template pc r 11) (pub : Fin 11 → Word w)
    (cap : ℕ) (s : Word w) (m : Memory w) (out : Report w) : Prop :=
  let P := (T.instantiate w pub).program
  execute P cap (P.start s) m [] = some out

/-- Close a startup report by keeping its events and clearing its returned continuation state. -/
def closed (r : Report w) : Report w := ⟨r.events,none⟩

/-- Packing a different number of directory rows changes their addresses
at runtime. The shape-dependent startup instruction tables are fixed. -/
theorem tight_tables (L : Layout) (rows a initial phases lanes : ℕ) :
    let F := (LevelFields.tightDirectory L rows).shape
    DescriptorParameters.table F a initial phases lanes =
        DescriptorParameters.table L.shape a initial phases lanes ∧
      DescriptorParameters.copyTable F = DescriptorParameters.copyTable L.shape ∧
      OnlineWorkspace.strideTable F = OnlineWorkspace.strideTable L.shape ∧
      Workspace.initTable F.arity = Workspace.initTable L.shape.arity :=
  ⟨rfl,rfl,rfl,rfl⟩

/-- The seven accepting calls that precede the first visit in the online
calendar. The three frame programs use single-call wrappers so the outer
linker can transfer control at their successful exits. -/
def Runs (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (B n a lanes : ℕ)
    (pub : Fin 11 → Word w) (s : Word w) (m : Memory w) : Prop :=
    let T := roundedDown D.p D.q n
    let q := CalendarRows.report D pub n
    let counted := after m q.events
    let tr := DescriptorParameters.trace L B n a D.initialRows D.phaseRows T lanes pub 0 0 0 counted
    let prepared := tr.post counted
    let stride := DescriptorStride.report L.shape pub 0 prepared
    let pitched := after prepared stride.events
    let bank := Workspace.initReport L.shape.arity (pub 2)
    let final := OnlineWorkspace.armed d L.shape.arity (pub 2) pitched
    Call (CalendarRows.table D) pub (CalendarRows.ticks D n+2) s m q ∧
      Call (LiveOneShot.oneShot (DescriptorParameters.table L.shape a D.initialRows D.phaseRows lanes))
        pub ((DescriptorParameters.raw L.shape a D.initialRows D.phaseRows lanes).recipe.code.length+1)
        0 counted (closed tr.raw) ∧
      Call (LiveOneShot.oneShot DescriptorParameters.loader) pub (VirtualParameters.ticks n+43+4*17)
        0 (tr.postRaw counted) (closed tr.loaded) ∧
      Call (LiveOneShot.oneShot (DescriptorParameters.copyTable L.shape)) pub
        ((DescriptorParameters.copy L.shape).recipe.code.length+1) 0 (tr.postLoad counted) (closed tr.copied) ∧
      Call (OnlineWorkspace.strideTable L.shape) pub (1+DescriptorStride.cost L.shape) 0 prepared (closed stride) ∧
      Call (Workspace.initTable L.shape.arity) pub 42 0 pitched bank ∧
      Call (Workspace.calendarStart d) pub 6 0 (after pitched bank.events) (Workspace.calendarReport d (pub 2)) ∧
      OnlineWorkspace.Ready d L.shape.arity (pub 2) (CalendarRows.rows D n) (levelWords L) final ∧
      Frame.data (DescriptorParameters.saved L w) final = DescriptorParameters.outputs L B n a (T*lanes) w

/-- Starting with arbitrary external memory, compute the row count, produce
both cursor frames, install the stride and leave the online calendar ready
with its level-zero frame intact. -/
theorem run (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (B n a lanes : ℕ)
    (pub : Fin 11 → Word w) (s : Word w) (m : Memory w) (input : Input D L B n pub)
    (hw : w = wordBits B n) (hB : 1 ≤ B)
    (hL : roundedDown D.p D.q n * lanes ≤ virtualBits B n)
    (arity : 7 ≤ L.shape.arity) (scalars : 14 ≤ L.shape.scalarFields)
    (positions : initialPositions B n = L.positions)
    (capacity : CursorRAM.ParametersInit.Capacity B n a (roundedDown D.p D.q n*lanes)
      (directoryBase L) 1 (incidenceStart L 0) (levelStart L 0+6)) :
    Runs D d L B n a lanes pub s m := by
  unfold Runs
  intro T q counted tr prepared stride pitched bank final
  obtain ⟨first, ready⟩ := count_ready D L B n pub s m input
  obtain ⟨raw, loaded, copied, _, _, _, permanent, active, keep, _⟩ :=
    DescriptorParameters.run ready hw hB a lanes hL arity scalars capacity 0 0 0
  have savedFit : levelStart L 0+6+8 < 2^w := hw ▸ capacity.frame_end
  have headFit : levelStart L 0 < 2^w := by omega
  have head : L.base+10+L.shape.arity < levelStart L 0 := by
    simp only [levelStart, levelsBase, directoryBase, plannerTag, frameBase, Nat.zero_mul, Nat.add_zero]
    omega
  have address : (pub 2+8).val = L.base+8 := by
    rw [Fin.val_add, input.base, show (8 : Word w).val = 8 from Nat.mod_eq_of_lt (by omega : 8 < 2^w),
      Nat.mod_eq_of_lt (by omega)]
  have count : prepared (pub 2+8).val = (CalendarRows.rows D n : Word w) := by
    change tr.post counted _ = _
    rw [keep _ (Or.inl (by rw [address, frameBase]; omega)) (Or.inl (by rw [address]; omega))]
    rw [CalendarRows.after_report, writeMemory, ite_eq_left rfl]
  have pos := (position_count hL).trans positions
  have ⟨strideExec,initExec,armExec,armed⟩ :=
    OnlineWorkspace.stride_and_arm d L pub 0 prepared _ active pos (by omega) count
  refine ⟨first, closed_call _ _ _ _ _ _ raw, closed_call _ _ _ _ _ _ loaded,
    closed_call _ _ _ _ _ _ copied, strideExec, initExec, armExec, armed, ?_⟩
  apply Eq.trans _ permanent
  funext j
  have hv : (DescriptorParameters.saved L w).val = levelStart L 0+6 := Nat.mod_eq_of_lt (by omega)
  have fit : (DescriptorParameters.saved L w).val+8 ≤ 2^w := by omega
  rw [Frame.data_at _ _ fit j, Frame.data_at _ _ fit j]
  exact arm_preserves_levels d L pub 0 prepared input.base headFit active pos (by rw [hv]; omega)

/-- External memory passed to the online calendar after the seven calls. -/
noncomputable def finalMemory (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (B n a lanes : ℕ)
    (pub : Fin 11 → Word w) (m : Memory w) : Memory w :=
  let T := roundedDown D.p D.q n
  let counted := after m (CalendarRows.report D pub n).events
  let tr := DescriptorParameters.trace L B n a D.initialRows D.phaseRows T lanes pub 0 0 0 counted
  let prepared := tr.post counted
  let stride := DescriptorStride.report L.shape pub 0 prepared
  OnlineWorkspace.armed d L.shape.arity (pub 2) (after prepared stride.events)

theorem Runs.output {D d L B n a lanes pub s m} (h : Runs (w := w) D d L B n a lanes pub s m) :
    let out := finalMemory D d L B n a lanes pub m
    OnlineWorkspace.Ready d L.shape.arity (pub 2) (CalendarRows.rows D n) (levelWords L) out ∧
      Frame.data (DescriptorParameters.saved L w) out =
        DescriptorParameters.outputs L B n a (roundedDown D.p D.q n*lanes) w :=
  h.2.2.2.2.2.2.2

/-- The first actual dispatch on the pair ABI starts from the memory produced
by the seven calls. Its parameter-frame load and internal tag selection are
included in the reported transcript. -/
theorem Runs.first_dispatch {D d L B n a lanes pub s m}
    (h : Runs (w := w) D d L B n a lanes pub s m)
    {C : Schedule.Catalog d} (plan : Schedule.Online.Config C D.initialRows D.phaseRows)
    (arity : L.shape.arity = Schedule.arity C)
    (nonempty : 0 < (CalendarRows.rows D n : Word w)) (j : Fin (D.initialRows+D.phaseRows)) (hj : j.val = 0)
    (fits : Schedule.Online.N d (D.initialRows+D.phaseRows) ≤ 2^w)
    {cap : ℕ} (budget : 30+2*(D.initialRows+D.phaseRows)+2*Schedule.Online.N d (D.initialRows+D.phaseRows)+5 ≤ cap) :
    let out := finalMemory D d L B n a lanes pub m
    let P := Workspace.ports (Schedule.arity C) (pub 2)
    let rep := Schedule.Online.linked P (Schedule.Online.calendarIndex d (D.initialRows+D.phaseRows))
      (Schedule.LevelCalendar.dispatchReport (Schedule.Online.calendar plan) P.data out (Schedule.Online.phaseIndex plan j))
    Call (OnlineWorkspace.table plan) pub (cap+24) 0 out (Workspace.report (pub 2) out rep) := by
  have ready := h.output.1
  rw [arity] at ready
  exact OnlineWorkspace.first_dispatch plan pub 0 _ _ _ ready nonempty j hj fits budget

/-- At the actual cursor position count, one length threshold establishes
the complete startup for every entry state and memory, for every number of
levels allocated beyond the first header. -/
theorem eventually_run (D : CalendarRows.Spec) (d : ℕ) (F : Shape) (B a lanes : ℕ)
    (hB : 1 ≤ B) (hq : 0 < D.q) (hph : 0 < D.phaseRows)
    (hθ : (D.p : ℝ)/D.q ≤ 1) (hlanes : lanes ≤ B)
    (arity : 7 ≤ F.arity) (scalars : 14 ≤ F.scalarFields)
    {base : ℕ → ℕ} (hb : PolynomiallyBounded base) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (levels : ℕ) (pub : Fin 11 → Word (wordBits B n)),
      (pub 2).val = base n → (pub 6).val = n → (pub 7).val = addressBits B n →
      ∀ s m, Runs D d (LevelFields.tightDirectory ⟨F,base n,initialPositions B n,levels⟩
        (CalendarRows.rows D n)) B n a lanes pub s m := by
  filter_upwards [eventually_input D B hB hq hph,
    DescriptorParameters.eventually_tight_capacity D F B a lanes hB hθ hlanes hb] with n ready cap
  intro levels pub base_eq length_eq address_eq s m
  obtain ⟨lanes_fit, capacity⟩ := cap (initialPositions B n) levels
  exact run D d _ B n a lanes pub s m (ready _ pub base_eq length_eq address_eq) rfl hB
    lanes_fit arity scalars rfl capacity

end CompressorRecords.OnlineCursorStartup

end VPVNP
end Computability
end OAI
