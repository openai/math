import OAI.Computability.VPVNP.CompressorInitialScriptPackets
import OAI.Computability.VPVNP.CompressorHeaderOperands
import OAI.Computability.VPVNP.CompressorWindowPrepared
import OAI.Computability.VPVNP.CompressorBlockStartupPrefix

/-!
# Running the four initial visits inside the online scheduler

The source packets start from the transferred startup memory. For each
of the four actual phase indices, the runtime calendar locates level zero.
Its recipe reads the row count, pitch, and persistent data and launches
the source with those same operands. The interval retains the source
memory throughout the descriptor suffix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.InitialOnline

open BurstRAM DescriptorSpace BlockPlanner SourceTransport Schedule InitialScriptPackets
open scoped Fin.CommRing
open private port_bounds from OAI.Computability.VPVNP.CompressorOnlineFootprint
open private calendar_agree from OAI.Computability.VPVNP.CompressorWindowPrepared

variable {w : ℕ} (A : Script) (L : Layout) (base : Word w)
local notation "pt" => Workspace.ports (arity A.catalog) base
local notation "H" => levelStart L 0
local notation "gap" => Fin.val (Ports.directory pt - 1)
local notation "Pkt" => SourceWalk.Packet (SourceOnline.Visit A w) w

private theorem low_controls (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base) (fit : H < 2^w) :
    (pt).rows.val < H ∧ gap < H := by
  obtain ⟨dir,_,_,_⟩ := port_bounds A L base hg hb fit
  have before : directoryBase L ≤ H := by simp [levelStart,levelsBase]
  have ahead : L.base + 8 < directoryBase L := by simp only [directoryBase,plannerTag,frameBase]; omega
  have rowsFit : base.val+8 < 2^w := hb ▸ (ahead.trans_le before).trans fit
  constructor
  · change (base.val+(8 : Word w).val)%2^w < H
    rw [show (8 : Word w).val = 8 from Nat.mod_eq_of_lt (by omega : 8 < 2^w),Nat.mod_eq_of_lt rowsFit,hb]
    exact ahead.trans_le before
  · have nz : (pt).directory ≠ 0 := by
      intro h
      rw [h,Fin.val_zero] at dir
      omega
    rw [Fin.val_sub_one_of_ne_zero nz,dir]
    omega

private theorem input_before (cap : ℕ) (ps : List Pkt) (m : Memory w)
    (chron : SourceWalk.Chronological SourceOnline.Visit.Runs m ps)
    (checks : ∀ p ∈ ps, SourceOnline.Checked A L cap p) (x : ℕ) (below : x < H) :
    ∀ p ∈ ps, p.input x = m x := by
  induction ps generalizing m with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨rfl,_,tail⟩ := chron
    have keep : p.output x = p.input x := after_outside _ (checks p List.mem_cons_self).write (not_le_of_gt below)
    intro q hq
    rcases List.mem_cons.mp hq with rfl|mem
    · rfl
    · exact (ih p.output tail (fun j hj ↦ checks j (List.mem_cons_of_mem _ hj)) q mem).trans keep

/-- The calendar uses the literal initial ordinal as its phase label and
level zero as its header, including at the fourth role-publication visit. -/
private theorem phase (i : Fin A.initial.length) :
    (Online.calendar A.plan).phase i.val = i.val ∧ (Online.calendar A.plan).level i.val = 0 := by
  have eqn : (Online.calendar A.plan).initial.length = A.initial.length := by
    simp [Online.calendar,LevelCalendar.recipeCalendar]
  have bound : i.val < (Online.calendar A.plan).initial.length := by rw [eqn]; exact i.isLt
  simp only [LevelCalendar.Calendar.phase,LevelCalendar.Calendar.level,ite_eq_left bound,and_self]

theorem prepared (a : ℕ) (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base)
    (nonempty : 0 < L.levels) (fields : 14 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (order : A.initial = BlockInitialPackets.order L a) (i : Fin A.initial.length) (p : Pkt)
    (index : p.stage.phase = i.castAdd A.block.length)
    (evaluated : p.stage = HeaderPacket.attach A p.stage.phase (pt).data (BlockHeaderRun.header w L 0) p.input
      p.stage.fuel p.stage.choices)
    (count : p.input (pt).rows.val = (directoryRows L : Word w)) (pitch : p.input gap = (levelWords L : Word w))
    (room : i.val < directoryRows L) :
    SourceOnline.Prepared A L base i.val (directoryRows L) p := by
  have firstFit : H < 2^w := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  have baseEq : base = (L.base : Word w) := Fin.ext (by rw [Fin.val_natCast,← hb,Nat.mod_eq_of_lt base.isLt])
  have first : BlockHeaderPlan.firstHeader.eval (pt).data (BlockHeaderRun.header w L 0) p.input =
      BlockHeaderRun.header w L 0 := by
    rw [hg]
    exact BlockHeaderPlan.firstHeader_eval L base p.input _ baseEq count
  have member : A.visit p.stage.phase ∈ BlockInitialPackets.order L a := by
    rw [index,A.initial_visit,← order]
    exact List.getElem_mem ..
  let data := Window.operandRegion A L base
  have support := HeaderOperands.initial data (pt).data (BlockHeaderRun.header w L 0) p.input L a
    nonempty fields fit (.inl rfl) (.inr (.inl rfl)) (fun _ h ↦ .inr (.inr h)) first _ member
  intro live ag ordinal total _ livePitch
  have active : live (pt).ordinal.val < live (pt).rows.val := Fin.lt_def.mpr (ordinal ▸ total ▸ room)
  have liveCount : live (pt).rows.val = (directoryRows L : Word w) := by
    apply Fin.ext; rw [Fin.val_natCast,← total,Nat.mod_eq_of_lt (live _).isLt]
  obtain ⟨pc,level⟩ := phase A i
  refine ⟨pc.trans (congrArg Fin.val index.symm),?_⟩
  have dir := (port_bounds A L base hg hb firstFit).1
  have dirWord : (pt).data 1 = (directoryBase L : Word w) := by
    apply Fin.ext; rw [Fin.val_natCast,← dir,Nat.mod_eq_of_lt (pt).directory.isLt]; rfl
  have entry := LevelFields.eval_calendar_entry (Online.calendar A.plan) (pt).data live L dirWord
    (congrArg (·+3) hg) liveCount livePitch
  have head : A.recipeState base live = BlockHeaderRun.header w L 0 := by
    have h := entry.pointer
    change A.recipeState base live = ((levelStart L (A.levelsPerBlock*(Online.calendar A.plan).level
      (live (pt).ordinal.val).val) : ℕ) : Word w) at h
    rwa [ordinal,level,Nat.mul_zero] at h
  have agree := calendar_agree L base hg hb firstFit p.input live p.stage.phase ag (count.trans liveCount.symm)
    (pitch.trans livePitch.symm)
  have eqn (e : PhaseRecipe.Expr) (rd : e.ReadsFrom data (pt).data (BlockHeaderRun.header w L 0) p.input) :
      A.operand base live p.stage.phase e = e.eval (pt).data (BlockHeaderRun.header w L 0) p.input := by
    unfold Script.operand
    rw [head]
    exact (e.eval_eq_of_reads rd agree).symm
  apply SourceOnline.launch_of_evaluation A base L hg hb firstFit live p.stage (ordinal ▸ room) active
  · exact (eqn _ support.initial).trans (congrArg SourceOnline.Visit.start evaluated).symm
  · exact (eqn _ support.stop).trans (congrArg SourceOnline.Visit.stop evaluated).symm
  · intro j
    have h : (p.stage.params j) = ((A.visit p.stage.phase).params j).eval (pt).data (BlockHeaderRun.header w L 0) p.input := by
      cases p with
      | mk v input rs =>
        cases v
        simp only [HeaderPacket.attach,SourceOnline.Visit.mk.injEq,heq_eq_eq,true_and,and_true] at evaluated
        exact congrFun evaluated.2.2 j
    exact (eqn _ (support.params j)).trans h.symm

/-- The four catalog phases run online with the same reports and choices as
their raw workers. The next ordinal is four, and every suffix word agrees
with the typed level-zero result. -/
theorem interval (a b l width cap : ℕ) (hcap : budget A L a ≤ cap) (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base)
    (nonempty : 0 < L.levels) (fields : 14 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (order : A.initial = BlockInitialPackets.order L a) (m : Memory w)
    (walk : SourceWalk (BlockInitialPackets.Source L a (pt).data (BlockHeaderRun.header w L 0))
      (BlockInitialPackets.order L a) m (BlockInitialPackets.logs L a b l width m))
    (live : 4 ≤ directoryRows L) (ord : m (pt).ordinal.val = 0) (total : (m (pt).rows.val).val = directoryRows L)
    (tag : m (pt).tag.val = LiveStageLink.tagWord w (Online.calendarIndex A.size A.size))
    (pitch : m gap = (levelWords L : Word w)) :
    ∃ steps : List (Online.Run.Step A.size A.size w),
      Online.Run.Interval A.plan pt cap m steps ∧ steps.map Online.Run.Step.phase = indices A ∧
      (steps.map (fun step ↦ step.row.reports)).flatten = BlockInitialPackets.logs L a b l width m ∧
      Agree (H ≤ ·) (BlockInitialPackets.post L a b l width m)
        (Online.Run.finalMemory (C := A.catalog) pt m steps) ∧
      ((Online.Run.finalMemory (C := A.catalog) pt m steps) (pt).ordinal.val).val = 4 ∧
      (Online.Run.finalMemory (C := A.catalog) pt m steps) (pt).rows.val = m (pt).rows.val ∧
      (Online.Run.finalMemory (C := A.catalog) pt m steps) gap = m gap ∧
      SourceBankFrame.Stable (base.val+6) m (Online.Run.intervalLog A.plan pt m steps) := by
  let s := BlockHeaderRun.header w L 0
  have firstFit : H < 2^w := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  obtain ⟨ps,chron,phases,logs,checks⟩ := attach_initial A L a cap (pt).data s m _ order walk
    (fun i _ ↦ (budget_bounds A L a i).1.trans hcap) (fun i _ ↦ (budget_bounds A L a i).2.trans hcap)
  have hi : A.initial.length = 4 := by rw [order]; rfl
  have len : ps.length = A.initial.length := by simpa [indices] using congrArg List.length phases
  have native (p : Pkt) (h : p ∈ ps) := (checks p h).1
  have ⟨rowLow,gapLow⟩ := low_controls A L base hg hb firstFit
  have cnt : m (pt).rows.val = (directoryRows L : Word w) := by
    apply Fin.ext; rw [Fin.val_natCast,← total,Nat.mod_eq_of_lt (m _).isLt]
  have prep (i : Fin ps.length) : SourceOnline.Prepared A L base (0+i.val) (directoryRows L) ps[i.val] := by
    let j := i.cast len
    let p := ps[i.val]
    have mem : p ∈ ps := List.getElem_mem ..
    have index : p.stage.phase = j.castAdd A.block.length := by
      apply Fin.ext
      have eqn := congrArg (fun xs : List (Fin A.size) ↦ (xs[i.val]?).map Fin.val) phases
      simpa [indices,List.getElem?_eq_getElem,i.isLt,show i.val < A.initial.length by exact j.isLt,j,p] using eqn
    have kept (x : ℕ) (below : x < H) : p.input x = m x := input_before A L cap ps m chron native x below p mem
    simp only [Nat.zero_add]
    exact prepared A L base a hg hb nonempty fields fit order j p index (checks p mem).2
      ((kept _ rowLow).trans cnt) ((kept _ gapLow).trans pitch) (j.isLt.trans_le (hi ▸ live))
  have start : (m (pt).ordinal.val).val = 0 := congrArg Fin.val ord
  obtain ⟨steps,actual,phaseEq,reportEq,_,agree,done,rows,unchanged,stable⟩ :=
    SourceOnline.interval_stable A L base hg hb firstFit cap 0 (directoryRows L) m m ps chron native prep
      (by omega) le_rfl (fun _ _ ↦ rfl) start total tag pitch
  refine ⟨steps,actual,phaseEq.trans phases,?_,?_,by omega,rows,unchanged,stable⟩
  · rw [reportEq]
    exact logs
  · rw [logs] at agree
    exact agree

end CompressorRecords.InitialOnline

end VPVNP
end Computability
end OAI
