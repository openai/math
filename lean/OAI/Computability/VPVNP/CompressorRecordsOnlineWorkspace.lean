import OAI.Computability.VPVNP.CompressorRecordsOnline
import OAI.Computability.VPVNP.CompressorRecordsWorkspace
import OAI.Computability.VPVNP.CompressorDescriptorStride
import OAI.Computability.VPVNP.CompressorCalendarRows

/-!
# The online descriptor scheduler on the pair program's native ABI

The outer program gives the pair workspace in public word two. Every
descriptor call snapshots six pointer words there, then runs the same online
calendar, planner, launch, or worker stage that the internal tag selected.
The snapshot preserves the persistent result and all branch choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.OnlineWorkspace

open BurstRAM BurstRAM.PrivateRAM Schedule
open scoped Fin.CommRing

variable {w d initial phases : ℕ} {C : Catalog d} (plan : Online.Config C initial phases)

/-- Compile the online scheduler with a workspace-pointer snapshot at entry and expose it
through the pair program's eleven public words. Public word two supplies the workspace
base. -/
def table := LiveStageLink.widen (Frame.compile (Online.template plan)) (Function.Embedding.refl _)
  (fun _ : Fin 1 ↦ (2 : Fin 11))

/-- Instantiate the framed online scheduler with the actual eleven public words of the pair
program. -/
abbrev program (pub : Fin 11 → Word w) := ((table plan).instantiate w pub).program
/-- Addresses used by the online scheduler for this catalog, computed from its maximum operand
count and the workspace base in public word two. -/
abbrev ports (pub : Fin 11 → Word w) := Workspace.ports (arity C) (pub 2)

theorem execute_dispatch (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bits : List Bool) (cap : ℕ) (h : Workspace.Installed (arity C) (pub 2) m) :
    execute (program plan pub) cap ((program plan pub).start s) m bits =
      (execute (Online.program plan (ports (C := C) pub)) (cap-24)
        ((Online.program plan (ports (C := C) pub)).start s) m bits).map (Workspace.report (pub 2) m) := by
  unfold program table
  rw [LiveStageLink.execute_widen_start]
  change execute (Frame.machine (Online.template plan) (pub 2)).program cap
    ((Frame.machine (Online.template plan) (pub 2)).program.start s) m bits = _
  rw [Frame.execute_cap, show (Frame.data (pub 2) m : Fin 6 → Word w) = _ from h]
  rfl

/-- Six external reads and eighteen private ticks precede each native linked
source report, including the reports that switch from a planner to a worker. -/
theorem execute_linked (pub : Fin 11 → Word w) (s : Word w) (m : Memory w) (bs : List Bool)
    (h : Workspace.Installed (arity C) (pub 2) m) (fuel : ℕ) (rep : Report w)
    (run : let S := Online.program plan (ports (C := C) pub)
      execute S fuel (S.start s) m bs = some rep) :
    let out := Workspace.report (pub 2) m rep
    execute (program plan pub) (fuel+24) ((program plan pub).start s) m bs = some out ∧
      out.events.length = 24+rep.events.length ∧ out.probes = 6+rep.probes ∧
      choiceBits out.events = choiceBits rep.events ∧ after m out.events = after m rep.events ∧
      out.result = rep.result := by
  refine ⟨?_, Workspace.report_effect _ _ _⟩
  dsimp only at run ⊢
  rw [execute_dispatch plan pub s m bs _ h, Nat.add_sub_cancel, run]
  rfl

/-- The native linker's data tag is inside the pair workspace. It is distinct
from the enclosing stage tag whenever that tag precedes the workspace. -/
theorem tag_ne_outer (g : ℕ) (base outer : Word w) (h : outer.val < base.val)
    (fit : base.val+6 < 2^w) : (Workspace.ports g base).tag ≠ outer := by
  have v : (base+6 : Word w).val = base.val+6 := by
    change (base+((6 : ℕ) : Word w)).val = _
    rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (show 6 < 2^w by omega),Nat.mod_eq_of_lt fit]
  intro eqn
  have hx := congrArg Fin.val eqn
  change (base+6 : Word w).val = _ at hx
  omega

/-- Prepend the workspace-pointer snapshot to each source report, reading the pointer bank in
the memory left by preceding reports. -/
def framed (base : Word w) : Memory w → List (Report w) → List (Report w)
  | _, [] => []
  | m, rep :: rest => Workspace.report base m rep :: framed base (after m rep.events) rest

/-- Only the pointer bank must be available at call boundaries. The active
frame, stage tag, ordinal and all level records may change across calls. -/
def Banks (g : ℕ) (base : Word w) : Memory w → List (Report w) → Prop
  | _, [] => True
  | m, rep :: rest => Workspace.Installed g base m ∧ Banks g base (after m rep.events) rest

theorem run_framed (pub : Fin 11 → Word w) (fuel : ℕ) (st : Option (Word w)) (m : Memory w)
    (bits : List (List Bool)) (rs : List (Report w))
    (hr : runSegment (Online.program plan (ports (C := C) pub)) fuel st m bits = some rs)
    (hb : Banks (arity C) (pub 2) m rs) :
    runSegment (program plan pub) (fuel+24) st m bits = some (framed (pub 2) m rs) := by
  induction bits generalizing st m rs with
  | nil =>
    have : rs = [] := (Option.some.inj hr).symm
    subst rs; rfl
  | cons b bits ih =>
    cases st with
    | none => contradiction
    | some s =>
      let S := Online.program plan (ports (C := C) pub)
      cases hc : execute S fuel (S.start s) m b with
      | none => simp [runSegment, ← show S = Online.program plan (ports (C := C) pub) by rfl, hc] at hr
      | some rep =>
        simp only [runSegment, ← show S = Online.program plan (ports (C := C) pub) by rfl, hc,
          Option.map_eq_some_iff] at hr
        obtain ⟨tail,ht,rfl⟩ := hr
        obtain ⟨he,_,_,_,hm,hs⟩ := execute_linked plan pub s m b hb.1 fuel rep hc
        rw [runSegment, he]
        simp only [hs,hm,ih _ _ _ ht hb.2,Option.map_some,framed]

theorem framed_effect (base : Word w) (m : Memory w) (rs : List (Report w)) (st : Option (Word w)) :
    endState st (framed base m rs) = endState st rs ∧
      after m (eventLog (framed base m rs)) = after m (eventLog rs) ∧
      RAMBuckets.cost Report.probes (framed base m rs) = 6*rs.length + RAMBuckets.cost Report.probes rs := by
  induction rs generalizing m st with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons x xs ih =>
    obtain ⟨_,hp,_,hm,hs⟩ := Workspace.report_effect base m x
    obtain ⟨h₁,h₂,h₃⟩ := ih (after m x.events) x.result
    refine ⟨?_,?_,?_⟩
    · simpa only [framed,endState,hs] using h₁
    · simp only [framed,eventLog,List.flatMap_cons,after,List.foldl_append]
      change after (after m (Workspace.report base m x).events) (eventLog (framed base (after m x.events) xs)) = _
      rw [hm]; exact h₂
    · simp only [framed,RAMBuckets.cost,hp,h₃,List.length_cons]
      omega

/-- The calendar's level stride occupies the word immediately before the
first directory row. -/
def gap (g : ℕ) (base : Word w) : Word w := base + ((10+g : ℕ) : Word w)

theorem gap_eq (g : ℕ) (base : Word w) : (Workspace.ports g base).directory-1 = gap g base := by
  simp only [Workspace.ports,gap,Nat.cast_add,Nat.cast_ofNat]
  ring

/-- Ready state of the workspace on the first calendar call. -/
structure Ready (d g : ℕ) (base rows stride : Word w) (m : Memory w) : Prop where
  bank : Workspace.Installed g base m
  tag : m (Workspace.ports g base).tag.val = ((d+1 : ℕ) : Word w)
  ordinal : m (Workspace.ports g base).ordinal.val = 0
  count : m (Workspace.ports g base).rows.val = rows
  pitch : m ((Workspace.ports g base).directory-1).val = stride

private theorem address_ne (base : Word w) {i j : ℕ} (hi : i < 2^w) (hj : j < 2^w) (e : i ≠ j) :
    (base+(i : Word w)).val ≠ (base+(j : Word w)).val := by
  intro he
  have hv := congrArg Fin.val (show (i : Word w) = (j : Word w) from add_left_cancel (Fin.ext he))
  simp only [Fin.val_natCast,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at hv
  exact e hv

/-- Memory after the setup reports install the workspace pointer bank, reset the ordinal, and
select the calendar as the next stage. -/
def armed (d g : ℕ) (base : Word w) (m : Memory w) : Memory w :=
  after (after m (Workspace.initReport g base).events) (Workspace.calendarReport d base).events

/-- Two native accepting setup calls install the pointer bank and select the
calendar. The earlier row-count and stride computations survive both calls. -/
theorem arm (d g : ℕ) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (rows stride : Word w) (fit : 10+g < 2^w)
    (hr : m (Workspace.ports g (pub 2)).rows.val = rows) (hp : m (gap g (pub 2)).val = stride) :
    let base := pub 2
    let A := (Workspace.initMachine g pub).program
    let B := ((Workspace.calendarStart d).instantiate w pub).program
    let mid := after m (Workspace.initReport g base).events
    execute A 42 (A.start s) m [] = some (Workspace.initReport g base) ∧
      execute B 6 (B.start 0) mid [] = some (Workspace.calendarReport d base) ∧
      Ready d g base rows stride (armed d g base m) := by
  let base := pub 2
  let mid := after m (Workspace.initReport g base).events
  have room : 8 < 2^w := by omega
  have mg : mid (gap g base).val = stride := by
    apply Eq.trans (Workspace.init_outside g base m (gap g base).val _) hp
    intro i
    exact address_ne base fit (i.isLt.trans room) (by have := i.isLt; omega)
  have me := (Workspace.calendar_effect d g base mid).1
  have eqn : armed d g base m = writeMemory mid (Workspace.ports g base).tag ((d+1 : ℕ) : Word w) := me
  refine ⟨Workspace.execute_init g pub s m [] 42 le_rfl,
    Workspace.execute_calendarStart d pub 0 mid [] 6 le_rfl, ?_⟩
  constructor
  · exact Workspace.calendar_installed d g base mid (Workspace.init_installed _ _ _ room.le) (by omega)
  · change armed d g base m (Workspace.ports g base).tag.val = _
    rw [eqn]; simp [writeMemory]
  · have hn : (base+7).val ≠ (base+6).val := address_ne base (i := 7) (j := 6) (by omega) (by omega) (by decide)
    change armed d g base m (base+7).val = 0
    rw [eqn]
    change (if (base+7).val = (base+6).val then _ else mid (base+7).val) = _
    rw [ite_eq_right hn]
    exact (Workspace.init_controls g base m room.le).2
  · have hn : (base+8).val ≠ (base+6).val := address_ne base (i := 8) (j := 6) (by omega) (by omega) (by decide)
    change armed d g base m (base+8).val = _
    rw [eqn]
    change (if (base+8).val = (base+6).val then _ else mid (base+8).val) = _
    rw [ite_eq_right hn]
    exact (Workspace.init_rowCount g base m room).trans hr
  · rw [gap_eq]
    change armed d g base m (gap g base).val = _
    rw [eqn]
    change (if (gap g base).val = (base+6).val then _ else mid (gap g base).val) = _
    have hn : (gap g base).val ≠ (base+6).val := address_ne base fit (j := 6) (by omega) (by omega)
    rw [ite_eq_right hn]
    exact mg

theorem frame_after_count (base count : Word w) (m : Memory w) (fit : 16 < 2^w) :
    (Frame.data (base+9) (writeMemory m (base+8) count) : Fin 8 → Word w) = Frame.data (base+9) m := by
  funext i
  have haddr : base+9+(i.val : Word w) = base+((9+i.val : ℕ) : Word w) := by
    rw [Nat.cast_add,Nat.cast_ofNat,add_assoc]
  have h : (base+9+(i.val : Word w)).val ≠ (base+8).val := by
    rw [haddr]
    exact address_ne base (i := 9+i.val) (j := 8) (by have := i.isLt; omega) (by omega) (by omega)
  change writeMemory m (base+8) count (base+9+(i.val : Word w)).val = _
  exact ite_eq_right h

/-- The stride computation is a one-call outer setup stage. Its original
persistent return is closed by the existing single-call stage wrapper. -/
def strideTable (F : DescriptorSpace.Shape) := LiveOneShot.oneShot (DescriptorStride.table F)

theorem stride_and_arm (d : ℕ) (L : DescriptorSpace.Layout) (pub : Fin 11 → Word w)
    (s : Word w) (m : Memory w) (rows : Word w) {row tag : Word w} {b l a W start : ℕ}
    (frame : Frame.data (pub 2+9) m = CursorRAM.ScheduleInit.inputs row tag b l a W start)
    (positions : (b+l)*2^b*2^l = L.positions) (fit : 10+L.shape.arity < 2^w)
    (count : m (pub 2+8).val = rows) :
    let g := L.shape.arity
    let base := pub 2
    let S := ((strideTable L.shape).instantiate w pub).program
    let es := (DescriptorStride.report L.shape pub s m).events
    let m' := after m es
    let A := (Workspace.initMachine g pub).program
    let B := ((Workspace.calendarStart d).instantiate w pub).program
    execute S (1+DescriptorStride.cost L.shape) (S.start s) m [] = some ⟨es,none⟩ ∧
      execute A 42 (A.start 0) m' [] = some (Workspace.initReport g base) ∧
      execute B 6 (B.start 0) (after m' (Workspace.initReport g base).events) [] =
        some (Workspace.calendarReport d base) ∧
      Ready d g base rows (DescriptorSpace.levelWords L : Word w) (armed d g base m') := by
  obtain ⟨hs,_,hm,_,_⟩ := DescriptorStride.native L pub s m frame positions
  have hr : after m (DescriptorStride.report L.shape pub s m).events (pub 2+8).val = rows := by
    rw [hm]
    have h : (pub 2+8).val ≠ (pub 2+((10+L.shape.arity : ℕ) : Word w)).val :=
      address_ne (pub 2) (i := 8) (by omega) fit (by omega)
    simpa only [writeMemory,h,↓reduceIte] using count
  have hp : after m (DescriptorStride.report L.shape pub s m).events (gap L.shape.arity (pub 2)).val =
      (DescriptorSpace.levelWords L : Word w) := by rw [hm]; simp [gap, writeMemory]
  refine ⟨?_, arm d L.shape.arity pub 0 _ _ _ fit hr hp⟩
  dsimp only [strideTable]
  rw [LiveOneShot.execute_oneShot]
  change (execute _ _ (((DescriptorStride.table L.shape).instantiate w pub).program.start s) m []).map _ = _
  rw [hs]
  rfl

theorem tag_is_calendar (q d g : ℕ) {base rows stride : Word w} {m : Memory w}
    (ready : Ready d g base rows stride m) :
    m (Workspace.ports g base).tag.val = LiveStageLink.tagWord w (Online.calendarIndex d q) := by
  rw [ready.tag]
  simp [Online.calendarIndex, LiveStageLink.tagWord]

/-- The calendar runs one fixed prefix and one fixed phase block for each of the
paper's logarithmically many compression blocks. -/
def rowsSpec (initial phases p q : ℕ) : CalendarRows.Spec := ⟨p,q,initial,phases⟩

/-- Run all four native metadata stages in the pair ABI. The cursor-parameter
producer has already installed its eight-word frame. The row counter reads
the input length, the stride stage reads the cursor frame, and the final two
stages publish the six pointers and select the calendar. -/
theorem bootstrap (p q : ℕ) (L : DescriptorSpace.Layout) (pub : Fin 11 → Word w)
    (s : Word w) (m : Memory w) (n : ℕ) (arityEq : L.shape.arity = arity C)
    (hq : 0 < q) (hn : (pub 6).val = n) (hp : p < 2^w) (hpow : n^p < 2^w) (hr : 2^q < 2^w)
    {row tag : Word w} {b l a W start : ℕ}
    (frame : Frame.data (pub 2+9) m = CursorRAM.ScheduleInit.inputs row tag b l a W start)
    (positions : (b+l)*2^b*2^l = L.positions) (fit : 10+arity C < 2^w) (frameFit : 16 < 2^w) :
    let g := arity C
    let base := pub 2
    let D := rowsSpec initial phases p q
    let Q := ((CalendarRows.table D).instantiate w pub).program
    let qrep := CalendarRows.report D pub n
    let m₁ := after m qrep.events
    let S := ((strideTable L.shape).instantiate w pub).program
    let es := (DescriptorStride.report L.shape pub 0 m₁).events
    let m₂ := after m₁ es
    let A := (Workspace.initMachine g pub).program
    let B := ((Workspace.calendarStart d).instantiate w pub).program
    execute Q (CalendarRows.ticks D n + 2) (Q.start s) m [] = some qrep ∧
      execute S (1+DescriptorStride.cost L.shape) (S.start 0) m₁ [] = some ⟨es,none⟩ ∧
      execute A 42 (A.start 0) m₂ [] = some (Workspace.initReport g base) ∧
      execute B 6 (B.start 0) (after m₂ (Workspace.initReport g base).events) [] =
        some (Workspace.calendarReport d base) ∧
      Ready d g base ((initial+phases*Compression.blockCount ((p : ℝ)/q) n : ℕ) : Word w)
        (DescriptorSpace.levelWords L : Word w) (armed d g base m₂) := by
  let D := rowsSpec initial phases p q
  let m₁ := after m (CalendarRows.report D pub n).events
  have hm : m₁ = writeMemory m (pub 2+8) (CalendarRows.rows D n) := CalendarRows.after_report D pub n m
  have frame' : Frame.data (pub 2+9) m₁ = CursorRAM.ScheduleInit.inputs row tag b l a W start := by
    rw [hm,frame_after_count _ _ _ frameFit,frame]
  have cnt : m₁ (pub 2+8).val = (CalendarRows.rows D n : Word w) := by rw [hm]; simp [writeMemory]
  have hs := stride_and_arm d L pub 0 m₁ _ frame' positions (by rwa [arityEq]) cnt
  rw [arityEq,CalendarRows.rows_eq] at hs
  exact ⟨CalendarRows.execute_native D pub s m [] n hq hn hp hr hpow le_rfl,hs⟩

/-- At ordinal zero the calendar passes the first actual level header to
its planner, directly after the last reserved directory row. -/
theorem first_header (pub : Fin 11 → Word w) (m : Memory w) (rows stride : Word w)
    (ready : Ready d (arity C) (pub 2) rows stride m) :
    LevelCalendar.header (Online.calendar plan) (ports (C := C) pub).data m =
      (ports (C := C) pub).directory + ((arity C+3 : ℕ) : Word w)*rows := by
  let A := Online.calendar plan
  have level : A.level 0 = 0 := by
    unfold LevelCalendar.Calendar.level
    split <;> simp
  change _ + ((A.rowPitch : ℕ) : Word w)*m (Workspace.ports (arity C) (pub 2)).rows.val +
    _*(A.level (m (Workspace.ports (arity C) (pub 2)).ordinal.val).val : Word w) = _
  rw [ready.count, ready.ordinal]
  simp only [Fin.val_zero,level,Nat.cast_zero,mul_zero,add_zero]
  rfl

/-- The first nonempty calendar call executes on the enclosing eleven-word
table with the complete pointer-loading and stage-selection transcripts. -/
theorem first_dispatch (pub : Fin 11 → Word w) (state : Word w) (m : Memory w) (rows stride : Word w)
    (ready : Ready d (arity C) (pub 2) rows stride m) (nonempty : 0 < rows)
    (j : Fin (initial+phases)) (hj : j.val = 0) (fits : Online.N d (initial+phases) ≤ 2^w)
    {cap : ℕ} (budget : 30+2*(initial+phases)+2*Online.N d (initial+phases)+5 ≤ cap) :
    let P := ports (C := C) pub
    let rep := Online.linked P (Online.calendarIndex d (initial+phases))
      (LevelCalendar.dispatchReport (Online.calendar plan) P.data m (Online.phaseIndex plan j))
    execute (program plan pub) (cap+24) ((program plan pub).start state) m [] =
      some (Workspace.report (pub 2) m rep) := by
  let P := ports (C := C) pub
  have active : m P.ordinal.val < m P.rows.val := by rw [ready.ordinal,ready.count]; exact nonempty
  have phase : (Online.calendar plan).phase (m P.ordinal.val).val = j.val := by
    rw [ready.ordinal,hj]
    simp only [Fin.val_zero,LevelCalendar.Calendar.phase]
    by_cases h : 0 < (Online.calendar plan).initial.length
    · simp [h]
    · have hz : (Online.calendar plan).initial.length = 0 := by omega
      simp [hz]
  have hc := Online.calendar_call plan P state m j (tag_is_calendar _ _ _ ready) fits active phase budget
  exact (execute_linked plan pub state m [] ready.bank cap _ hc).1

end CompressorRecords.OnlineWorkspace

end VPVNP
end Computability
end OAI
