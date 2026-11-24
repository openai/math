import OAI.Computability.VPVNP.PrimedCounterAdminExec
import OAI.Computability.VPVNP.PrimedCounterCallPaths
import OAI.Computability.VPVNP.PrimedInputRAMOnce
import Mathlib.Data.ZMod.Defs

/-!
# Packing the evaluator's advice bit banks

The initial cursor of each output row writes zero to the destination word.
Each of its remaining cursors installs one low-endian bit if that bit lies
in the actual raw advice. The padding cursors leave the partial final word
intact. Every call makes at most three probes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceBanks

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

/-- A native advice-packing flow with 32 registers and five public operands. -/
abbrev PackCode := Flow 32 5
variable {w : ℕ}

/-- Number of cursor positions per packed row, including the initial clear and one position per
source bit. -/
def stride (pub : Fin 5 → Word w) := pub 2 + 1
/-- Number of advice-packing cursor positions across all destination rows. -/
def total (pub : Fin 5 → Word w) := pub 4 * stride pub
/-- Recover the packed row number from a linear packing cursor. -/
def row (pub : Fin 5 → Word w) (st : Word w) := BinaryOp.div.eval st (stride pub)
/-- Recover the position within a packing row, with zero reserved for clearing its destination. -/
def column (pub : Fin 5 → Word w) (st : Word w) := BinaryOp.mod.eval st (stride pub)
/-- The zero-based raw advice bit index corresponding to a bit-installation cursor. -/
def index (pub : Fin 5 → Word w) (st : Word w) := row pub st * pub 2 + (column pub st - 1)
/-- The packed destination word address for the current row. -/
def dst (pub : Fin 5 → Word w) (st : Word w) := pub 1 + row pub st
/-- The raw advice bit address for the current bit-installation cursor. -/
def src (pub : Fin 5 → Word w) (st : Word w) := pub 0 + index pub st

/-- The specified native shift and OR of the bit read and the accumulated destination. -/
def packedValue (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) :=
  BinaryOp.bitOr.eval (m (dst pub st).val) (BinaryOp.shiftLeft.eval (m (src pub st).val) (column pub st - 1))

/-- The memory effect of one packing cursor, clearing a new row, installing an in-range bit, or
skipping padding. -/
def stepMemory (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) : Memory w :=
  if column pub st = 0 then writeMemory m (dst pub st) 0
  else if index pub st < pub 3 then writeMemory m (dst pub st) (packedValue pub st m)
  else m

private def load : PackCode := straight (.constant 0 0)
  [.constant 1 1, .constant 2 2, .publicWord 3 0, .publicWord 4 1, .publicWord 5 2,
   .publicWord 6 3, .publicWord 7 4, .stateWord 8, .binary .add 9 5 1, .binary .mul 30 7 9,
   .binary .div 10 8 9, .binary .mod 11 8 9, .binary .add 12 4 10, .binary .sub 13 11 1,
   .binary .mul 14 10 5, .binary .add 14 14 13, .binary .add 15 3 14, .binary .add 29 8 1]

private def installBit : PackCode := straight (.read 16 15)
  [.guardLt 16 2, .read 17 12, .binary .shiftLeft 18 16 13, .binary .bitOr 19 17 18, .write 12 19]

/-- Public words in order are source bit base, destination word base, field
width, actual source length and number of destination rows. -/
def stepBody : PackCode := .seq load (.seq (.line (.guardLt 8 30))
  (.ifEq 11 0 (.line (.write 12 0)) (.ifLt 14 6 installBit (.line (.copy 20 0)))))

/-- The native call template implementing one advice-packing cursor step. -/
def stepTable := PrimedCounter.Call.template stepBody 29 30

private def loadRegs (pub : Fin 5 → Word w) (st : Word w) (r : Regs w 32) : Regs w 32 :=
  let f : List (Fin 32 × Word w) := [(0,0), (1,1), (2,2), (3,pub 0), (4,pub 1), (5,pub 2),
    (6,pub 3), (7,pub 4), (8,st), (9,stride pub), (30,total pub), (10,row pub st), (11,column pub st),
    (12,dst pub st), (13,column pub st-1), (14,row pub st * pub 2), (14,index pub st),
    (15,src pub st), (29,st+1)]
  f.foldl (fun s x => Function.update s x.1 x.2) r

private def bitRegs (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) (r : Regs w 32) : Regs w 32 :=
  let f : List (Fin 32 × Word w) := [(16,m (src pub st).val), (17,m (dst pub st).val),
    (18,BinaryOp.shiftLeft.eval (m (src pub st).val) (column pub st-1)), (19,packedValue pub st m)]
  f.foldl (fun s x => Function.update s x.1 x.2) r

private def bitEvents (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) : List (Event w) :=
  [.read (src pub st) (m (src pub st).val), .tick, .read (dst pub st) (m (dst pub st).val), .tick,
    .tick, .write (dst pub st) (packedValue pub st m)]

/-- The local ticks and probes of a packing step, selected by the row-clear, in-range bit, or
padding case. -/
def stepEvents (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) : List (Event w) :=
  List.replicate 19 .tick ++ [.tick] ++ .tick ::
    (if column pub st = 0 then [.write (dst pub st) 0] else .tick ::
      (if index pub st < pub 3 then bitEvents pub st m else [.tick]))

/-- The packing step's events and return state, closing at the end of the last row. -/
def stepReport (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) : Report w :=
  ⟨stepEvents pub st m ++ [.tick], if st+1 = total pub then none else some (st+1)⟩

private theorem load_exec (pub : Fin 5 → Word w) (st : Word w) (r : Regs w 32) (m : Memory w) :
    Flow.Exec pub st load r m (List.replicate 19 .tick) (loadRegs pub st r) m :=
  (Flow.once_sound pub st false load r m rfl).1

private theorem installBit_exec (pub : Fin 5 → Word w) (st : Word w) (r : Regs w 32) (m : Memory w)
    (hb : m (src pub st).val < (2 : Word w)) :
    let s := loadRegs pub st r
    Flow.Exec pub st installBit s m (bitEvents pub st m) (bitRegs pub st m s)
      (writeMemory m (dst pub st) (packedValue pub st m)) := by
  intro s
  let readRegs := Function.update s (16 : Fin 32) (m (src pub st).val)
  have hg : Flow.Exec pub st (.line (.guardLt 16 2)) readRegs m [.tick] readRegs m := by
    apply Flow.Exec.line
    change (if m (src pub st).val < (2 : Word w) then some _ else none) = _
    rw [ite_eq_left hb]
  exact (Flow.Exec.line rfl).seq (hg.seq ((Flow.Exec.line rfl).seq
    ((Flow.Exec.line rfl).seq ((Flow.Exec.line rfl).seq (Flow.Exec.line rfl)))))

/-- Every valid cursor produces the specified trace and final memory, with
the next cursor and total in the common closing registers. -/
theorem step_exec (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) (r : Regs w 32)
    (hcur : st < total pub)
    (hbit : column pub st ≠ 0 → index pub st < pub 3 → m (src pub st).val < (2 : Word w)) :
    ∃ out, Flow.Exec pub st stepBody r m (stepEvents pub st m) out (stepMemory pub st m) ∧
      out 29 = st+1 ∧ out 30 = total pub := by
  let s := loadRegs pub st r
  have hg : Flow.Exec pub st (.line (.guardLt 8 30)) s m [.tick] s m := by
    apply Flow.Exec.line
    change (if st < total pub then some _ else none) = _
    rw [ite_eq_left hcur]
  have hl := load_exec pub st r m
  by_cases hz : column pub st = 0
  · rw [stepEvents, stepMemory, ite_eq_left hz, ite_eq_left hz]
    exact ⟨s, hl.seq (hg.seq (.ifEqYes hz (.line rfl))), rfl, rfl⟩
  · by_cases hi : index pub st < pub 3
    · rw [stepEvents, stepMemory, ite_eq_right hz, ite_eq_right hz, ite_eq_left hi, ite_eq_left hi]
      exact ⟨_, hl.seq (hg.seq (.ifEqNo hz (.ifLtYes hi (installBit_exec pub st r m (hbit hz hi))))), rfl, rfl⟩
    · rw [stepEvents, stepMemory, ite_eq_right hz, ite_eq_right hz, ite_eq_right hi, ite_eq_right hi]
      exact ⟨_, hl.seq (hg.seq (.ifEqNo hz (.ifLtNo hi (.line rfl)))), rfl, rfl⟩

theorem stepReport_memory (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) :
    after m (stepReport pub st m).events = stepMemory pub st m := by
  unfold stepReport stepEvents stepMemory
  split_ifs <;> rfl

theorem stepReport_probes_le (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) :
    (stepReport pub st m).probes ≤ 3 := by
  unfold stepReport stepEvents
  split_ifs <;> first | exact (by decide : 1 ≤ 3) | exact (by decide : 3 ≤ 3) | exact (by decide : 0 ≤ 3)

private theorem stepEvents_bounds (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) :
    (stepEvents pub st m).length ≤ 28 ∧ choiceBits (stepEvents pub st m) = [] := by
  unfold stepEvents
  split_ifs <;> exact ⟨by simp [bitEvents], rfl⟩

/-- At most 28 body instructions and two closing instructions. -/
def callFuel : ℕ := 30

theorem stepReport_length_le (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) :
    (stepReport pub st m).events.length ≤ 29 := by
  simpa [stepReport] using Nat.succ_le_succ (stepEvents_bounds pub st m).1

/-- Native execution rejects surplus choice bits. Every valid cursor with a
canonical source bit returns its single deterministic report. -/
theorem execute_step (pub : Fin 5 → Word w) (st : Word w) (m : Memory w)
    (hcur : st < total pub)
    (hbit : column pub st ≠ 0 → index pub st < pub 3 → m (src pub st).val < (2 : Word w))
    (rs : Regs w 32) (priv : Word w → Word w) (choices : List Bool) {fuel : ℕ} (hf : callFuel ≤ fuel) :
    let mach := stepTable.instantiate w pub
    execute mach.program fuel ⟨mach.entry, st, rs, priv⟩ m choices =
      if choices.isEmpty then some (stepReport pub st m) else none := by
  obtain ⟨out, run, hn, ht⟩ := step_exec pub st m rs hcur hbit
  obtain ⟨hlen, hb⟩ := stepEvents_bounds pub st m
  have h := PrimedCounter.Call.execute_body stepBody 29 30 pub st rs priv m run choices
    (fuel - ((stepEvents pub st m).length + 2))
  rw [show (stepEvents pub st m).length + (fuel - ((stepEvents pub st m).length + 2) + 2) = fuel by
    unfold callFuel at hf; omega, hn, ht, hb, List.nil_append] at h
  exact h

private theorem trace_of_straight {pub : Fin 5 → Word w} {st : Word w} {r out : Regs w 32}
    {m mem : Memory w} {es : List (Event w)} {op : Op 32 5} {ops : List (Op 32 5)}
    (h : Flow.Exec pub st (straight op ops) r m es out mem) :
    trace pub st (op :: ops) r m = some (es, out, mem) :=
  (PrimedCounter.Admin.exec_lines_iff_trace (ops := op :: ops) (by simp)).mp h

private theorem guard_result {pub : Fin 5 → Word w} {st : Word w} {r out : Regs w 32}
    {m mem : Memory w} {es : List (Event w)} {i j : Fin 32}
    (h : Flow.Exec pub st (.line (.guardLt i j)) r m es out mem) :
    r i < r j ∧ out = r ∧ mem = m := by
  cases h with
  | line he =>
    by_cases hlt : r i < r j
    · simp only [Op.effect, hlt, ite_true, Option.some.injEq, Prod.mk.injEq] at he
      exact ⟨hlt, he.2.1.symm, he.2.2.symm⟩
    · simp [Op.effect, hlt] at he

/-- The source-range test is imposed only for data columns that read a real bit.
An invalid cursor or a nonbinary word read from that interval cannot exit. -/
theorem step_required {pub : Fin 5 → Word w} {st : Word w} {m mem : Memory w} {r out : Regs w 32}
    {es : List (Event w)} (run : Flow.Exec pub st stepBody r m es out mem) :
    st < total pub ∧ (column pub st ≠ 0 → index pub st < pub 3 → m (src pub st).val < (2 : Word w)) := by
  cases run with
  | seq hl ht =>
    have hx := trace_of_straight hl
    have hy := trace_of_straight (load_exec pub st r m)
    obtain ⟨-, rfl, rfl⟩ := (show _ ∧ _ ∧ _ by simpa using hx.symm.trans hy)
    cases ht with
    | seq hg htail =>
      obtain ⟨hcur, rfl, rfl⟩ := guard_result hg
      refine ⟨hcur, ?_⟩
      intro hz hi
      cases htail with
      | ifEqYes he _ => exact (hz he).elim
      | ifEqNo _ hc =>
        cases hc with
        | ifLtNo hn _ => exact (hn hi).elim
        | ifLtYes _ hb =>
          cases hb with
          | seq hread hrest =>
            cases hread with
            | line he =>
              simp only [Op.effect, Option.some.injEq, Prod.mk.injEq] at he
              obtain ⟨-, rfl, rfl⟩ := he
              cases hrest with
              | seq hg _ => exact (guard_result hg).1

/-- Exact successful reports on arbitrary raw memory and arbitrary choices,
including rejection of nonbinary source words and out-of-range cursors. -/
theorem execute_step_iff (pub : Fin 5 → Word w) (st : Word w) (m : Memory w)
    (rs : Regs w 32) (priv : Word w → Word w) (choices : List Bool) {fuel : ℕ}
    (hf : callFuel ≤ fuel) (rep : Report w) :
    let mach := stepTable.instantiate w pub
    execute mach.program fuel ⟨mach.entry, st, rs, priv⟩ m choices = some rep ↔
      st < total pub ∧ (column pub st ≠ 0 → index pub st < pub 3 → m (src pub st).val < (2 : Word w)) ∧
      choices = [] ∧ rep = stepReport pub st m := by
  constructor
  · intro h
    obtain ⟨_, _, _, run, -⟩ := (PrimedCounter.Call.execute_iff stepBody 29 30 pub st rs priv m choices fuel rep).mp h
    obtain ⟨hc, hb⟩ := step_required run
    rw [execute_step pub st m hc hb rs priv choices hf] at h
    cases choices with
    | nil => exact ⟨hc, hb, rfl, (Option.some.inj h).symm⟩
    | cons => cases h
  · rintro ⟨hc, hb, rfl, rfl⟩
    exact execute_step pub st m hc hb rs priv [] hf

private def stageStart : PackCode := straight (.constant 0 0) [.publicWord 7 4]

private def emptyStage : PackCode := straight (.stateWord 8)
  [.guardEq 8 0, .constant 29 1, .constant 30 1]

/-- The linkable stage treats an empty bank as one accepting call at cursor zero. -/
def stageBody : PackCode := .seq stageStart (.ifEq 7 0 emptyStage stepBody)

/-- The native advice-packing stage template, including the test for a zero row count. -/
def stageTable := PrimedCounter.Call.template stageBody 29 30

/-- The 33-step private clock bound for a native advice-packing stage call. -/
def stageFuel : ℕ := 33

/-- Native report with the row-count test included in the event stream. -/
def stageReport (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) : Report w :=
  if pub 4 = 0 then ⟨List.replicate 8 .tick, none⟩ else
    ⟨List.replicate 3 .tick ++ (stepReport pub st m).events, (stepReport pub st m).result⟩

private def stageRegs (pub : Fin 5 → Word w) (rs : Regs w 32) : Regs w 32 :=
  Function.update (Function.update rs 0 0) 7 (pub 4)

private theorem stageStart_exec (pub : Fin 5 → Word w) (st : Word w) (rs : Regs w 32) (m : Memory w) :
    Flow.Exec pub st stageStart rs m [.tick, .tick] (stageRegs pub rs) m :=
  (Flow.Exec.line rfl).seq (Flow.Exec.line rfl)

theorem execute_stage_step (pub : Fin 5 → Word w) (st : Word w) (m : Memory w)
    (hn : pub 4 ≠ 0) (hc : st < total pub)
    (hb : column pub st ≠ 0 → index pub st < pub 3 → m (src pub st).val < (2 : Word w))
    (rs : Regs w 32) (priv : Word w → Word w) (choices : List Bool) {fuel : ℕ} (hf : stageFuel ≤ fuel) :
    let mach := stageTable.instantiate w pub
    execute mach.program fuel ⟨mach.entry, st, rs, priv⟩ m choices =
      if choices.isEmpty then some (stageReport pub st m) else none := by
  obtain ⟨out, hrun, hnext, ht⟩ := step_exec pub st m (stageRegs pub rs) hc hb
  have hr : Flow.Exec pub st stageBody rs m (List.replicate 3 .tick ++ stepEvents pub st m) out
      (stepMemory pub st m) := (stageStart_exec ..).seq (.ifEqNo hn hrun)
  obtain ⟨hlen, hbits⟩ := stepEvents_bounds pub st m
  have h := PrimedCounter.Call.execute_body stageBody 29 30 pub st rs priv m hr choices
    (fuel - ((stepEvents pub st m).length+5))
  simp only [List.length_append, List.length_replicate] at h
  rw [show 3 + (stepEvents pub st m).length + (fuel - ((stepEvents pub st m).length+5) + 2) = fuel by
      unfold stageFuel at hf; omega,
    hnext, ht] at h
  change execute _ _ _ _ (choiceBits (stepEvents pub st m) ++ choices) = _ at h
  rw [hbits, List.nil_append] at h
  simpa only [stageTable, stageReport, ite_eq_right hn, stepReport, List.append_assoc] using h

theorem execute_stage_empty (pub : Fin 5 → Word w) (m : Memory w) (hz : pub 4 = 0)
    (rs : Regs w 32) (priv : Word w → Word w) (choices : List Bool) {fuel : ℕ} (hf : stageFuel ≤ fuel) :
    let mach := stageTable.instantiate w pub
    execute mach.program fuel ⟨mach.entry, 0, rs, priv⟩ m choices =
      if choices.isEmpty then some (stageReport pub 0 m) else none := by
  let s := stageRegs pub rs
  let s' := Function.update s 8 0
  let out := Function.update (Function.update s' 29 1) 30 1
  have hg : Flow.Exec pub (0 : Word w) (.line (.guardEq 8 0)) s' m [.tick] s' m := by
    apply Flow.Exec.line
    change (if (0 : Word w) = 0 then some _ else none) = _
    rw [ite_eq_left rfl]
  have he : Flow.Exec pub 0 emptyStage s m (List.replicate 4 .tick) out m :=
    (Flow.Exec.line rfl).seq (hg.seq ((Flow.Exec.line rfl).seq (Flow.Exec.line rfl)))
  have hr : Flow.Exec pub 0 stageBody rs m (List.replicate 7 .tick) out m :=
    (stageStart_exec ..).seq (.ifEqYes hz he)
  have h := PrimedCounter.Call.execute_body stageBody 29 30 pub 0 rs priv m hr choices (fuel-9)
  change execute _ (7+(fuel-9+2)) _ _ choices = _ at h
  rw [show 7+(fuel-9+2)=fuel by unfold stageFuel at hf; omega, ite_eq_left (show out 29 = out 30 from rfl)] at h
  have hevents : List.replicate 7 (Event.tick (w := w)) ++ [.tick] = List.replicate 8 .tick :=
    (List.replicate_add 7 1 _).symm
  simpa only [stageTable, stageReport, ite_eq_left hz, hevents] using h

theorem stageReport_memory (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) :
    after m (stageReport pub st m).events = if pub 4 = 0 then m else stepMemory pub st m := by
  by_cases h : pub 4 = 0
  · rw [stageReport, ite_eq_left h, ite_eq_left h]; rfl
  · rw [stageReport, ite_eq_right h, ite_eq_right h]
    exact stepReport_memory ..

theorem stageReport_probes_le (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) :
    (stageReport pub st m).probes ≤ 3 := by
  by_cases h : pub 4 = 0
  · rw [stageReport, ite_eq_left h]; exact (by decide : 0 ≤ 3)
  · rw [stageReport, ite_eq_right h]; exact stepReport_probes_le ..

private theorem stage_required {pub : Fin 5 → Word w} {st : Word w} {m mem : Memory w}
    {rs out : Regs w 32} {es : List (Event w)} (run : Flow.Exec pub st stageBody rs m es out mem) :
    if pub 4 = 0 then st = 0 else
      st < total pub ∧ (column pub st ≠ 0 → index pub st < pub 3 → m (src pub st).val < (2 : Word w)) := by
  cases run with
  | seq head tail =>
    have hx := trace_of_straight head
    have hy := trace_of_straight (stageStart_exec pub st rs m)
    obtain ⟨-, rfl, rfl⟩ := (show _ ∧ _ ∧ _ by simpa using hx.symm.trans hy)
    cases tail with
    | ifEqNo hn hr =>
      change pub 4 ≠ 0 at hn
      rw [ite_eq_right hn]
      exact step_required hr
    | ifEqYes hz hr =>
      change pub 4 = 0 at hz
      rw [ite_eq_left hz]
      cases hr with
      | seq hs rest =>
        cases hs with
        | line he =>
          simp only [Op.effect, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨-, rfl, rfl⟩ := he
          cases rest with
          | seq hg _ =>
            cases hg with
            | line he =>
              by_contra hn
              change (if st = 0 then some _ else none) = _ at he
              rw [ite_eq_right hn] at he
              cases he

/-- The linkable stage also checks the empty bank's initial cursor, and
rejects every surplus branch bit in both branches. -/
theorem execute_stage_iff (pub : Fin 5 → Word w) (st : Word w) (m : Memory w)
    (rs : Regs w 32) (priv : Word w → Word w) (choices : List Bool) {fuel : ℕ}
    (hf : stageFuel ≤ fuel) (rep : Report w) :
    let mach := stageTable.instantiate w pub
    execute mach.program fuel ⟨mach.entry, st, rs, priv⟩ m choices = some rep ↔
      (if pub 4 = 0 then st = 0 else st < total pub ∧
        (column pub st ≠ 0 → index pub st < pub 3 → m (src pub st).val < (2 : Word w))) ∧
      choices = [] ∧ rep = stageReport pub st m := by
  have he (ha : if pub 4 = 0 then st = 0 else st < total pub ∧
      (column pub st ≠ 0 → index pub st < pub 3 → m (src pub st).val < (2 : Word w))) :
      let mach := stageTable.instantiate w pub
      execute mach.program fuel ⟨mach.entry, st, rs, priv⟩ m choices =
        if choices.isEmpty then some (stageReport pub st m) else none := by
    by_cases hz : pub 4 = 0
    · rw [ite_eq_left hz] at ha
      subst st
      exact execute_stage_empty pub m hz rs priv choices hf
    · rw [ite_eq_right hz] at ha
      exact execute_stage_step pub st m hz ha.1 ha.2 rs priv choices hf
  constructor
  · intro h
    obtain ⟨_, _, _, run, -⟩ := (PrimedCounter.Call.execute_iff stageBody 29 30 pub st rs priv m choices fuel rep).mp h
    have ha := stage_required run
    rw [he ha] at h
    cases choices with
    | nil => exact ⟨ha, rfl, (Option.some.inj h).symm⟩
    | cons => cases h
  · rintro ⟨ha, hbits, rfl⟩
    simpa [hbits] using he ha

end LiveEvaluatorAdviceBanks

end VPVNP
end Computability
end OAI
