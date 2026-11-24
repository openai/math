import OAI.Computability.VPVNP.LiveHeaderFields
import OAI.Computability.VPVNP.LiveHeaderRuns
import OAI.Computability.VPVNP.PrimedCounterAdminExec
import OAI.Computability.VPVNP.PrimedCounterRenameRun

/-!
# Fixed-capacity scans with a runtime field count

Each call reads the count from the descriptor and tests the current position
relative to the phase's first cursor. Occupied positions run the actual
payload copy or padding guard. An idle position advances the cursor without
reading the field offset or the packed header. The scheduling capacity can
therefore be public while the length of the occupied interval is private.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader.Allocated

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM PrimedCounter

/-- Public operand indices identifying the first cursor, source-offset cell, destination base,
and runtime count for a bounded field scan. -/
structure Parameters where
  /-- Index of the public word from which the field-relative cursor is measured. -/
  firstCursor : Fin 16
  /-- Index of the public address of the descriptor cell holding the packed source offset. -/
  srcOffsetAddress : Fin 16
  /-- Index of the public destination base used to store copied field bits. -/
  destinationBase : Fin 16
  /-- Index of the public address of the field's live count word. -/
  countAddress : Fin 16

private def setupOps (p : Parameters) : List (Op 48 16) :=
  [.stateWord 4, .publicWord 6 p.firstCursor, .binary .sub 8 4 6,
   .publicWord 6 p.countAddress, .read 9 6]

private def setup (p : Parameters) := lines (setupOps p) (by simp [setupOps])

private def cellRegs : Fin 12 ↪ Fin 48 where
  toFun i := i.castLE (by decide)
  inj' _ _ h := Fin.ext (congrArg (Fin.val : Fin 48 → ℕ) h)

private def cellParams (p : Parameters) : Fin 3 → Fin 16 :=
  ![p.firstCursor, p.srcOffsetAddress, p.destinationBase]

private def cellOps (slot : Fin 4) (padding : Bool) :=
  if padding then checkPaddingCell slot else copyFieldCell slot

private theorem cell_ne_nil (slot : Fin 4) (padding : Bool) : cellOps slot padding ≠ [] := by
  cases padding <;> exact List.cons_ne_nil _ _

private def activeCell (p : Parameters) (slot : Fin 4) (padding : Bool) : Flow 48 16 :=
  renameFlow cellRegs (cellParams p) (lines (cellOps slot padding) (cell_ne_nil slot padding))

private def idleCell : Flow 48 16 := straight (.constant 3 1) [.binary .add 7 4 3]

/-- Register 7 contains the successor on every normal return. -/
def block (p : Parameters) (slot : Fin 4) (padding : Bool) : Flow 48 16 :=
  .seq (setup p) (.ifLt 8 9 (activeCell p slot padding) idleCell)

/-- The allocated-field worker table for either copying or padding-checking the selected packed
bit slot. -/
def table (p : Parameters) (slot : Fin 4) (padding : Bool) :=
  (block p slot padding).template (some 7)

variable {w : ℕ}

/-- The field-relative cursor obtained by subtracting the phase's first cursor. -/
def position (p : Parameters) (pub : Fin 16 → Word w) (state : Word w) :=
  state - pub p.firstCursor

/-- The cursor lies within the occupied prefix specified by the live count word. -/
def Active (p : Parameters) (pub : Fin 16 → Word w) (state : Word w) (m : Memory w) :=
  position p pub state < m (pub p.countAddress).val

/-- The selected slot bit read from the packed source word at the current field-relative
position. -/
def bitAt (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w) (state : Word w) (m : Memory w) :=
  (m (m (pub p.srcOffsetAddress).val + position p pub state).val).val.testBit slot.val

/-- The address to which an occupied payload bit is copied. -/
def destination (p : Parameters) (pub : Fin 16 → Word w) (state : Word w) :=
  pub p.destinationBase + position p pub state

private def loaded (p : Parameters) (pub : Fin 16 → Word w) (state : Word w)
    (rs : Regs w 48) (m : Memory w) : Regs w 48 :=
  let a := Function.update rs 4 state
  let b := Function.update a 6 (pub p.firstCursor)
  let c := Function.update b 8 (position p pub state)
  let d := Function.update c 6 (pub p.countAddress)
  Function.update d 9 (m (pub p.countAddress).val)

private def setupEvents (p : Parameters) (pub : Fin 16 → Word w) (m : Memory w) : List (Event w) :=
  [.tick, .tick, .tick, .tick, .read (pub p.countAddress) (m (pub p.countAddress).val)]

private theorem setup_trace (p : Parameters) (pub : Fin 16 → Word w) (state : Word w)
    (rs : Regs w 48) (m : Memory w) :
    trace pub state (setupOps p) rs m = some (setupEvents p pub m, loaded p pub state rs m, m) := rfl

/-- The complete event log, including the count read, witnesses the effect on
memory and the cost of the successful call. -/
abbrev Returns (p : Parameters) (slot : Fin 4) (padding : Bool) (pub : Fin 16 → Word w)
    (state : Word w) (rs : Regs w 48) (m final : Memory w) (steps probes : ℕ) : Prop :=
  ∃ es out, Flow.Exec pub state (block p slot padding) rs m es out final ∧ out 7 = state+1 ∧
    after m es = final ∧ es.length = steps ∧ countProbes es = probes ∧ choiceBits es = []

private theorem active_returns (p : Parameters) (slot : Fin 4) (padding : Bool) (pub : Fin 16 → Word w)
    (state : Word w) (rs : Regs w 48) (m final : Memory w) (ha : Active p pub state m)
    {es : List (Event w)} {small : Regs w 12} {n q : ℕ}
    (run : trace (pub ∘ cellParams p) state (cellOps slot padding)
      (loaded p pub state rs m ∘ cellRegs) m = some (es,small,final))
    (next : small 7 = state+1) (hlen : es.length = n) (hpr : countProbes es = q)
    (hbits : choiceBits es = []) :
    Returns p slot padding pub state rs m final (6+n) (1+q) := by
  let r := loaded p pub state rs m
  have hs := Admin.exec_lines_iff_trace (by simp [setupOps]) |>.mpr (setup_trace p pub state rs m)
  obtain ⟨out, h, he, _⟩ := liftExec cellRegs (cellParams p) pub
    ((Admin.exec_lines_iff_trace (cell_ne_nil slot padding)).mpr run) r rfl
  have hh : r 8 < r 9 := ha
  refine ⟨setupEvents p pub m ++ .tick :: es, out, hs.seq (.ifLtYes hh h),
    (congrFun he 7).trans next, ?_, ?_, ?_, hbits⟩
  · change after m es = final
    exact trace_after run
  · change es.length + 6 = 6+n
    omega
  · change 1 + countProbes es = _
    rw [hpr]

/-- An active payload call copies the selected bit and advances the cursor.
The four probes are count, offset, packed word, and destination. -/
theorem copy_exec (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w)
    (state : Word w) (rs : Regs w 48) (m : Memory w) (ha : Active p pub state m) :
    Returns p slot false pub state rs m
      (writeMemory m (destination p pub state) (encodeBit w (bitAt p slot pub state m))) 21 4 := by
  obtain ⟨_, _, h, hn, hl, hp, hb⟩ := copyFieldCell_trace hw slot (pub ∘ cellParams p) state
    (loaded p pub state rs m ∘ cellRegs) m
  exact active_returns p slot false pub state rs m _ ha h hn hl hp hb

/-- Occupied zero padding passes the guard and leaves memory unchanged. -/
theorem padding_exec (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w)
    (state : Word w) (rs : Regs w 48) (m : Memory w) (ha : Active p pub state m)
    (hz : bitAt p slot pub state m = false) : Returns p slot true pub state rs m m 20 3 := by
  have h := checkPaddingCell_trace hw slot (pub ∘ cellParams p) state
    (loaded p pub state rs m ∘ cellRegs) m
  have hbit : (m (sourceSite (pub ∘ cellParams p) state m).val).val.testBit slot.val = false := hz
  simp only [hbit, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨_, _, h, hn, hl, hp, hb⟩ := h
  exact active_returns p slot true pub state rs m m ha h hn hl hp hb

/-- At every unoccupied position the count is the only external read. -/
theorem idle_exec (p : Parameters) (slot : Fin 4) (padding : Bool) (pub : Fin 16 → Word w)
    (state : Word w) (rs : Regs w 48) (m : Memory w) (ha : ¬ Active p pub state m) :
    Returns p slot padding pub state rs m m 8 1 := by
  let r := loaded p pub state rs m
  let u := Function.update r (3 : Fin 48) (1 : Word w)
  let out := Function.update u (7 : Fin 48) (state+1)
  have hs := Admin.exec_lines_iff_trace (by simp [setupOps]) |>.mpr (setup_trace p pub state rs m)
  have hi : Flow.Exec pub state idleCell r m [.tick,.tick] out m := (Flow.Exec.line rfl).seq (.line rfl)
  have hh : ¬r 8 < r 9 := ha
  exact ⟨_,out,hs.seq (.ifLtNo hh hi), rfl, rfl, rfl, rfl, rfl⟩

/-- No successful derivation can bypass a failing guard on an occupied
padding position, whatever the initial register file. -/
theorem padding_rejects (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w)
    (state : Word w) (rs : Regs w 48) (m : Memory w) (ha : Active p pub state m)
    (hn : bitAt p slot pub state m = true) {es out final} :
    ¬ Flow.Exec pub state (block p slot true) rs m es out final := by
  intro h
  cases h with
  | seq first branch =>
    have h₁ := (Admin.exec_lines_iff_trace (by simp [setupOps])).mp first
    rw [setup_trace] at h₁
    obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h₁
    cases branch with
    | ifLtNo hbad _ => exact hbad ha
    | ifLtYes _ body =>
      have ht := (Admin.exec_lines_iff_trace (cell_ne_nil slot true)).mp
        (restrictExec cellRegs (cellParams p) pub _ body).1
      have hfail := checkPaddingCell_trace hw slot (pub ∘ cellParams p) state
        (loaded p pub state rs m ∘ cellRegs) m
      have hbit : (m (sourceSite (pub ∘ cellParams p) state m).val).val.testBit slot.val = true := hn
      simp only [hbit, ↓reduceIte] at hfail
      change trace _ _ (checkPaddingCell slot) _ _ = some _ at ht
      rw [hfail] at ht
      contradiction

/-- Every successful execution, on any initial register file and memory,
consists entirely of deterministic instructions. -/
theorem exec_choices {p : Parameters} {slot : Fin 4} {padding : Bool} {pub : Fin 16 → Word w}
    {state : Word w} {rs m es out final} (run : Flow.Exec pub state (block p slot padding)
      rs m es out final) : choiceBits es = [] := by
  cases run with
  | seq pre branch =>
    rw [Flow.choiceBits_append, Admin.trace_choiceBits ((Admin.exec_lines_iff_trace
      (by simp [setupOps])).mp pre), List.nil_append]
    cases branch with
    | ifLtYes _ body =>
      simp only [choiceBits]
      exact Admin.trace_choiceBits ((Admin.exec_lines_iff_trace (cell_ne_nil slot padding)).mp
        (restrictExec cellRegs (cellParams p) pub _ body).1)
    | ifLtNo _ body =>
      simp only [choiceBits]
      exact Admin.trace_choiceBits ((Admin.exec_lines_iff_trace
        (ops := [Op.constant (r := 48) (k := 16) 3 1, .binary .add 7 4 3]) (by decide)).mp body)

/-- A successful block has the same effect in the native fixed table when
the allotted fuel includes its return instruction. -/
theorem native_of_returns {p : Parameters} {slot : Fin 4} {padding : Bool} {pub : Fin 16 → Word w}
    {state : Word w} {m final : Memory w} {steps probes fuel : ℕ}
    (h : Returns p slot padding pub state (fun _ => 0) m final steps probes) (hf : steps < fuel) :
    let P := ((table p slot padding).instantiate w pub).program
    ∃ es, execute P fuel (P.start state) m [] = some ⟨es, some (state+1)⟩ ∧
      after m es = final ∧ es.length = steps ∧ countProbes es = probes ∧ choiceBits es = [] := by
  obtain ⟨es,out,run,hnext,hmem,hlen,hprobes,hbits⟩ := h
  refine ⟨es, ?_, hmem, hlen, hprobes, hbits⟩
  apply (Flow.template_execute_iff (block p slot padding) (some 7) pub state
    (fun _ => 0) (fun _ => 0) m fuel [] _).mpr
  exact ⟨out,final,run,congrArg some hnext.symm,hlen.trans_lt hf,hbits⟩

/-- An arbitrary successful native report realizes the very same cursor,
memory effect and cost. This also accounts for surplus choice tapes and
arbitrary proposed fuel bounds. -/
theorem native_report_of_returns {p : Parameters} {slot : Fin 4} {padding : Bool}
    {pub : Fin 16 → Word w} {state : Word w} {m final : Memory w} {steps probes fuel : ℕ}
    {bits : List Bool} {report : Report w}
    (h : Returns p slot padding pub state (fun _ => 0) m final steps probes)
    (hr : let P := ((table p slot padding).instantiate w pub).program
      execute P fuel (P.start state) m bits = some report) :
    bits = [] ∧ report.result = some (state+1) ∧ after m report.events = final ∧
      report.events.length = steps ∧ countProbes report.events = probes := by
  let P := ((table p slot padding).instantiate w pub).program
  have iffRun := Flow.template_execute_iff (block p slot padding) (some 7) pub state
    (fun _ => 0) (fun _ => 0) m
  obtain ⟨r,m',run,hnext,hlen,hbits⟩ := (iffRun fuel bits report).mp hr
  have hno := exec_choices run
  obtain rfl : bits = [] := hbits.symm.trans hno
  let budget := fuel + steps + 1
  have hmore : execute P budget (P.start state) m [] = some report :=
    (iffRun budget [] report).mpr ⟨r,m',run,hnext,by dsimp [budget]; omega,hno⟩
  obtain ⟨es,he,hm,hl,hp,_⟩ := native_of_returns h (show steps < budget by dsimp [budget]; omega)
  obtain rfl : report = ⟨es,some (state+1)⟩ := Option.some.inj (hmore.symm.trans he)
  exact ⟨rfl,rfl,hm,hl,hp⟩

/-- Failing active padding rejects the native call for every choice tape and
fuel bound. -/
theorem padding_native_rejects (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (pub : Fin 16 → Word w)
    (state : Word w) (m : Memory w) (ha : Active p pub state m) (hn : bitAt p slot pub state m = true)
    (fuel : ℕ) (bits : List Bool) :
    let P := ((table p slot true).instantiate w pub).program
    execute P fuel (P.start state) m bits = none := by
  let P := ((table p slot true).instantiate w pub).program
  change execute P fuel (P.start state) m bits = none
  cases h : execute P fuel (P.start state) m bits with
  | none => rfl
  | some out =>
    obtain ⟨r,m',hr,_⟩ := (Flow.template_execute_iff (block p slot true) (some 7) pub state
      (fun _ => 0) (fun _ => 0) m fuel bits out).mp h
    exact (padding_rejects hw p slot pub state _ m ha hn hr).elim

/-- Every successful allocated cell, including an idle padding check, is
deterministic and advances the persistent cursor. -/
theorem report_successor (hw : 4 ≤ w) (p : Parameters) (slot : Fin 4) (padding : Bool)
    (pub : Fin 16 → Word w) (state : Word w) (m : Memory w) (bits : List Bool) (fuel : ℕ) {rep : Report w}
    (hr : let P := ((table p slot padding).instantiate w pub).program
      execute P fuel (P.start state) m bits = some rep) :
    bits = [] ∧ rep.result = some (state+1) := by
  have use {padding : Bool} {m' : Memory w} {n q : ℕ}
      (ret : Returns p slot padding pub state (fun _ => 0) m m' n q)
      (call : let P := ((table p slot padding).instantiate w pub).program
        execute P fuel (P.start state) m bits = some rep) : bits = [] ∧ rep.result = some (state+1) := by
    have hp := native_report_of_returns ret call
    exact ⟨hp.1,hp.2.1⟩
  by_cases ha : Active p pub state m
  · cases padding
    · exact use (copy_exec hw p slot pub state _ m ha) hr
    · cases hz : bitAt p slot pub state m with
      | false => exact use (padding_exec hw p slot pub state _ m ha hz) hr
      | true =>
        have hf := padding_native_rejects hw p slot pub state m ha hz fuel bits
        have impossible : (none : Option (Report w)) = some rep := hf.symm.trans hr
        contradiction
  · exact use (idle_exec p slot padding pub state _ m ha) hr

private def readOnly {r k : ℕ} : Op r k → Bool
  | .write .. => false
  | _ => true

private theorem trace_readOnly {r k : ℕ} {pub : Fin k → Word w} {state : Word w} {ops : List (Op r k)}
    {rs out : Regs w r} {m final : Memory w} {es : List (Event w)}
    (ht : trace pub state ops rs m = some (es,out,final)) (hs : ops.all readOnly = true)
    (replay : Memory w) : after replay es = replay := by
  induction ops generalizing rs m es with
  | nil => simp [trace] at ht; rw [ht.1]; rfl
  | cons op rest ih =>
    obtain ⟨hhead,htail⟩ := Bool.and_eq_true_iff.mp hs
    cases he : op.effect pub state rs m with
    | none => simp [trace,he] at ht
    | some u =>
      obtain ⟨e,rs',m'⟩ := u
      have hupdate : update replay e = replay := by
        cases op <;> simp only [readOnly,Op.effect,Option.some.injEq,Prod.mk.injEq] at he hhead
        all_goals first | contradiction | (rw [← he.1]; rfl) | (split at he <;> simp at he; rw [← he.1]; rfl)
      cases hr : trace pub state rest rs' m' with
      | none => simp [trace,he,hr] at ht
      | some u =>
        obtain ⟨es',out',final'⟩ := u
        simp [trace,he,hr] at ht
        obtain ⟨hh,rfl,rfl⟩ := ht
        rw [← hh]
        change after (update replay e) es' = replay
        rw [hupdate]
        exact ih hr htail

private theorem active_frame {p : Parameters} {slot : Fin 4} {padding : Bool} {pub : Fin 16 → Word w}
    {state : Word w} {rs : Regs w 48} {m final : Memory w} {es out}
    (he : Flow.Exec pub state (activeCell p slot padding) rs m es out final) (addr : Word w)
    (safe : padding = true ∨ addr ≠ destination p pub state) (replay : Memory w) :
    after replay es addr.val = replay addr.val := by
  have ht := (Admin.exec_lines_iff_trace (cell_ne_nil slot padding)).mp
    (restrictExec cellRegs (cellParams p) pub _ he).1
  cases padding with
  | false =>
    have hn := safe.resolve_left (by decide)
    have hnv : addr.val ≠ (destination p pub state).val := fun eq => hn (Fin.ext eq)
    simp (config := { decide := true }) [cellOps, copyFieldCell,locateCell,fetch,trace,Op.effect,
      Function.update] at ht
    rw [← ht.1]
    change writeMemory replay (destination p pub state) _ addr.val = replay addr.val
    exact ite_eq_right hnv
  | true =>
    rw [trace_readOnly ht (by rfl) replay]

/-- A report preserves the reserved tag under replay on every memory.
Only an active copy has a write, and it targets the current destination. -/
theorem report_frame (p : Parameters) (slot : Fin 4) (padding : Bool) (pub : Fin 16 → Word w)
    (state : Word w) (m : Memory w) (bits : List Bool) (fuel : ℕ) {rep : Report w}
    (hr : let P := ((table p slot padding).instantiate w pub).program
      execute P fuel (P.start state) m bits = some rep) (addr : Word w)
    (safe : Active p pub state m → padding = true ∨ addr ≠ destination p pub state)
    (replay : Memory w) : after replay rep.events addr.val = replay addr.val := by
  obtain ⟨out,final,he,_⟩ := (Flow.template_execute_iff (block p slot padding) (some 7) pub state
    (fun _ => 0) (fun _ => 0) m fuel bits rep).mp hr
  generalize hs : rep.events = es at he ⊢
  cases he with
  | seq pre branch =>
    have hpre := (Admin.exec_lines_iff_trace (by simp [setupOps])).mp pre
    rw [setup_trace] at hpre
    obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj hpre
    cases branch with
    | ifLtYes ht body =>
      change after replay _ addr.val = replay addr.val
      exact active_frame body addr (safe ht) replay
    | ifLtNo _ body =>
      have hb := (Admin.exec_lines_iff_trace
        (ops := [Op.constant (r := 48) (k := 16) 3 1, .binary .add 7 4 3]) (by decide)).mp body
      simp [trace,Op.effect] at hb
      rw [← hb.1]
      rfl

end LiveHeader.Allocated

end VPVNP
end Computability
end OAI
