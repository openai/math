import OAI.Computability.VPVNP.PrimedCounterCall
import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete
import OAI.Computability.VPVNP.PrimedStackRAMNodeTable

/-!
# Straight-line executions of scheduled calls

A straight-line trace gives the exact events, registers and memory of the corresponding
structured body. Its instructions consume no choice bits. The scheduled call rejects any
surplus bits when it compares the next cursor with the total and halts or returns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Admin

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM

variable {w r k : ℕ} {pub : Fin k → Word w} {state : Word w}
  {rs out : Regs w r} {m m' : Memory w} {es : List (Event w)}

private theorem trace_cons_iff {op : Op r k} {ops : List (Op r k)} :
    trace pub state (op :: ops) rs m = some (es, out, m') ↔
      ∃ e r₁ m₁ fs, op.effect pub state rs m = some (e, r₁, m₁) ∧
        trace pub state ops r₁ m₁ = some (fs, out, m') ∧ es = e :: fs := by
  constructor
  · intro ht
    cases he : op.effect pub state rs m with
    | none => simp [trace, he] at ht
    | some a =>
      obtain ⟨e, r₁, m₁⟩ := a
      cases hf : trace pub state ops r₁ m₁ with
      | none => simp [trace, he, hf] at ht
      | some a =>
        obtain ⟨fs, r₂, m₂⟩ := a
        obtain ⟨rfl, rfl, rfl⟩ := by simpa [trace, he, hf] using ht
        exact ⟨e, r₁, m₁, fs, rfl, hf, rfl⟩
  · rintro ⟨e, r₁, m₁, fs, he, hf, rfl⟩
    simp [trace, he, hf]

private theorem exec_straight_iff_trace (op : Op r k) (ops : List (Op r k)) :
    Flow.Exec pub state (straight op ops) rs m es out m' ↔
      trace pub state (op :: ops) rs m = some (es, out, m') := by
  induction ops generalizing op rs m es with
  | nil =>
    constructor
    · intro h
      cases h with
      | line he => simp [trace, he]
    · intro ht
      obtain ⟨e, r₁, m₁, fs, he, hf, rfl⟩ := trace_cons_iff.mp ht
      obtain ⟨rfl, rfl, rfl⟩ := by simpa [trace] using hf
      exact .line he
  | cons next rest ih =>
    constructor
    · intro h
      cases h with
      | seq first last =>
        cases first with
        | line he => exact trace_cons_iff.mpr ⟨_, _, _, _, he, (ih next).mp last, rfl⟩
    · intro ht
      obtain ⟨e, r₁, m₁, fs, he, hf, rfl⟩ := trace_cons_iff.mp ht
      exact Flow.Exec.seq (.line he) ((ih next).mpr hf)

/-- Compiling a nonempty list of lines preserves and reflects its entire trace. -/
theorem exec_lines_iff_trace {ops : List (Op r k)} (hn : ops ≠ []) :
    Flow.Exec pub state (lines ops hn) rs m es out m' ↔
      trace pub state ops rs m = some (es, out, m') := by
  cases ops with
  | nil => contradiction
  | cons op ops => exact exec_straight_iff_trace op ops

/-- A successful straight-line trace contains only ticks, reads and writes. -/
theorem trace_choiceBits {ops : List (Op r k)}
    (ht : trace pub state ops rs m = some (es, out, m')) : choiceBits es = [] := by
  induction ops generalizing rs m es with
  | nil =>
    have h : [] = es ∧ rs = out ∧ m = m' := by simpa [trace] using ht
    rw [← h.1]
    rfl
  | cons op ops ih =>
    obtain ⟨e, r₁, m₁, fs, he, hf, rfl⟩ := trace_cons_iff.mp ht
    change choiceBits ([e] ++ fs) = []
    rw [Flow.choiceBits_append, Flow.line_choices he, ih hf, List.nil_append]

/-- A call whose body consumes no choices rejects every nonempty tape, for every fuel. -/
theorem call_reject_nonempty {a : Flow r k} (next total : Fin r) (priv : Word w → Word w)
    (det : ∀ {es out m'}, Flow.Exec pub state a rs m es out m' → choiceBits es = [])
    (fuel : ℕ) {bits : List Bool} (hne : bits ≠ []) :
    let M := (Call.template a next total).instantiate w pub
    execute M.program fuel ⟨M.entry, state, rs, priv⟩ m bits = none := by
  let M := (Call.template a next total).instantiate w pub
  change execute M.program fuel ⟨M.entry, state, rs, priv⟩ m bits = none
  cases hr : execute M.program fuel ⟨M.entry, state, rs, priv⟩ m bits with
  | none => rfl
  | some t =>
    obtain ⟨es, out, m', left, bs, tail, he, _, hbits, htail, _⟩ :=
      (Call.linked a next total pub).complete (Call.reject_code a next total pub) state priv rs m fuel bits t hr
    rw [det he, List.nil_append] at hbits
    subst bs
    cases left with
    | zero => contradiction
    | succ f =>
      cases f with
      | zero =>
        have hs : M.code (Call.stop a) = .jumpEq next total (Call.accept a) (Call.back a) := by
          simp [M, Template.instantiate, Call.template, Call.stop, Instr.resize]
        change execute M.program 1 ⟨Call.stop a, state, out, priv⟩ m' bits = some tail at htail
        simp [execute, Machine.program, hs, Instr.run] at htail
      | succ f =>
        rw [Call.execute_stop] at htail
        cases bits <;> simp_all

/-- A scheduled straight-line body rejects every nonempty choice tape. -/
theorem lines_call_reject_nonempty {ops : List (Op r k)} (hn : ops ≠ []) (next total : Fin r)
    (priv : Word w → Word w) (fuel : ℕ) {bits : List Bool} (hne : bits ≠ []) :
    let M := (Call.template (lines ops hn) next total).instantiate w pub
    execute M.program fuel ⟨M.entry, state, rs, priv⟩ m bits = none :=
  call_reject_nonempty next total priv (fun he => trace_choiceBits ((exec_lines_iff_trace hn).mp he)) fuel hne

end PrimedCounter.Admin

end VPVNP
end Computability
end OAI
