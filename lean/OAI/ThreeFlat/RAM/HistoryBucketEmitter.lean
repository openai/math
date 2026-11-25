import OAI.ThreeFlat.RAM.FetchWords
import OAI.ThreeFlat.RAM.DeterministicBlock

namespace OAI
/-! # Emitting interval offsets for external-pair buckets

A bucket is three consecutive words `[initial-site table offset, first bit, past bit]`.
With a final-group lookup for each initial site, a single native block
emits `[group, first bit, past bit, accumulated group offset]` and increments
the counter for that group. All input and counter reads precede all writes.
-/

namespace ThreeFlat.RAM.HistoryBucketEmitter

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM

variable {w r k : ℕ}

/-- Register zero points at the next three input words. Registers one and two
are the group lookup and prefix-counter array bases. A four-word group table stores
`4 * site` in the first input field. Register three points to
the next output row. -/
def ops (R : Fin 12 ↪ Fin r) : List (Op r k) :=
  [.constant (R 4) 1, .read (R 6) (R 0), .binary .add (R 6) (R 1) (R 6),
   .read (R 6) (R 6), .binary .add (R 0) (R 0) (R 4), .read (R 7) (R 0),
   .binary .add (R 0) (R 0) (R 4), .read (R 8) (R 0), .binary .add (R 0) (R 0) (R 4),
   .binary .add (R 9) (R 2) (R 6), .read (R 10) (R 9), .binary .sub (R 11) (R 8) (R 7),
   .binary .add (R 11) (R 10) (R 11), .write (R 9) (R 11),
   .write (R 3) (R 6), .binary .add (R 3) (R 3) (R 4),
   .write (R 3) (R 7), .binary .add (R 3) (R 3) (R 4),
   .write (R 3) (R 8), .binary .add (R 3) (R 3) (R 4),
   .write (R 3) (R 10), .binary .add (R 3) (R 3) (R 4)]

@[simp] theorem ops_length (R : Fin 12 ↪ Fin r) : (ops (k := k) R).length = 22 := rfl

def afterRow (m : Memory w) (src groups counters dest : Word w) : Memory w :=
  let group := m (groups+m src.val).val
  let lo := m (src+1).val
  let hi := m (src+1+1).val
  let offset := m (counters+group).val
  let a := writeMemory m (counters+group) (offset+(hi-lo))
  let b := writeMemory a dest group
  let c := writeMemory b (dest+1) lo
  let d := writeMemory c (dest+1+1) hi
  writeMemory d (dest+1+1+1) offset

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Complete deterministic semantics of all 22 native word operations. -/
theorem trace_row (R : Fin 12 ↪ Fin r) (pub : Fin k → Word w) (state : Word w)
    (reg : Regs w r) (m : Memory w) :
    ∃ es out, trace pub state (ops R) reg m = some (es,out,
      afterRow m (reg (R 0)) (reg (R 1)) (reg (R 2)) (reg (R 3))) ∧ es.length = 22 ∧
      out (R 0) = reg (R 0)+1+1+1 ∧ out (R 1) = reg (R 1) ∧ out (R 2) = reg (R 2) ∧
      out (R 3) = reg (R 3)+1+1+1+1 ∧ out (R 5) = reg (R 5) := by
  simp [ops,trace,Op.effect,BinaryOp.eval,afterRow,Function.update,R.injective.eq_iff]; exact ⟨rfl,rfl,rfl⟩

/-- Lift an existing checked straight-line instruction block into the deterministic
prefix semantics used by the weighted scanner. -/
private theorem line {p : ℕ} {M : Machine w p r k} {start next bad : Fin p} (op : Op r k)
    (rom : M.code start = (op.emit next bad).resize w) (state : Word w) (reg out : Regs w r)
    (priv : Word w → Word w) (m m' : Memory w) (e : Event w)
    (h : op.effect M.publicData state reg m = some (e,out,m')) :
    advance M.program 1 ⟨start,state,reg,priv⟩ m = some (⟨next,state,out,priv⟩,m') := by
  cases op <;> simp only [Op.effect] at h <;> (try split at h) <;>
    simp only [Option.some.injEq,Prod.mk.injEq,reduceCtorEq] at h
  all_goals first | contradiction | obtain ⟨rfl,rfl,rfl⟩ := h
  all_goals simp_all [Op.emit,Instr.resize,advance,Machine.program,Instr.run,Config.put]

theorem advance_trace {p : ℕ} {M : Machine w p r k} {start stop bad : Fin p} {xs : List (Op r k)}
    (linked : Contains M bad start xs stop) (state : Word w) (reg out : Regs w r)
    (priv : Word w → Word w) (m m' : Memory w) (es : List (Event w))
    (tr : trace M.publicData state xs reg m = some (es,out,m')) :
    advance M.program xs.length ⟨start,state,reg,priv⟩ m = some (⟨stop,state,out,priv⟩,m') := by
  induction linked generalizing reg m es with
  | nil =>
    simp only [trace,Option.some.injEq,Prod.mk.injEq] at tr
    obtain ⟨rfl,rfl,rfl⟩ := tr
    rfl
  | @cons first next stop op xs hd rest ih =>
    cases act : op.effect M.publicData state reg m with
    | none => simp [trace,act] at tr
    | some a =>
      obtain ⟨ev,mid,mem⟩ := a
      cases tail : trace M.publicData state xs mid mem with
      | none => simp [trace,act,tail] at tr
      | some y =>
        obtain ⟨vs,rs,z⟩ := y
        simp [trace,act,tail] at tr
        obtain ⟨rfl,rfl,rfl⟩ := tr
        simpa only [List.length_cons,Nat.add_comm 1] using
          advance_trans (line op hd state reg mid priv m mem ev act) (ih mid mem vs tail)

/-- Native scalar deterministic prefix for all four emitted fields and one
prefix-counter update. Register 5 is available for the outer loop limit. -/
theorem advance_row {p : ℕ} (R : Fin 12 ↪ Fin r) {M : Machine w p r k} {start stop bad : Fin p}
    (linked : Contains M bad start (ops R) stop) (state : Word w) (reg : Regs w r)
    (priv : Word w → Word w) (m : Memory w) :
    ∃ out, advance M.program 22 ⟨start,state,reg,priv⟩ m = some (⟨stop,state,out,priv⟩,
      afterRow m (reg (R 0)) (reg (R 1)) (reg (R 2)) (reg (R 3))) ∧
      out (R 0) = reg (R 0)+1+1+1 ∧ out (R 1) = reg (R 1) ∧ out (R 2) = reg (R 2) ∧
      out (R 3) = reg (R 3)+1+1+1+1 ∧ out (R 5) = reg (R 5) := by
  obtain ⟨es,out,tr,_,rs⟩ := trace_row R M.publicData state reg m
  exact ⟨out, advance_trace linked state reg out priv m _ es tr,rs⟩

end ThreeFlat.RAM.HistoryBucketEmitter

end OAI
