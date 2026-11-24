import OAI.Computability.VPVNP.RAMPrivateLogRun

/-!
# Single-pass metered private call execution

The instruction interpreter uses the write log for private memory, reads a
private cell and its work count in the same scan, and threads the report and
operation count through the same call recursion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.PrivateRAM

open VPVNP.BurstRAM

variable {w p r k : ℕ} {C : Type*}

/-- Charge the actual lookup in a log implementation, stopping at the first
matching write. Only a store extends the log. -/
def Instr.actualLogWork (i : Instr w p r k) (l : LogConfig w p r) : ℕ :=
  match i with
  | .loadPrivate _ addr _ => (WriteLog.scan l.writes (l.reg addr)).2
  | .storePrivate .. => 3
  | _ => 0

/-- The private load uses the value and cost of the same linear scan. -/
def Instr.meteredAction (i : Instr w p r k) (pub : Fin k → Word w) (l : LogConfig w p r) :
    CallAction w (LogConfig w p r) × ℕ :=
  match i with
  | .loadPrivate dst addr next =>
    let t := WriteLog.scan l.writes (l.reg addr)
    (.localStep {l with pc := next, reg := Function.update l.reg dst t.1}, i.wordWork + t.2)
  | .storePrivate .. => (i.runLogged pub l, i.wordWork + 3)
  | _ => (i.runLogged pub l, i.wordWork)

theorem Instr.meteredAction_spec (i : Instr w p r k) (pub : Fin k → Word w) (l : LogConfig w p r) :
    i.meteredAction pub l = (i.runLogged pub l, i.wordWork + i.actualLogWork l) := by
  cases i <;> rfl

/-- The frame gives the charged result of a stopping instruction or the one
continuation invocation and the event to prepend on return. -/
inductive CallFrame (w : ℕ) (C : Type*)
  | stop (out : LocalCallRun w)
  | next (event : Event w) (config : C) (allowance : ℕ) (bits : List Bool)

/-- Resolve one instruction action using the remaining probe allowance and choice stream.
Produce either a stopping result or an event with its residual call state. -/
def CallFrame.ofAction : CallAction w C → ℕ → List Bool → CallFrame w C
  | .finish s, _, bits => .stop (.stop (some (⟨[], s⟩, bits)) 0 0)
  | .reject, _, _ => .stop (.stop none 0 0)
  | .localStep c, a, bits => .next .tick c a bits
  | .branch _, _, [] => .stop (.stop none 0 1)
  | .branch c, a, b :: bits => .next (.choice b) (c b) a bits
  | .read .., 0, _ | .write .., 0, _ => .stop (.stop none 0 0)
  | .read addr c, a + 1, bits =>
    match takeWord w bits with
    | none => .stop (.stop none 1 w)
    | some (v, tail) => .next (.read addr v) (c v) a tail
  | .write addr v c, a + 1, bits => .next (.write addr v) c a bits

/-- Evaluate a call frame, prepending its event to the recursive run when the frame continues. -/
def CallFrame.result (recur : C → ℕ → List Bool → LocalCallRun w) : CallFrame w C → LocalCallRun w
  | .stop t => t
  | .next e c a bs => (recur c a bs).prepend e

theorem CallFrame.result_eq (P : Program w C) (f : ℕ) (c : C) (a : ℕ) (bits : List Bool) :
    (ofAction (P.step c) a bits).result (runLocalCall P f) = runLocalCall P (f+1) c a bits := by
  cases hs : P.step c with
  | finish | reject | localStep => simp [runLocalCall, hs, ofAction, result]
  | branch => cases bits <;> simp [runLocalCall, hs, ofAction, result]
  | write => cases a <;> simp [runLocalCall, hs, ofAction, result]
  | read =>
    cases a with
    | zero => simp [runLocalCall, hs, ofAction, result]
    | succ a =>
      cases h : takeWord w bits with
      | none => simp [runLocalCall, hs, ofAction, result, h]
      | some pair =>
        obtain ⟨v, rest⟩ := pair
        simp [runLocalCall, hs, ofAction, result, h]

/-- The interpreter controls reserve eight word operations per dispatch,
five stores per occupied probe, and four operations per guess bit. -/
def LocalCharge (t : LocalCallRun w) : ℕ := 8*t.instructions + 5*t.probes + 4*t.guessWork

/-- Interpreter work charged to one continuing event, with eight operations for dispatch, five
per probe and four per requested guess bit. -/
def EventCharge (e : Event w) : ℕ := 8 + 5*e.probeCharge + 4*e.guessWidth

theorem localCharge_prepend (e : Event w) (t : LocalCallRun w) :
    LocalCharge (t.prepend e) = EventCharge e + LocalCharge t := by
  simp only [LocalCharge, EventCharge, LocalCallRun.prepend, Nat.mul_add, Nat.mul_one]
  omega

/-- Run a bounded private call using its write log and return both the local execution and its
work, charging each actual log scan in that execution. -/
def Machine.meteredLoggedCall (M : Machine w p r k) :
    ℕ → LogConfig w p r → ℕ → List Bool → LocalCallRun w × ℕ
  | 0, _, _, _ => (⟨none, 0, 0, 0⟩, 0)
  | f+1, l, a, bits =>
    let step := (M.code l.pc).meteredAction M.publicData l
    match CallFrame.ofAction step.1 a bits with
    | .stop t => (t, step.2 + LocalCharge t)
    | .next e c a' bs =>
      let tail := M.meteredLoggedCall f c a' bs
      (tail.1.prepend e, step.2 + EventCharge e + tail.2)

theorem Machine.meteredLoggedCall_logResult (M : Machine w p r k) (fuel : ℕ) (l : LogConfig w p r)
    (a : ℕ) (bits : List Bool) :
    (M.meteredLoggedCall fuel l a bits).1 = runLocalCall M.logProgram fuel l a bits := by
  induction fuel generalizing l a bits with
  | zero => rfl
  | succ f ih =>
    rw [Machine.meteredLoggedCall, Instr.meteredAction_spec, ← CallFrame.result_eq]
    change ((match CallFrame.ofAction (M.logProgram.step l) a bits with
      | .stop t => (t, _)
      | .next e c a' bs => ((M.meteredLoggedCall f c a' bs).1.prepend e, _))
        : LocalCallRun w × ℕ).1 = _
    cases h : CallFrame.ofAction (M.logProgram.step l) a bits with
    | stop t => rfl
    | next e c a' bs => simp [CallFrame.result, ih]

theorem Machine.meteredLoggedCall_result (M : Machine w p r k) (fuel : ℕ) (l : LogConfig w p r)
    (a : ℕ) (bits : List Bool) :
    (M.meteredLoggedCall fuel l a bits).1 = runLocalCall M.program fuel l.denote a bits :=
  (M.meteredLoggedCall_logResult ..).trans (M.runLocalCall_logProgram ..)

end BurstRAM.PrivateRAM

end VPVNP
end Computability
end OAI
