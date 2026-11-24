import OAI.Computability.VPVNP.RAMProcessorLocalScan

/-!
# Exact native result at the external-action boundary

A successful private scan returns a callback and the residual state, fuel and
guess suffix. The caller's permitted probe consumes its charge before looking
at a read value. Resuming this way and prepending the scan's private events
gives exactly the native local report, also on over-cap or truncated streams.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.LocalProcessor

open BurstRAM PrivateRAM

variable {w p r k : ℕ}

/-- Optional call report together with the unconsumed suffix of the site's nominated bit
stream. -/
abbrev Output (w : ℕ) := Option (Report w × List Bool)

/-- Prepend one event to a successful report while retaining its unused bit suffix and
propagating failure. -/
def addEvent (e : Event w) (out : Output w) : Output w :=
  out.map fun ⟨r, bs⟩ => (r.prepend e, bs)

/-- Prepend a chronological event prefix to a successful local output, preserving its residual
bits. -/
def addEvents : List (Event w) → Output w → Output w
  | [], out => out
  | e :: es, out => addEvent e (addEvents es out)

/-- Resume exactly one pending external or terminal action. -/
def resume (P : Program w (LogConfig w p r)) (allowance : ℕ) (y : Yield w p r) : Output w :=
  match y.exit.action y.cfg with
  | .finish s => some (⟨[], s⟩, y.bits)
  | .read a next =>
    match allowance with
    | 0 => none
    | left+1 =>
      (takeWord w y.bits).bind fun ⟨v, tail⟩ =>
        addEvent (.read a v) (runLocalCall P y.fuel (next v) left tail).output
  | .write a v c =>
    match allowance with
    | 0 => none
    | left+1 => addEvent (.write a v) (runLocalCall P y.fuel c left y.bits).output
  | _ => none

/-- Resume a yielded local call under the remaining probe allowance and attach the private
events recorded before its callback. -/
def result (P : Program w (LogConfig w p r)) (allowance : ℕ) (y : Yield w p r) : Output w :=
  addEvents y.prefixEvents (resume P allowance y)

private theorem result_prepend (P : Program w (LogConfig w p r)) (a : ℕ)
    (e : Event w) (y : Yield w p r) :
    result P a (y.prepend e) = addEvent e (result P a y) := rfl

/-- The caller can consume the generated word and communicate a record at
each callback without losing or multiplying any native successful report. -/
theorem scan_result (T : Template p r k) (pub : Fin k → Word w) (f : ℕ)
    (c : LogConfig w p r) (bs : List Bool) (a : ℕ) :
    let P := (T.instantiate w pub).logProgram
    result P a (scan T pub f c bs) = (runLocalCall P f c a bs).output := by
  let P := (T.instantiate w pub).logProgram
  change result P a _ = (runLocalCall P f c a bs).output
  induction f generalizing c bs with
  | zero => rfl
  | succ f ih =>
    have hstep : P.step c = (instructionExit T c).action (instructionPost T pub c) :=
      (ISA.callback_action (T.code c.pc) pub c).symm
    rw [runLocalCall, hstep, scan]
    cases instructionExit T c with
    | next j => rw [result_prepend, ih]; rfl
    | choose yes no =>
      cases bs with
      | nil => rfl
      | cons b bs => rw [result_prepend, ih]; rfl
    | read dst addr j =>
      cases a with
      | zero => rfl
      | succ a =>
        cases hs : takeWord w bs with
        | none => simp [result, resume, ISA.Callback.action, hs, LocalCallRun.stop, addEvents]
        | some pair =>
          obtain ⟨v, tail⟩ := pair
          simp [result, resume, ISA.Callback.action, hs, LocalCallRun.prepend, addEvents, addEvent]
    | write addr src j => cases a <;> rfl
    | returnState _ | accept | reject => rfl

end RAMTape.LocalProcessor

end VPVNP
end Computability
end OAI
