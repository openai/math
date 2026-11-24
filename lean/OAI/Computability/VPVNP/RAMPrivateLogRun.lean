import OAI.Computability.VPVNP.RAMPrivateLog
import OAI.Computability.VPVNP.RAMLocalRun

/-!
# Call simulation and log capacity

The list-backed machine produces the direct machine's exact report, unused
suffix, and all three counters even on rejecting inputs. Along every possible
prefix, including arbitrary read guesses, the log grows by at most one entry
per instruction. Hence the same fixed scan allowance applies on every path.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C D : Type*}

/-- Mapping every instruction continuation preserves the whole metered call. -/
theorem runLocalCall_mapState (P : Program w C) (Q : Program w D) (f : C → D)
    (hs : ∀ c, (P.step c).mapState f = Q.step (f c)) (fuel : ℕ)
    (c : C) (allowance : ℕ) (bits : List Bool) :
    runLocalCall P fuel c allowance bits = runLocalCall Q fuel (f c) allowance bits := by
  induction fuel generalizing c allowance bits with
  | zero => rfl
  | succ n ih =>
    rw [runLocalCall, runLocalCall, ← hs]
    cases P.step c with
    | localStep | finish | reject => simp [CallAction.mapState, ih]
    | branch next => cases bits <;> simp [CallAction.mapState, ih]
    | read a next =>
      cases allowance with
      | zero => rfl
      | succ p => cases takeWord w bits <;> simp [CallAction.mapState, ih]
    | write a v next => cases allowance <;> simp [CallAction.mapState, ih]

/-- All continuations of a dispatched instruction, before enforcing fuel,
probe caps, or correctness of the supplied read value. -/
def CallAction.continuesTo (action : CallAction w C) (c : C) : Prop :=
  match action with
  | .localStep next | .write _ _ next => c = next
  | .branch next => ∃ b, c = next b
  | .read _ next => ∃ v, c = next v
  | .finish _ | .reject => False

/-- A prefix of `n` continuing instructions, retaining every binary choice
and possible read answer. Halting and rejection have no continuations. -/
inductive InstructionPrefix (P : Program w C) (start : C) : ℕ → C → Prop
  | initial : InstructionPrefix P start 0 start
  | step {n c next} (tail : InstructionPrefix P start n c) (hc : (P.step c).continuesTo next) :
      InstructionPrefix P start (n + 1) next

namespace PrivateRAM

variable {p r k : ℕ}

theorem Machine.runLocalCall_logProgram (M : Machine w p r k) (fuel : ℕ)
    (l : LogConfig w p r) (allowance : ℕ) (bits : List Bool) :
    runLocalCall M.logProgram fuel l allowance bits =
      runLocalCall M.program fuel l.denote allowance bits :=
  runLocalCall_mapState M.logProgram M.program LogConfig.denote M.logProgram_step fuel l allowance bits

theorem Instr.runLogged_writes {i : Instr w p r k} {pub : Fin k → Word w}
    {l next : LogConfig w p r} (hc : (i.runLogged pub l).continuesTo next) :
    next.writes = i.nextLog l := by
  unfold Instr.runLogged at hc
  cases h : i.run pub l.denote <;> rw [h] at hc
  case localStep | write => cases hc; rfl
  case branch | read => obtain ⟨_, rfl⟩ := hc; rfl
  case finish | reject => exact hc.elim

theorem Machine.prefix_log_length_le (M : Machine w p r k) {start l : LogConfig w p r}
    {n : ℕ} (h : InstructionPrefix M.logProgram start n l) :
    l.writes.length ≤ start.writes.length + n := by
  induction h with
  | initial => simp
  | step h hc ih =>
    rw [Instr.runLogged_writes hc]
    exact ((M.code _).nextLog_length_le _).trans (by omega)

/-- With `n` dispatches used out of the initial fuel, the reached log and
the remaining fuel still fit in the reserved capacity. -/
theorem Machine.prefix_log_capacity (M : Machine w p r k) {start l : LogConfig w p r}
    {n fuel capacity : ℕ} (h : InstructionPrefix M.logProgram start n l)
    (hn : n ≤ fuel) (hcap : start.writes.length + fuel ≤ capacity) :
    l.writes.length + (fuel - n) ≤ capacity := by
  have := M.prefix_log_length_le h
  omega

/-- This bound covers each private read, regardless of the supplied address
and the persistent input. The capacity depends only on the call fuel. -/
theorem Machine.prefix_scan_work_le (M : Machine w p r k) (s a : Word w)
    {l : LogConfig w p r} {n fuel : ℕ}
    (h : InstructionPrefix M.logProgram (M.logProgram.start s) n l) (hn : n ≤ fuel) :
    (WriteLog.scan l.writes a).2 ≤ 4 * (fuel + 1) := by
  have hlen := M.prefix_log_length_le h
  change l.writes.length ≤ 0 + n at hlen
  exact (WriteLog.scan_work_le _ _).trans (Nat.mul_le_mul_left 4 (by omega))

end PrivateRAM
end BurstRAM

end VPVNP
end Computability
end OAI
