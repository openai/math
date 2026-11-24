import OAI.Computability.VPVNP.QueryProgram
import OAI.Computability.VPVNP.QueryTape
import OAI.Computability.VPVNP.TableCompiler
import Mathlib.Data.Fintype.Prod

/-!
# Read a query bit on the literal machine's tape

A control records the remaining number of queries, the query-program state, and a phase.
Phase zero scans right until the blank immediately after the input. A query for suffix bit
`i` then moves left by `k - i` cells. Phase one reads the selected symbol and starts the next
query. The input and work tapes are preserved throughout the simulation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace QueryMachine

open UniversalMachine TableCompiler QueryTape

/-- Control state recording the remaining query budget, the query-program state, and the
tape-scan phase. -/
abbrev Control (t k : ℕ) (Q : Type*) := Fin (t + 1) × Q × Fin (k + 1)

/-- Decrease a bounded counter by one, saturating at zero. -/
def predFin {n : ℕ} (a : Fin (n + 1)) : Fin (n + 1) := ⟨a.val - 1, by omega⟩

/-- Distance from the blank after the payload to bit `i` of its `k`-bit suffix. -/
def offset {k : ℕ} (i : Fin k) : Fin (k + 1) := ⟨k - i.val, by omega⟩

variable {k : ℕ} {Q : Type*} (p : QueryProgram k Q) (t : ℕ)

/-- Start at the query program's initial state with all `t` queries available and scan phase
zero. -/
def start : Control t k Q := (Fin.last t, p.start, 0)

/-- Take one tape-control step toward the requested bit, branch on its value when reached, or
halt with the query result. -/
def command (c : Control t k Q) (a : Symbol) : Step (Control t k Q) :=
  let (r, q, phase) := c
  match p.step q with
  | .halt b => .halt b
  | .read i low high =>
    if r.val = 0 then .halt false else
    if phase.val = 0 then
      if a = 0 then .move (r, q, offset i) 1 else .move (r, q, 0) 2
    else if phase.val = 1 then .move (predFin r, if a = 2 then high else low, 0) 0
    else .move (r, q, predFin phase) 1

variable [Fintype Q]

/-- Compile the bounded binary query controller into the universal machine's instruction table. -/
noncomputable def machine : Program := compile (start p t) (command p t)

/-- Count accepting paths with the specified tick budget, control state, input-head position,
and initially blank work tape. -/
noncomputable def countAt (input : Word) (pos : ℕ) (c : Control t k Q) (ticks : ℕ) : ℕ :=
  paths (machine p t) ticks
    (running (start p t) c (atPosition input pos) (Turing.Tape.mk₁ []))

theorem countAt_step (input : Word) (pos : ℕ) (c : Control t k Q) (ticks : ℕ) :
    countAt p t input pos c (ticks + 1) =
      match command p t c (atPosition input pos).head with
      | .halt b => if b then 1 else 0
      | .move next dir => paths (machine p t) ticks
          (running (start p t) next (moveTape (atPosition input pos) dir) (Turing.Tape.mk₁ [])) :=
  by
    have h := paths_running_succ (start p t) (command p t) c (atPosition input pos) (Turing.Tape.mk₁ []) ticks
    cases hc : command p t c (atPosition input pos).head <;> simp only [hc] at h <;> exact h

end QueryMachine

end VPVNP
end Computability
end OAI
