import OAI.Computability.VPVNP.QueryTape
import OAI.Computability.VPVNP.TableCompiler
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# Read-only control for an exact-one incidence matrix

Each column on the input tape carries a tag, its selection bit, and one incidence bit per
row. The control checks one row on each pass from the right end of the tape. A three-valued
counter distinguishes zero, one, and at least two selected columns incident with the row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace IncidenceMachine

open UniversalMachine TableCompiler QueryTape

/-- One incidence column, consisting of a selection bit and an incidence bit for each of the
`m` rows. -/
abbrev Column (m : ℕ) := Bool × (Fin m → Bool)

/-- Bits of one column in the order read by the leftward scan. -/
def columnBits {m : ℕ} (c : Column m) : Word := true :: c.1 :: List.ofFn c.2

/-- Control states for searching for a row and reading each column's tag, selection bit, and
incidence bits, with a count saturated at two. -/
inductive State (m : ℕ) where
  | search (row : Fin (m + 1))
  | tag (row : Fin m) (seen : Fin 3)
  | flag (row : Fin m) (seen : Fin 3)
  | bit (row colRow : Fin m) (selected : Bool) (seen : Fin 3)
  deriving DecidableEq, Fintype

/-- Begin the incidence check by searching for row zero. -/
def start (m : ℕ) : State m := .search 0

/-- Saturating count of selected incidences. -/
def tally (n : ℕ) : Fin 3 := ⟨min n 2, by omega⟩

theorem tally_succ (n : ℕ) : tally ((tally n).val + 1) = tally (n + 1) := by
  apply Fin.ext
  dsimp [tally]
  omega

theorem tally_eq_one_iff (n : ℕ) : tally n = 1 ↔ n = 1 := by
  rw [Fin.ext_iff]
  change min n 2 = 1 ↔ n = 1
  omega

/-- Literal instructions, with directions 0 (stay), 1 (left), and 2 (right). -/
def command (m : ℕ) (q : State m) (a : Symbol) : Step (State m) :=
  match q with
  | .search row =>
    if h : row.val < m then
      if a = 0 then .move (.tag ⟨row.val, h⟩ (tally 0)) 1 else .move (.search row) 2
    else .halt true
  | .tag r seen =>
    if a = 2 then .move (.flag r seen) 1
    else if a = 1 ∧ seen = 1 then .move (.search r.succ) 0 else .halt false
  | .flag r seen =>
    .move (.bit r ⟨0, Nat.zero_lt_of_lt r.isLt⟩ (decide (a = 2)) seen) 1
  | .bit r j selected seen =>
    let nextSeen := if j = r ∧ selected = true ∧ a = 2 then tally (seen.val + 1) else seen
    if hj : j.val + 1 < m then .move (.bit r ⟨j.val + 1, hj⟩ selected nextSeen) 1
    else .move (.tag r nextSeen) 1

/-- Compile the read-only exact-one incidence checker for `m` rows into a universal-machine
program. -/
noncomputable def machine (m : ℕ) : Program := compile (start m) (command m)

/-- Number of accepting paths within the fuel bound when the input head is at `pos` and the
checker is in state `q`. -/
noncomputable def countAt (m : ℕ) (input : Word) (pos : ℕ) (q : State m) (fuel : ℕ) : ℕ :=
  paths (machine m) fuel (running (start m) q (atPosition input pos) (Turing.Tape.mk₁ []))

theorem countAt_step (m : ℕ) (input : Word) (pos : ℕ) (q : State m) (fuel : ℕ) :
    countAt m input pos q (fuel + 1) =
      match command m q (atPosition input pos).head with
      | .halt b => if b then 1 else 0
      | .move next dir => paths (machine m) fuel
          (running (start m) next (moveTape (atPosition input pos) dir) (Turing.Tape.mk₁ [])) := by
  have h := paths_running_succ (start m) (command m) q (atPosition input pos) (Turing.Tape.mk₁ []) fuel
  cases hc : command m q (atPosition input pos).head <;> simp only [hc] at h <;> exact h

theorem countAt_left {m : ℕ} {input : Word} {pos : ℕ} {q next : State m} {fuel : ℕ}
    (h : command m q (atPosition input (pos + 1)).head = .move next 1) :
    countAt m input (pos + 1) q (fuel + 1) = countAt m input pos next fuel := by
  rw [countAt_step, h]
  change paths (machine m) fuel (running (start m) next ((atPosition input (pos + 1)).move .left) _) = _
  rw [move_left_atPosition_succ]
  rfl

/-- The head sees these bits in order as it moves left, finishing at position `base`. -/
def ReadsLeft (input : Word) (base : ℕ) (bits : Word) : Prop :=
  ∀ (i : ℕ) (hi : i < bits.length),
    (atPosition input (base + bits.length - i)).head = if bits[i] then 2 else 1

end IncidenceMachine

end VPVNP
end Computability
end OAI
