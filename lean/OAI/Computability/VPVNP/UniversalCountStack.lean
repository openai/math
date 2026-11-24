import OAI.Computability.VPVNP.RAMTapeUnaryWordValue
import OAI.Computability.VPVNP.StructuredStackLink
import Mathlib.Tactic.DeriveFintype

/-!
# Deterministic enumeration of fixed-length Boolean witnesses

Section 8.1 queries an integer coefficient by counting all canonical witnesses.
Two little-endian counters hold the current witness and the number accepted.
The control invokes a verifier, adds its one-bit result to the count, and
increments the witness. Overflow of the witness counter ends the enumeration,
including the case of a zero-bit witness.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalCountStack

open RAMTape TapeWord RAMTape.UnaryWord

/-- The witness and total counters, temporary digit stack, verifier result flag, and auxiliary
ports used by the witness enumerator. -/
inductive Port (K : Type*) where
  | choice | total | scratch | flag | aux (k : K)
  deriving DecidableEq, Fintype

/-- Selects the binary counter holding the current witness or the number of witnesses accepted
so far. -/
inductive Register where
  | choice | total
  deriving DecidableEq

instance : Fintype Register := derive_fintype% _

/-- The stack port storing the selected witness or total counter. -/
def Register.port {K : Type*} : Register → Port K
  | .choice => .choice
  | .total => .total

/-- The local states for invoking the verifier, collecting its result, and propagating a carry
through either counter before restoring its digit order. -/
inductive Control (Q : Type*) where
  | verify (q : Q) | collect
  | scan (r : Register) (carry : Bool)
  | emit (r : Register) (digit carry : Bool)
  | restore (r : Register) (overflow : Bool)
  | put (r : Register) (overflow digit : Bool)
  deriving DecidableEq, Fintype

variable {K Q : Type*}

private def resume (entry : Q) : Register → Bool → Option (Control Q)
  | .total, _ => some (.scan .choice true)
  | .choice, false => some (.verify entry)
  | .choice, true => none

/-- The finite control and ports are independent of the width of either counter. -/
def enumerate (v : Routine (Port K) Q) : Routine (Port K) (Control Q) where
  entry := .verify v.entry
  code
    | .verify q => v.install Control.verify (some .collect) q
    | .collect => .pop .flag (fun b => some (.scan .total (b.getD false)))
    | .scan r c => .pop r.port (fun b => some (b.elim (.restore r c) (fun d => .emit r (d ^^ c) (d && c))))
    | .emit r d c => .push .scratch d (some (.scan r c))
    | .restore r c => .pop .scratch (fun b => b.elim (resume v.entry r c) (fun d => some (.put r c d)))
    | .put r c d => .push r.port d (some (.restore r c))

/-- Call boundary for the verifier. Its private work and its persistent input
are all located at `aux` ports. A normal return places one Boolean in `flag`. -/
def bank (aux : Stacks K) (choice total scratch flag : List Bool) : Stacks (Port K)
  | .choice => choice
  | .total => total
  | .scratch => scratch
  | .flag => flag
  | .aux k => aux k

private def scanBank (r : Register) (aux : Stacks K) (active other scratch : List Bool) :=
  match r with
  | .choice => bank aux active other scratch []
  | .total => bank aux other active scratch []

private theorem scanBank_active (r : Register) (aux : Stacks K) (a o s : List Bool) :
    scanBank r aux a o s r.port = a := by cases r <;> rfl

private theorem scanBank_scratch (r : Register) (aux : Stacks K) (a o s : List Bool) :
    scanBank r aux a o s .scratch = s := by cases r <;> rfl

variable [DecidableEq K]

private theorem active_update (r : Register) (aux : Stacks K) (a o s b : List Bool) :
    Function.update (scanBank r aux a o s) r.port b = scanBank r aux b o s := by
  funext i
  cases r <;> cases i <;> simp [Register.port, scanBank, bank]

private theorem scratch_update (r : Register) (aux : Stacks K) (a o s b : List Bool) :
    Function.update (scanBank r aux a o s) .scratch b = scanBank r aux a o b := by
  funext i
  cases r <;> cases i <;> simp [scanBank, bank]

local macro "counter_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [scanBank_active, scanBank_scratch, active_update, scratch_update,
    List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil, Option.elim_some, Option.elim_none])

variable (v : Routine (Port K) Q) (aux : Stacks K)

private theorem scan_run (r : Register) (carry : Bool) (active other scratch : List Bool) :
    StackRuns (enumerate v).standalone (2 * active.length + 1) (some (.scan r carry))
      (scanBank r aux active other scratch) (some (.restore r (incScan carry active).2))
      (scanBank r aux [] other ((incScan carry active).1.reverse ++ scratch)) := by
  induction active generalizing carry scratch with
  | nil => counter_step; exact .nil ..
  | cons b bs ih =>
    simp only [List.length_cons, Nat.mul_succ, incScan, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    counter_step
    counter_step
    exact ih (b && carry) ((b ^^ carry) :: scratch)

private theorem restore_run (r : Register) (carry : Bool) (active other scratch : List Bool) :
    StackRuns (enumerate v).standalone (2 * scratch.length + 1) (some (.restore r carry))
      (scanBank r aux active other scratch) (resume v.entry r carry)
      (scanBank r aux (scratch.reverse ++ active) other []) := by
  induction scratch generalizing active with
  | nil => counter_step; exact .nil ..
  | cons b bs ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    counter_step
    counter_step
    exact ih (b :: active)

private theorem increment_run (r : Register) (carry : Bool) (active other : List Bool) :
    StackRuns (enumerate v).standalone (4 * active.length + 2) (some (.scan r carry))
      (scanBank r aux active other []) (resume v.entry r (incScan carry active).2)
      (scanBank r aux (incScan carry active).1 other []) := by
  have h := (scan_run v aux r carry active other []).trans
    (restore_run v aux r (incScan carry active).2 [] other ((incScan carry active).1.reverse ++ []))
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse, incScan_length] at h
  convert h using 1
  omega

/-- The next call starts with the incremented counters. On the last witness
the normal return has exactly the same layout, with the witness reset to zero. -/
theorem iteration_run {v : Routine (Port K) Q} {aux : Stacks K} {work : ℕ}
    {choice total : List Bool} {ok : Bool}
    (hv : v.Runs work (bank aux choice total [] []) (bank aux choice total [] [ok])) :
    StackRuns (enumerate v).standalone (work + 4 * total.length + 4 * choice.length + 5)
      (some (enumerate v).entry) (bank aux choice total [] [])
      (if (incScan true choice).2 then none else some (enumerate v).entry)
      (bank aux (incScan true choice).1 (incScan ok total).1 [] []) := by
  have verified := hv.link (enumerate v) Control.verify (some .collect) (fun _ => rfl)
  have hf : Function.update (bank aux choice total [] [ok]) .flag [] = bank aux choice total [] [] := by
    funext i
    cases i <;> simp [bank]
  have pop : StackRuns (enumerate v).standalone 1 (some .collect) (bank aux choice total [] [ok])
      (some (.scan .total ok)) (bank aux choice total [] []) := by
    refine .cons (.pop rfl) ?_
    simp only [bank, List.head?_cons, List.tail_cons, hf, Option.getD_some]
    exact .nil ..
  have add := increment_run v aux .total ok total choice
  have next := increment_run v aux .choice true choice (incScan ok total).1
  have h := ((verified.trans pop).trans add).trans next
  have he : resume v.entry .choice (incScan true choice).2 =
      (if (incScan true choice).2 then none else some (enumerate v).entry) := by
    cases (incScan true choice).2 <;> rfl
  rw [he] at h
  convert h using 1 <;> first | rfl | omega

end UniversalCountStack

end VPVNP
end Computability
end OAI
