import OAI.Computability.VPVNP.QueryProgram
import Mathlib.Data.Fintype.Card

/-!
# Compiling a CNF test into a finite query program

The payload assigns one bit to each Boolean variable. Each occurrence of a literal
becomes one read state. A matching literal skips the rest of its clause, and an
exhausted clause goes directly to the rejecting halt.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessCNF

/-- The bit must equal the indicated polarity for this literal to hold. -/
abbrev Literal (k : ℕ) := Fin k × Bool

/-- A list of clauses over `k` Boolean variables. Each clause is a disjunction of signed
literals. -/
abbrev CNF (k : ℕ) := List (List (Literal k))

/-- Number of literal occurrences, counting repetitions within or across clauses. -/
def literalCount {k : ℕ} (φ : CNF k) : ℕ := (φ.map List.length).sum

/-- An assignment satisfies the formula when every clause contains a literal whose required bit
matches the assignment. -/
def Satisfies {k : ℕ} (φ : CNF k) (x : Fin k → Bool) : Prop :=
  ∀ clause ∈ φ, ∃ l ∈ clause, x l.1 = l.2

variable {k n : ℕ}

/-- The compiler reserves two halting states, then adds one state per literal. -/
def stateCount : CNF k → ℕ
  | [] => 2
  | clause :: φ => stateCount φ + clause.length

/-- The query evaluator has one control state per literal occurrence, in addition to its two
terminal states. -/
abbrev State (φ : CNF k) := Fin (stateCount φ)

theorem card_state (φ : CNF k) : Fintype.card (State φ) = 2 + literalCount φ := by
  rw [Fintype.card_fin]
  induction φ with
  | nil => rfl
  | cons c φ ih => simp [stateCount, literalCount] at ih ⊢; omega

/-- During assembly of a clause, the first matching literal jumps to `pass`
(the start of the remaining clauses), and exhaustion jumps to `reject`. -/
private structure Block (k n : ℕ) extends QueryProgram k (Fin n) where
  pass : Fin n
  reject : Fin n

private def liftStep : QueryStep k (Fin n) → QueryStep k (Fin (n + 1))
  | .halt b => .halt b
  | .read i lo hi => .read i lo.succ hi.succ

private def push (l : Literal k) (b : Block k n) : Block k (n + 1) where
  start := 0
  pass := b.pass.succ
  reject := b.reject.succ
  step := Fin.cases
    (.read l.1 (if l.2 then b.start.succ else b.pass.succ)
      (if l.2 then b.pass.succ else b.start.succ))
    (fun q => liftStep (b.step q))

/-- Existing states keep their behavior when a new literal is prepended. -/
private theorem eval_push_succ (l : Literal k) (b : Block k n) (x : Fin k → Bool)
    (f : ℕ) (q : Fin n) :
    (push l b).eval x f q.succ = b.eval x f q := by
  induction f generalizing q with
  | zero => cases h : b.step q <;> simp [QueryProgram.eval, push, h, liftStep]
  | succ f ih =>
    cases h : b.step q with
    | halt v => simp [QueryProgram.eval, push, h, liftStep]
    | read i lo hi =>
      cases hv : x i <;> simpa [QueryProgram.eval, push, h, liftStep, hv] using
        ih (if x i then hi else lo)

private def compileClause (b : Block k n) : (c : List (Literal k)) → Block k (n + c.length)
  | [] => { b with start := b.reject, pass := b.start }
  | l :: c => push l (compileClause b c)

private def compile : (φ : CNF k) → Block k (stateCount φ)
  | [] => (⟨⟨1, fun q => .halt (q == 1)⟩, 1, 0⟩ : Block k 2)
  | c :: φ => compileClause (compile φ) c

/-- A query program deciding whether the payload satisfies a CNF. -/
def query (φ : CNF k) : QueryProgram k (State φ) := (compile φ).toQueryProgram

private structure Correct (b : Block k n) (x : Fin k → Bool) (budget : ℕ)
    (pass start : Bool) : Prop where
  reject_ok : ∀ f, budget ≤ f → b.eval x f b.reject = false
  pass_ok : ∀ f, budget ≤ f → b.eval x f b.pass = pass
  start_ok : ∀ f, budget ≤ f → b.eval x f b.start = start

private theorem correct_push {b : Block k n} {x : Fin k → Bool} {budget : ℕ}
    {pass start : Bool} (h : Correct b x budget pass start) (l : Literal k) :
    Correct (push l b) x (budget + 1) pass (if x l.1 = l.2 then pass else start) := by
  constructor
  · intro f hf
    exact (eval_push_succ l b x f b.reject).trans (h.reject_ok f (by omega))
  · intro f hf
    exact (eval_push_succ l b x f b.pass).trans (h.pass_ok f (by omega))
  · intro f hf
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    change (push l b).eval x (f + 1) 0 = _
    rw [QueryProgram.eval]
    have hp := (eval_push_succ l b x f b.pass).trans (h.pass_ok f (by omega))
    have hs := (eval_push_succ l b x f b.start).trans (h.start_ok f (by omega))
    cases h₁ : x l.1 <;> cases h₂ : l.2 <;> simp [push, h₁, h₂] at hp hs ⊢ <;> assumption

private def clauseValue (x : Fin k → Bool) (c : List (Literal k)) : Bool :=
  c.any (fun l => x l.1 == l.2)

private theorem eval_step_congr {Q : Type*} (p p' : QueryProgram k Q)
    (h : p.step = p'.step) (x : Fin k → Bool) (f : ℕ) (q : Q) :
    p.eval x f q = p'.eval x f q := by
  induction f generalizing q with
  | zero => simp only [QueryProgram.eval, h]
  | succ f ih =>
    simp only [QueryProgram.eval, h]
    cases p'.step q with
    | halt v => rfl
    | read i lo hi => exact ih _

private theorem correct_clause {b : Block k n} {x : Fin k → Bool} {budget : ℕ}
    {oldPass next : Bool} (h : Correct b x budget oldPass next) (c : List (Literal k)) :
    Correct (compileClause b c) x (budget + c.length) next (clauseValue x c && next) := by
  induction c with
  | nil =>
    have he (f : ℕ) (q : Fin n) :=
      eval_step_congr (compileClause b []).toQueryProgram b.toQueryProgram rfl x f q
    exact ⟨fun f hf => (he f b.reject).trans (h.reject_ok f hf),
      fun f hf => (he f b.start).trans (h.start_ok f hf),
      fun f hf => (he f b.reject).trans (h.reject_ok f hf)⟩
  | cons l c ih =>
    have h' := correct_push ih l
    change Correct (push l (compileClause b c)) x (budget + c.length + 1) next _
    convert h' using 1
    cases hb : x l.1 <;> cases hl : l.2 <;> simp [clauseValue, hb, hl]

private theorem correct_compile (φ : CNF k) (x : Fin k → Bool) :
    ∃ pass, Correct (compile φ) x (literalCount φ) pass (φ.all (clauseValue x)) := by
  induction φ with
  | nil =>
    refine ⟨true, ?_⟩
    constructor <;> intro f _ <;> cases f <;> rfl
  | cons c φ ih =>
    obtain ⟨pass, h⟩ := ih
    refine ⟨φ.all (clauseValue x), ?_⟩
    have hc := correct_clause h c
    simpa [compile, stateCount, literalCount, Nat.add_comm] using hc

/-- At most one query per literal is sufficient, including for formulas with
empty clauses and the empty conjunction. -/
theorem query_eval_iff (φ : CNF k) (x : Fin k → Bool) {fuel : ℕ}
    (hf : literalCount φ ≤ fuel) :
    (query φ).eval x fuel (query φ).start = true ↔ Satisfies φ x := by
  obtain ⟨_, h⟩ := correct_compile φ x
  rw [show (query φ).eval x fuel (query φ).start = φ.all (clauseValue x) from h.start_ok _ hf]
  simp [List.all_eq_true, clauseValue, Satisfies]

end HardnessCNF

end VPVNP
end Computability
end OAI
