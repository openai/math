import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Pow

/-!
# The clocked signed multitape machine

The signed witness uses a fixed encoding of finite programs. The semantics here give each
program a read-only input tape and a specified number of work tapes. A branch instruction
requests one fresh bit. Both continuations count, even when they have identical configurations.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedMachine

inductive Symbol where
  | blank | zero | one
  deriving DecidableEq, BEq, Repr

inductive Direction where
  | left | stay | right
  deriving DecidableEq, BEq, Repr

inductive Output where
  | zero | pos | neg
  deriving DecidableEq, BEq, Repr

/-- Integer returned by a valid halt. -/
def Output.value : Output → ℤ
  | .zero => 0
  | .pos => 1
  | .neg => -1

/-- A simultaneous tape operation. Each work head writes a symbol before moving. -/
structure Transition where
  state : ℕ
  inputMove : Direction
  workMoves : List (Symbol × Direction)
  deriving DecidableEq, BEq, Repr

inductive Action where
  | halt (out : Output)
  | step (a : Transition)
  | branch (a b : Transition)
  deriving DecidableEq, BEq, Repr

/-- The input and work symbols are tested at the current head positions. -/
structure Rule where
  state : ℕ
  inputSymbol : Symbol
  workSymbols : List Symbol
  action : Action
  deriving DecidableEq, BEq, Repr

structure Program where
  workTapes : ℕ
  table : List Rule
  deriving DecidableEq, BEq, Repr

/-- A two-sided tape, with the nearest cell first on either side of the head.
Missing list entries are blank. -/
structure Tape where
  left : List Symbol
  head : Symbol
  right : List Symbol
  deriving Repr

def Tape.blank : Tape := ⟨[], .blank, []⟩

def Tape.move (t : Tape) : Direction → Tape
  | .left => ⟨t.left.tail, t.left.headD .blank, t.head :: t.right⟩
  | .stay => t
  | .right => ⟨t.head :: t.left, t.right.headD .blank, t.right.tail⟩

def Tape.writeMove (t : Tape) (sd : Symbol × Direction) : Tape :=
  ({t with head := sd.1} : Tape).move sd.2

structure Config where
  state : ℕ
  inputTape : Tape
  work : List Tape
  deriving Repr

/-- Start in state zero with the head on the first bit of the whole input, including the
program prefix. All work tapes start blank. -/
def Program.initial (p : Program) (input : List Bool) : Config :=
  let bits := input.map (fun b ↦ if b then Symbol.one else Symbol.zero)
  ⟨0, ⟨[], bits.headD .blank, bits.tail⟩, List.replicate p.workTapes Tape.blank⟩

def Config.advance (cfg : Config) (t : Transition) : Option Config :=
  if t.workMoves.length = cfg.work.length then
    some ⟨t.state, cfg.inputTape.move t.inputMove, cfg.work.zipWith Tape.writeMove t.workMoves⟩
  else none

/-- The four possible outcomes of interpreting one instruction. -/
inductive Outcome (C : Type*) where
  | fail
  | halt (out : Output)
  | step (cfg : C)
  | branch (a b : C)

def Program.next (p : Program) (cfg : Config) : Outcome Config :=
  let workSymbols := cfg.work.map Tape.head
  let rule := p.table.find? (fun r ↦
    r.state == cfg.state && r.inputSymbol == cfg.inputTape.head &&
    r.workSymbols == workSymbols)
  match rule.map Rule.action with
  | none => .fail
  | some (.halt out) => .halt out
  | some (.step t) =>
    match cfg.advance t with
    | some cfg' => .step cfg'
    | none => .fail
  | some (.branch a b) =>
    match cfg.advance a, cfg.advance b with
    | some ca, some cb => .branch ca cb
    | _, _ => .fail

/-- Sum the values of the paths which halt within the remaining clock budget. -/
def run {C : Type*} (next : C → Outcome C) : ℕ → C → ℤ
  | 0, _ => 0
  | n + 1, c =>
    match next c with
    | .fail => 0
    | .halt out => out.value
    | .step c' => run next n c'
    | .branch a b => run next n a + run next n b

theorem abs_run_le {C : Type*} (next : C → Outcome C) (fuel : ℕ) (c : C) :
    |run next fuel c| ≤ (2 : ℤ) ^ fuel := by
  induction fuel generalizing c with
  | zero => simp [run]
  | succ n ih =>
    have h₁ : (1 : ℤ) ≤ 2 ^ n := one_le_pow₀ (by decide)
    have h₂ : (2 : ℤ) ^ n ≤ 2 ^ (n + 1) := by
      rw [pow_succ, mul_two]
      omega
    cases h : next c with
    | fail => simp [run, h]
    | halt out =>
      have hout : |out.value| ≤ 1 := by cases out <;> decide
      simpa [run, h] using hout.trans (h₁.trans h₂)
    | step c' => simpa [run, h] using (ih c').trans h₂
    | branch a b =>
      simpa only [run, h, pow_succ, mul_two] using
        (abs_add_le (run next n a) (run next n b)).trans (add_le_add (ih a) (ih b))

def pathSum (p : Program) (input : List Bool) (fuel : ℕ) : ℤ :=
  run p.next fuel (p.initial input)

theorem abs_pathSum_le (p : Program) (input : List Bool) (fuel : ℕ) :
    |pathSum p input fuel| ≤ (2 : ℤ) ^ fuel :=
  abs_run_le _ _ _

/-- The number of cells represented by the two lists and the current head. -/
def Tape.cells (t : Tape) : ℕ := t.left.length + 1 + t.right.length

private theorem Tape.cells_move_le (t : Tape) (d : Direction) :
    (t.move d).cells ≤ t.cells + 1 := by
  cases d <;> simp [Tape.move, Tape.cells] <;> omega

private theorem Tape.cells_writeMove_le (t : Tape) (sd : Symbol × Direction) :
    (t.writeMove sd).cells ≤ t.cells + 1 :=
  Tape.cells_move_le {t with head := sd.1} _

/-- The next configurations on all live branches of an instruction. -/
def Outcome.successors {C : Type*} : Outcome C → List C
  | .fail | .halt _ => []
  | .step c => [c]
  | .branch a b => [a, b]

private theorem advance_of_successor {p : Program} {cfg cfg' : Config}
    (h : cfg' ∈ (p.next cfg).successors) : ∃ t, cfg.advance t = some cfg' := by
  unfold Program.next at h
  dsimp only at h
  split at h
  · simp [Outcome.successors] at h
  · simp [Outcome.successors] at h
  · split at h
    · simp [Outcome.successors] at h
      subst cfg'
      exact ⟨_, by assumption⟩
    · simp [Outcome.successors] at h
  · split at h
    · simp [Outcome.successors] at h
      rcases h with rfl | rfl <;> exact ⟨_, by assumption⟩
    · simp [Outcome.successors] at h

/-- Reachability after exactly `elapsed` live transitions along some branch. -/
inductive Program.Reachable (p : Program) (input : List Bool) : ℕ → Config → Prop
  | initial : p.Reachable input 0 (p.initial input)
  | step {n c c'} : p.Reachable input n c → c' ∈ (p.next c).successors →
      p.Reachable input (n + 1) c'

/-- Every reachable work tape contains at most one newly visited cell per elapsed step,
and the same bound applies to the input tape beyond its initial window. -/
theorem Program.Reachable.tape_bounds {p : Program} {input : List Bool} {elapsed : ℕ} {c : Config}
    (h : p.Reachable input elapsed c) :
    c.work.length = p.workTapes ∧ c.inputTape.cells ≤ max 1 input.length + elapsed ∧
      ∀ tape ∈ c.work, tape.cells ≤ 1 + elapsed := by
  induction h with
  | initial =>
    simp only [Program.initial, Tape.cells, List.length_replicate, List.length_nil, Nat.zero_add,
      List.length_tail, List.length_map, Nat.add_zero, true_and]
    constructor
    · omega
    · intro tape ht
      rw [(List.mem_replicate.mp ht).2]
      rfl
  | @step n c c' _ hs ih =>
    obtain ⟨tr, htr⟩ := advance_of_successor hs
    unfold Config.advance at htr
    split at htr
    next hlen =>
      cases htr
      refine ⟨by simpa only [List.length_zipWith, hlen, min_self] using ih.1, ?_, ?_⟩
      · exact (Tape.cells_move_le ..).trans (Nat.succ_le_succ ih.2.1)
      · intro tape ht
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
        rw [List.getElem_zipWith]
        exact (Tape.cells_writeMove_le ..).trans (Nat.succ_le_succ
          (ih.2.2 _ (List.getElem_mem _)))
    next => contradiction

/-- Total number of explicitly stored input and work cells. -/
def Config.cells (c : Config) : ℕ := c.inputTape.cells + (c.work.map Tape.cells).sum

private theorem sum_cells_le (w : List Tape) (k : ℕ) (h : ∀ t ∈ w, t.cells ≤ k) :
    (w.map Tape.cells).sum ≤ w.length * k := by
  induction w with
  | nil => simp
  | cons t w ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    exact (Nat.add_le_add (h _ (by simp)) (ih (fun t ht ↦ h _ (by simp [ht])))).trans_eq
      (Nat.add_comm ..)

/-- The number of represented cells along any branch is linear in the clock for a fixed
program, with its dependence on both program arity and input length explicit. -/
theorem Program.Reachable.cells_le {p : Program} {input : List Bool} {elapsed : ℕ} {c : Config}
    (h : p.Reachable input elapsed c) :
    c.cells ≤ max 1 input.length + elapsed + p.workTapes * (1 + elapsed) := by
  obtain ⟨hk, hin, hw⟩ := h.tape_bounds
  simpa only [Config.cells, ← hk] using Nat.add_le_add hin (sum_cells_le _ _ hw)

end SignedMachine

end SpectralBooks
end LinearAlgebra
end OAI
