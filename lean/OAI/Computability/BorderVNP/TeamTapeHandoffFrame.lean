import OAI.Computability.VPVNP.RAMWordBits
import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Tactic.DeriveFintype

/-!
# Canonical successor messages in the team computation

A live processor transmits its program counter, register file and cumulative
tick count. An accepting halt clears the instruction fields and retains the
time. No private path sign is present in the message. A physical comparison
accepts exactly the binary encoding of the locally determined outgoing frame.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeHandoff

open VPVNP.RAMTape VPVNP.BurstRAM

/-- Canonical live and halted forms of the successor link. -/
inductive Frame (w k : ℕ) where
  | live (pc : Word w) (registers : Fin k → Word w) (ticks : Word w)
  | accepted (ticks : Word w)

variable {w k : ℕ}

/-- The elapsed logical ticks are visible in either form. -/
def Frame.elapsed : Frame w k → Word w
  | .live _ _ t | .accepted t => t

/-- Unique accepted-halt representation at this logical time. -/
def Frame.halt (f : Frame w k) : Frame w k := .accepted f.elapsed

/-- The status bit is true exactly for the propagated accepted halt. -/
def Frame.halted : Frame w k → Bool
  | .live .. => false
  | .accepted _ => true

/-- Fixed-width payload in the order program counter, registers, cumulative ticks.
At a halt the program counter and registers are zero and the cumulative clock is retained. -/
def Frame.words : Frame w k → List (Word w)
  | .live pc regs tick => pc :: List.ofFn regs ++ [tick]
  | .accepted tick => (0 : Word w) :: List.replicate k 0 ++ [tick]

/-- The actual shared binary link payload, least-significant bit first within a word. -/
def Frame.bits (f : Frame w k) : List Bool := f.halted :: f.words.flatMap wordBits

private theorem wordData_length (xs : List (Word w)) : (xs.flatMap wordBits).length = xs.length*w := by
  induction xs with
  | nil => simp
  | cons x xs ih => rw [List.flatMap_cons, List.length_append, length_wordBits, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- Each predecessor/successor link has exactly one tag bit and `k+2` complete words. -/
theorem Frame.bits_length (f : Frame w k) : f.bits.length = 1+(k+2)*w := by
  rw [Frame.bits, List.length_cons, wordData_length]
  cases f <;> simp only [Frame.words, List.length_cons, List.length_append, List.length_ofFn, List.length_nil, List.length_replicate] <;> ring

private theorem eq_of_flatMap_words {xs ys : List (Word w)} (hlen : xs.length = ys.length)
    (h : xs.flatMap wordBits = ys.flatMap wordBits) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hlen.symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have he := List.append_inj h (show (wordBits x).length = (wordBits y).length by simp)
      rw [(List.ofFn_injective.comp (VPVNP.RAMSerialization.wordBits w).injective) he.1,
        ih (Nat.succ.inj hlen) he.2]

/-- Two checked ends of a physical link agree in status, PC, every register and time.
This includes zero-width words and an empty register file. -/
theorem Frame.bits_injective : Function.Injective (@Frame.bits w k) := by
  intro f g he
  have ht := (List.cons.inj he).1
  have hw := eq_of_flatMap_words (show f.words.length = g.words.length by cases f <;> cases g <;> simp [Frame.words])
    (List.cons.inj he).2
  cases f with
  | accepted t =>
    cases g with
    | live => contradiction
    | accepted u => simpa [Frame.words] using hw
  | live pc regs t =>
    cases g with
    | accepted => contradiction
    | live pc' regs' u =>
      have ⟨hp, he'⟩ := List.cons.inj hw
      have eqs := List.append_inj he' (by simp)
      obtain rfl := hp
      obtain rfl : regs = regs' := List.ofFn_injective eqs.1
      obtain rfl : t = u := List.cons.inj eqs.2 |>.1
      rfl

/-- The unique startup frame. No predecessor is needed at processor zero. -/
def initial (pc : Word w) (regs : Fin k → Word w) : Frame w k := .live pc regs 0

/-- Scan a locally prescribed outgoing frame and the guessed shared bits. Both
streams must end together and all compared bit positions must agree. -/
inductive CompareState where
  | left (agree : Bool) | right (bit : Option Bool) (agree : Bool) | done (agree : Bool)
  deriving Fintype

private def afterPair (eq : Bool) : Option Bool → Option Bool → CompareState
  | none, b => .done (eq && b.isNone)
  | some _, none => .done false
  | some a, some b => .left (eq && (a == b))

/-- The left stream is on the false port and the physical link stream on the true port. -/
def compareCode : StackCode Bool CompareState
  | .left eq => .pop false (fun b => .right b eq)
  | .right bit eq => .pop true (afterPair eq bit)
  | .done eq => .halt eq

/-- The two physical bit stacks compared by the outgoing validator. -/
def streams (xs ys : List Bool) : Stacks Bool := fun b => if b then ys else xs

private theorem update_left (xs ys us : List Bool) :
    Function.update (streams xs ys) false us = streams us ys := by
  funext b; cases b <;> simp [streams]

private theorem update_right (xs ys vs : List Bool) :
    Function.update (streams xs ys) true vs = streams xs vs := by
  funext b; cases b <;> simp [streams]

private theorem pair_run (xs ys : List Bool) (eq : Bool) :
    StackRuns compareCode 2 (.left eq) (streams xs ys) (afterPair eq xs.head? ys.head?) (streams xs.tail ys.tail) := by
  refine .cons (.pop (k := false) (f := fun b => .right b eq) rfl) ?_
  change StackRuns compareCode 1 (.right xs.head? eq) (Function.update (streams xs ys) false xs.tail) _ _
  rw [update_left]
  refine .cons (.pop (k := true) (f := afterPair eq xs.head?) rfl) ?_
  change StackRuns compareCode 0 _ (Function.update (streams xs.tail ys) true ys.tail) _ _
  rw [update_right]
  exact .nil ..

/-- The comparison halts within two instructions per common bit and two end tests,
including malformed input with unequal lengths. -/
theorem compare_run (xs ys : List Bool) (eq : Bool) :
    ∃ st : Stacks Bool, StackRuns compareCode (2 * min xs.length ys.length + 2)
      (.left eq) (streams xs ys) (.done (eq && decide (xs = ys))) st := by
  induction xs generalizing ys eq with
  | nil =>
    refine ⟨streams [] ys.tail, ?_⟩
    cases ys with
    | nil => simpa [afterPair] using pair_run [] [] eq
    | cons y ys => simpa [afterPair] using pair_run [] (y :: ys) eq
  | cons x xs ih =>
    cases ys with
    | nil => exact ⟨streams xs [], by simpa [afterPair] using pair_run (x :: xs) [] eq⟩
    | cons y ys =>
      obtain ⟨st, hr⟩ := ih ys (eq && (x == y))
      refine ⟨st, ?_⟩
      rw [List.length_cons, List.length_cons, show min (xs.length + 1) (ys.length + 1) = min xs.length ys.length + 1 by omega,
        show 2*(min xs.length ys.length + 1)+2 = 2+(2*min xs.length ys.length + 2) by omega]
      have h := (pair_run (x :: xs) (y :: ys) eq).trans hr
      cases x <;> cases y <;> simpa [List.cons.injEq, Bool.and_assoc] using h

/-- A raw outgoing message passes the concrete bit comparison exactly when it is the
prescribed frame, including the canonical zero fields in an accepted halt. -/
theorem outgoing_checked (f : Frame w k) (raw : List Bool) :
    ∃ st : Stacks Bool, StackRuns compareCode (2 * min (1+(k+2)*w) raw.length + 2)
      (.left true) (streams f.bits raw) (.done (decide (f.bits = raw))) st := by
  simpa only [Frame.bits_length, Bool.true_and] using compare_run f.bits raw true

/-- A shared successor link has at most one locally admissible typed frame. -/
theorem unique_frame_on_link (raw : List Bool) (f : Frame w k) (h : f.bits = raw) :
    ∃! g : Frame w k, g.bits = raw := ⟨f, h, fun _ hg => Frame.bits_injective (hg.trans h.symm)⟩

end TeamTapeHandoff

end BorderVNP
end Computability
end OAI
