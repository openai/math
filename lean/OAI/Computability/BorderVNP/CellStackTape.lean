import OAI.Computability.BorderVNP.CellBytecode
import OAI.Computability.BorderVNP.TeamPrivateValue

/-! # Calling a named-stack cell validator as a private multitape routine

The head of each tape scans the top of one named stack. A blank terminates that stack.
Push moves to the left, then writes. Pop erases the scanned digit and moves right.
Each instruction takes two native steps, with just one binary choice for a guess.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.StackTape

open VPVNP.RAMTape TeamPrivateTape TeamPrivateValue

variable {K Q : Type} {m : ℕ} [DecidableEq K]

/-- Read the occupied portion of a stack tape, stopping at its first blank. -/
def digits : List (Option Bool) → List Bool
  | [] | none :: _ => []
  | some b :: xs => b :: digits xs

/-- Abstract stack bank seen at an instruction boundary. -/
def values (e : K ≃ Fin m) (t : Fin m → SymbolTape (Option Bool)) : Stacks K :=
  fun k => digits ((t (e k)).head :: (t (e k)).right)

/-- Two native transitions per continuing stack instruction. -/
inductive Control (Q : Type) (m : ℕ) where
  | ready (q : Q)
  | idle (q : Q)
  | write (i : Fin m) (bit : Bool) (q : Q)
  deriving Fintype

private abbrev Head (m : ℕ) := Fin m → Option Bool
private abbrev Tapes (m : ℕ) := Fin m → SymbolTape (Option Bool)

private def stay (q : Control Q m) (h : Head m) : TapeCommand (Control Q m) (Option Bool) m :=
  ⟨q, h, fun _ => none⟩

private def seek (q : Q) (i : Fin m) (b : Bool) (h : Head m) : TapeCommand (Control Q m) (Option Bool) m :=
  ⟨.write i b q, h, Function.update (fun _ => none) i (some false)⟩

private def write (q : Q) (i : Fin m) (b : Bool) (h : Head m) : TapeCommand (Control Q m) (Option Bool) m :=
  ⟨.ready q, Function.update h i (some b), fun _ => none⟩

private def pop (f : Option Bool → Q) (i : Fin m) (h : Head m) : TapeCommand (Control Q m) (Option Bool) m :=
  ⟨.idle (f (h i)), Function.update h i none, Function.update (fun _ => none) i ((h i).map fun _ => true)⟩

/-- A fixed native private tape table for any signed validator on finitely many named stacks. -/
def table (e : K ≃ Fin m) (program : StackCode K Q) (neg : Q → Bool) :
    TapeTable (Control Q m) (Option Bool) m
  | .idle q, h => .one (stay (.ready q) h)
  | .write i b q, h => .one (write q i b h)
  | .ready q, h => match program q with
    | .halt ok => .halt ok (neg q)
    | .goto q' => .one (stay (.idle q') h)
    | .choose l r => .two (stay (.idle l) h) (stay (.idle r) h)
    | .push k b q' => .one (seek q' (e k) b h)
    | .pop k f => .one (pop f (e k) h)

private def head (t : Tapes m) : Head m := fun i => (t i).head

private theorem stay_eq (t : Tapes m) (q : Control Q m) :
    (stay q (head t)).apply none t = t := by funext i; rfl

private theorem push_eq (e : K ≃ Fin m) (k : K) (b : Bool) (q : Q) (t : Tapes m) :
    let u := (seek q (e k) b (head t)).apply none t
    values e ((write q (e k) b (head u)).apply none u) =
      Function.update (values e t) k (b :: values e t k) := by
  dsimp only
  funext j
  by_cases hj : j = k
  · subst j
    simp [values, seek, write, TapeCommand.apply, head, SymbolTape.move, digits]
  · have hn : e j ≠ e k := fun he => hj (e.injective he)
    simp [values, seek, write, TapeCommand.apply, head, SymbolTape.move, hj, hn]

private theorem tail_digits (xs : List (Option Bool)) :
    digits (xs.head?.getD none :: xs.tail) = digits xs := by
  cases xs <;> rfl

private theorem pop_eq (e : K ≃ Fin m) (k : K) (f : Option Bool → Q) (t : Tapes m) :
    values e ((pop f (e k) (head t)).apply none t) =
      Function.update (values e t) k (values e t k).tail := by
  funext j
  by_cases hj : j = k
  · subst j
    cases h : (t (e k)).head <;>
      simp [values, pop, TapeCommand.apply, head, SymbolTape.move, digits, h, tail_digits]
  · have hn : e j ≠ e k := fun he => hj (e.injective he)
    simp [values, pop, TapeCommand.apply, head, SymbolTape.move, hj, hn]

omit [DecidableEq K] in
private theorem head_eq (e : K ≃ Fin m) (k : K) (t : Tapes m) :
    (values e t k).head? = (t (e k)).head := by cases h : (t (e k)).head <;> simp [values, h, digits]

/-- At twice the stack clock the native machine has precisely the same signed count and
stops on every branch exactly when the stack machine does. -/
theorem simulation (e : K ≃ Fin m) (program : StackCode K Q) (neg : Q → Bool)
    (fuel : ℕ) (q : Q) (t : Tapes m) :
    (TapeStops (table e program neg) none (2*fuel) (.ready q) t ↔
      StopsWithin program fuel q (values e t)) ∧
    tapePaths (table e program neg) none (2*fuel) (.ready q) t =
      TeamStack.paths program neg fuel q (values e t) := by
  induction fuel generalizing q t with
  | zero => exact ⟨Iff.rfl,rfl⟩
  | succ fuel ih =>
    rw [Nat.mul_succ]
    cases h : program q with
    | halt ok => simp [TapeStops, StopsWithin, tapePaths, TeamStack.paths, table, h]
    | goto r =>
      simp only [TapeStops, StopsWithin, tapePaths, TeamStack.paths, table, h, stay]
      exact ih r t
    | choose l r =>
      simp only [TapeStops, StopsWithin, tapePaths, TeamStack.paths, table, h, stay]
      exact ⟨and_congr (ih l t).1 (ih r t).1, congrArg₂ (· + ·) (ih l t).2 (ih r t).2⟩
    | pop k f =>
      let u := (pop f (e k) (head t)).apply none t
      have hp := ih (f (head t (e k))) u
      simp only [TapeStops, StopsWithin, tapePaths, TeamStack.paths, table, h, pop, stay]
      rw [← pop_eq e k f t, head_eq]
      exact hp
    | push k b r =>
      let u := (seek r (e k) b (head t)).apply none t
      have hp := ih r ((write r (e k) b (head u)).apply none u)
      simp only [TapeStops, StopsWithin, tapePaths, TeamStack.paths, table, h, seek, write]
      rw [← push_eq e k b r t]
      exact hp

private theorem digits_map (xs : List Bool) : digits (xs.map some) = xs := by
  induction xs with | nil => rfl | cons b xs ih => simp [digits, ih]

/-- Loading the ordinary private input tape places exactly the incoming bit string on its
named port, with all the other stacks empty. -/
theorem values_input (e : K ≃ Fin m) (i : K) (xs : List Bool) :
    values e (input none some (e i) xs) = Function.update (fun _ => []) i xs := by
  funext k
  by_cases h : k = i
  · subst k
    cases xs with
    | nil => simp [values, input, digits]
    | cons b xs => simp [values, input, digits, digits_map]
  · have he : e k ≠ e i := fun eq => h (e.injective eq)
    simp [values, input, h, he, digits]

end CellMacro.StackTape

end BorderVNP
end Computability
end OAI
