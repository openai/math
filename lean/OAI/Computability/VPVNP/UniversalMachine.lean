import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Data.List.OfFn

/-!
# The coefficient machine of “VP and VNP differ over every field”, §1.1

We fix two two-way tapes over the alphabet blank, zero, one (codes 0, 1, 2). States 0 and 1
halt with rejection and acceptance. The running states start at 2. Every transition writes
one symbol on each tape, moves each head by at most one cell and enters its target state.

The prefix is the table's bit length in unary (`1^k 0`) followed by exactly `k` bits. Inside
that table each natural-number field is also unary. The empty table has no running states and
starts in the accepting state. Otherwise the first field is the number of running states minus
one. The remaining fields give all nine rows for each running state, ordered by state, first
head and second head. Each row is a branch count (0, 1 or 2) followed by that many records.
A record lists target, first symbol, first move, second symbol, second move. Moves 0, 1 and 2
mean stay, left and right. All fields are literal. Both tapes start with the head at cell 0,
and the first tape carries the complete input, including the program prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

/-- The tape alphabet encodes blank, binary zero and binary one as 0, 1 and 2. -/
abbrev Symbol := Fin 3
/-- A finite binary input, including its literal program prefix. -/
abbrev Word := List Bool

/-- `target = 0` rejects, `target = 1` accepts, and `target = 2 + i` enters running state `i`. -/
structure Instruction (extra : ℕ) where
  /-- The state entered after the writes and head movements. -/
  target : Fin (extra + 2)
  /-- Symbol written under the first head. -/
  firstSymbol : Symbol
  /-- First-head movement, in the order stay, left, right. -/
  firstMove : Fin 3
  /-- Symbol written under the second head. -/
  secondSymbol : Symbol
  /-- Second-head movement, in the order stay, left, right. -/
  secondMove : Fin 3

/-- Each branch occupies its own slot, even if two transitions are identical. -/
inductive Branches (extra : ℕ)
  | stop
  | one (a : Instruction extra)
  | two (a b : Instruction extra)

/-- A finite nondeterministic table with a row for each running state and symbol pair. -/
structure Program where
  /-- Number of states besides the two halting states. -/
  extra : ℕ
  /-- Transition lists ordered by state, first-head symbol, then second-head symbol. -/
  rows : List (Branches extra)
  rows_length : rows.length = extra * 9

/-- The state and both head-centered tapes at one instant of a computation. -/
structure Config (extra : ℕ) where
  /-- The current running or halting state. -/
  state : Fin (extra + 2)
  /-- The tape that initially holds the input word. -/
  firstTape : Turing.Tape Symbol
  /-- The initially blank work tape. -/
  secondTape : Turing.Tape Symbol

/-- The empty table is the machine that starts already halted in acceptance. -/
def emptyProgram : Program := ⟨0, [], rfl⟩

/-- Start at the first running state with the complete input on the first tape.
The empty table starts in the accepting state. -/
def initial (p : Program) (input : Word) : Config p.extra where
  state := if h : p.extra = 0 then ⟨1, by omega⟩ else ⟨2, by omega⟩
  firstTape := Turing.Tape.mk₁ (input.map fun b => if b then 2 else 1)
  secondTape := Turing.Tape.mk₁ []

/-- Look up the transition slots for the current running state and the two scanned symbols. -/
def branches (p : Program) (c : Config p.extra) : Branches p.extra :=
  p.rows[(c.state.val - 2) * 9 + c.firstTape.head.val * 3 + c.secondTape.head.val]?.getD .stop

/-- Write at the head and then carry out its specified movement. -/
def updateTape (t : Turing.Tape Symbol) (write : Symbol) (move : Fin 3) :=
  let t' := t.write write
  match move.val with
  | 0 => t'
  | 1 => t'.move .left
  | _ => t'.move .right

/-- Apply one chosen transition to both tapes and enter its target state. -/
def advance {extra : ℕ} (c : Config extra) (a : Instruction extra) : Config extra where
  state := a.target
  firstTape := updateTape c.firstTape a.firstSymbol a.firstMove
  secondTape := updateTape c.secondTape a.secondSymbol a.secondMove

/-- Accepting leaves within `fuel` transitions of the encoded machine, including time zero. -/
def paths (p : Program) : ℕ → Config p.extra → ℕ
  | 0, c => if c.state.val = 1 then 1 else 0
  | fuel + 1, c =>
    if c.state.val = 1 then 1 else if c.state.val = 0 then 0 else
      match branches p c with
      | .stop => 0
      | .one a => paths p fuel (advance c a)
      | .two a b => paths p fuel (advance c a) + paths p fuel (advance c b)

theorem paths_accept (p : Program) (c : Config p.extra) (hc : c.state.val = 1) (fuel : ℕ) :
    paths p fuel c = 1 := by cases fuel <;> simp [paths, hc]

theorem paths_reject (p : Program) (c : Config p.extra) (hc : c.state.val = 0) (fuel : ℕ) :
    paths p fuel c = 0 := by cases fuel <;> simp [paths, hc]

/-- The unary field for a number, including the terminating zero. -/
def unary (k : ℕ) : Word := List.replicate k true ++ [false]

private def readUnary : Word → Option (ℕ × Word)
  | [] => none
  | false :: xs => some (0, xs)
  | true :: xs => (fun (k, rest) => (k + 1, rest)) <$> readUnary xs

private theorem readUnary_append (k : ℕ) (xs : Word) :
    readUnary (unary k ++ xs) = some (k, xs) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (fun (j, rest) => (j + 1, rest)) <$> readUnary (unary k ++ xs) = _
    rw [ih]
    rfl

/-- Read all unary fields in the table. A last field with no terminator fails. -/
private def readFields : Word → Option (List ℕ)
  | [] => some []
  | false :: xs => (0 :: ·) <$> readFields xs
  | true :: xs => do
    let k :: rest ← readFields xs | none
    return (k + 1) :: rest

private def checkFin (m k : ℕ) : Option (Fin m) :=
  if h : k < m then some ⟨k, h⟩ else none

private def readInstruction (extra : ℕ) : List ℕ → Option (Instruction extra × List ℕ)
  | q :: x :: u :: y :: v :: rest => do
    let target ← checkFin (extra + 2) q
    let firstSymbol ← checkFin 3 x
    let firstMove ← checkFin 3 u
    let secondSymbol ← checkFin 3 y
    let secondMove ← checkFin 3 v
    return (⟨target, firstSymbol, firstMove, secondSymbol, secondMove⟩, rest)
  | _ => none

private def readBranch (extra : ℕ) : List ℕ → Option (Branches extra × List ℕ)
  | 0 :: xs => some (.stop, xs)
  | 1 :: xs => do
    let (a, rest) ← readInstruction extra xs
    return (.one a, rest)
  | 2 :: xs => do
    let (a, rest) ← readInstruction extra xs
    let (b, tail) ← readInstruction extra rest
    return (.two a b, tail)
  | _ => none

private def readRows (extra : ℕ) : ℕ → List ℕ → Option (List (Branches extra) × List ℕ)
  | 0, xs => some ([], xs)
  | count + 1, xs => do
    let (b, rest) ← readBranch extra xs
    let (bs, tail) ← readRows extra count rest
    return (b :: bs, tail)

private def decodeTable (table : Word) : Option Program := do
  match ← readFields table with
  | [] => return emptyProgram
  | k :: xs =>
    let extra := k + 1
    let (rows, []) ← readRows extra (extra * 9) xs | none
    if h : rows.length = extra * 9 then return ⟨extra, rows, h⟩ else none

/-- Decode just the program prefix. The payload is unrestricted. -/
def decode (input : Word) : Option Program := do
  let (len, rest) ← readUnary input
  if len ≤ rest.length then decodeTable (rest.take len) else none

/-- The five integer fields that encode a single instruction. -/
def instructionFields {extra : ℕ} (a : Instruction extra) : List ℕ :=
  [a.target, a.firstSymbol, a.firstMove, a.secondSymbol, a.secondMove]

/-- Encode the number of branches followed by their instructions in slot order. -/
def branchFields {extra : ℕ} : Branches extra → List ℕ
  | .stop => [0]
  | .one a => 1 :: instructionFields a
  | .two a b => 2 :: (instructionFields a ++ instructionFields b)

/-- Serialize the table with no implicit rows or unbounded instructions. -/
def tableBits (p : Program) : Word :=
  if p.extra = 0 then [] else ((p.extra - 1) :: p.rows.flatMap branchFields).flatMap unary

/-- A literal prefix, independent of the subsequent payload. -/
def programPrefix (p : Program) : Word := unary (tableBits p).length ++ tableBits p

private theorem readFields_unary (k : ℕ) (xs : Word) :
    readFields (unary k ++ xs) = (k :: ·) <$> readFields xs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (do
      let j :: rest ← readFields (unary k ++ xs) | none
      return (j + 1) :: rest) = _
    rw [ih]
    cases readFields xs <;> rfl

private theorem readFields_encode (xs : List ℕ) : readFields (xs.flatMap unary) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, readFields_unary, ih]

private theorem readInstruction_encode {extra : ℕ} (a : Instruction extra) (xs : List ℕ) :
    readInstruction extra (instructionFields a ++ xs) = some (a, xs) := by
  cases a
  simp [instructionFields, readInstruction, checkFin]

private theorem readBranch_encode {extra : ℕ} (b : Branches extra) (xs : List ℕ) :
    readBranch extra (branchFields b ++ xs) = some (b, xs) := by
  cases b <;> simp [branchFields, readBranch, List.append_assoc, readInstruction_encode]

private theorem readRows_encode {extra : ℕ} (bs : List (Branches extra)) (xs : List ℕ) :
    readRows extra bs.length (bs.flatMap branchFields ++ xs) = some (bs, xs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.flatMap_cons, List.append_assoc, readRows, readBranch_encode, ih]

private theorem decodeTable_encode (p : Program) : decodeTable (tableBits p) = some p := by
  rcases p with ⟨extra, rows, hrows⟩
  cases extra with
  | zero =>
    have : rows = [] := List.length_eq_zero_iff.mp (by simpa using hrows)
    subst rows
    rfl
  | succ k =>
    have h := readRows_encode rows []
    simp only [List.append_nil, hrows] at h
    simp [tableBits, decodeTable, readFields_unary, readFields_encode, h, hrows]

/-- Decoding the self-delimiting prefix recovers the exact machine, on every payload. -/
theorem decode_programPrefix (p : Program) (payload : Word) :
    decode (programPrefix p ++ payload) = some p := by
  simp [decode, programPrefix, List.append_assoc, readUnary_append, decodeTable_encode]

theorem decode_false_cons (payload : Word) : decode (false :: payload) = some emptyProgram := by
  simp [decode, readUnary, decodeTable, readFields]

end UniversalMachine

section

open UniversalMachine

/-- The exponent `K_*` from §1.1. -/
def clockExponent : ℕ := 10 ^ 9

/-- The integer coefficient `U_n(x)` of equation (1.1), prior to casting to a field. -/
def acceptingCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  let input := List.ofFn x
  match decode input with
  | none => 0
  | some p => paths p (n ^ clockExponent) (initial p input)

theorem acceptingCount_of_malformed {n : ℕ} (x : Fin n → Bool) (h : decode (List.ofFn x) = none) :
    acceptingCount x = 0 := by simp [acceptingCount, h]

theorem acceptingCount_allFalse {n : ℕ} (hn : 0 < n) :
    acceptingCount (fun _ : Fin n => false) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [acceptingCount, List.ofFn_succ, decode_false_cons]
  apply paths_accept
  rfl

end

end VPVNP
end Computability
end OAI
