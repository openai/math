import Mathlib.Data.Nat.Bits
import Mathlib.Data.Rat.Defs

/-! Finite bit machines used to state the oracle time bounds. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec

abbrev Word := List Bool

/-- Exchanges in reverse chronological order. The transcript is visible only to the oracle. -/
abbrev Transcript := List (Word × Word)

abbrev WordOracle := Transcript → Word → Word

/-- Delimit an arbitrary binary word: a `true` followed by the next bit, or `false` at the end. -/
def frame (bits : Word) : Word :=
  bits.foldr (fun b rest => true :: b :: rest) [false]

/-- Self-delimiting, little-endian binary representation. -/
def encodeNat (n : ℕ) : Word := frame n.bits

/-- Signed reduced numerator and the positive denominator, both in binary. -/
def encodeRat (x : ℚ) : Word :=
  decide (x.num < 0) :: (encodeNat x.num.natAbs ++ encodeNat x.den)

/-- One primitive instruction of a deterministic machine with finitely many binary stacks. -/
inductive BitInstruction (Q S : Type) where
  | jump (next : Q)
  | push (stack : S) (bit : Bool) (next : Q)
  | pop (stack : S) (next : Q)
  | emit (bit : Bool) (next : Q)
  | ask (next : Q)
  | halt

/-- The transition table is finite. It sees just the selected stack's top bit or an empty marker. -/
structure BitProgram where
  states : ℕ
  stackCount : ℕ
  start : Fin states
  inputStack : Fin stackCount
  answerStack : Fin stackCount
  scan : Fin states → Fin stackCount
  instruction : Fin states → Option Bool → BitInstruction (Fin states) (Fin stackCount)

namespace BitProgram

structure Config (p : BitProgram) where
  pc : Option (Fin p.states)
  store : Fin p.stackCount → Word
  /-- Appending one bit takes one `emit` instruction. Queries empty this buffer. -/
  bufferRev : Word
  transcript : Transcript

def initial (p : BitProgram) (input : Word) : p.Config where
  pc := some p.start
  store := fun s => if s = p.inputStack then input else []
  bufferRev := []
  transcript := []

/-- A query submits a fresh, fully written word and reads its answer onto the answer stack.
The extra word-length charge accounts for transferring both words at the oracle boundary. -/
def tick (p : BitProgram) (oracle : WordOracle) (c : p.Config) : Option (ℕ × p.Config) := do
  let q ← c.pc
  match p.instruction q (c.store (p.scan q)).head? with
  | .jump q' => return (1, {c with pc := some q'})
  | .push s b q' =>
    return (1, {c with pc := some q', store := Function.update c.store s (b :: c.store s)})
  | .pop s q' =>
    return (1, {c with pc := some q', store := Function.update c.store s (c.store s).tail})
  | .emit b q' => return (1, {c with pc := some q', bufferRev := b :: c.bufferRev})
  | .ask q' =>
    let packet := c.bufferRev.reverse
    let answer := oracle c.transcript packet
    return (1 + packet.length + answer.length,
      { pc := some q', store := Function.update c.store p.answerStack answer,
        bufferRev := [], transcript := (packet, answer) :: c.transcript })
  | .halt => return (1, {c with pc := none})

/-- A trace of actual instructions, indexed by the total number of charged bit steps. -/
inductive Run (p : BitProgram) (oracle : WordOracle) : p.Config → ℕ → p.Config → Prop where
  | refl (c) : Run p oracle c 0 c
  | step {c c' c'' n k} : p.tick oracle c = some (k, c') →
      Run p oracle c' n c'' → Run p oracle c (k + n) c''

/-- The machine itself cannot see `post`, its past transcript, the clock, or the time bound. -/
def ComputesWithin (p : BitProgram) (oracle : WordOracle) (input : Word) (budget : ℕ)
    (post : Transcript → Word → Prop) : Prop :=
  ∃ (elapsed : ℕ) (c : p.Config), p.Run oracle (p.initial input) elapsed c ∧
    elapsed ≤ budget ∧ c.pc = none ∧ post c.transcript c.bufferRev.reverse

end BitProgram
end OracleSpec
end LinearProgramming
end Optimization
end OAI
