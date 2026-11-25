import OAI.Computability.BorderVNP.RoutingISA
import OAI.Computability.VPVNP.BooleanTranscript

/-!
# A fixed word-RAM reader for a Boolean residue-entry verifier

The binary circuit is advice. The input words hold the query bits, followed by
room for one word per private guess and one per shared gate. Each gate has
three advice words: two absolute source addresses and a complement bit.
Thus AND and NOT use the same instruction sequence. A field element, pin or
exponent can occupy arbitrarily many bits; only addresses must fit in words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM VPVNP.BooleanTranscript RoutingISA

/-- Number of the first valuation cell containing a gate rather than an input. -/
def gateBase (base u v : ℕ) : ℕ := base + 2 + u + v

/-- Absolute address of an input, constant or earlier shared gate. -/
def address {u v k : ℕ} (base : ℕ) : Ref Bool (Fin u ⊕ Fin v) k → ℕ
  | .const b => base + b.toNat
  | .var (.inl i) => base + 2 + i.val
  | .var (.inr j) => base + 2 + u + j.val
  | .gate i => gateBase base u v + i.val

/-- Three consecutive advice words describe a single gate. -/
structure Row where
  /-- Left source address. -/
  left : ℕ
  /-- Right source address. For NOT this repeats the left source. -/
  right : ℕ
  /-- Complement the AND of the two source bits. -/
  invert : Bool

/-- Emit the literal advice words for one gate. -/
def gateRow {u v k : ℕ} (base : ℕ) : Gate (Fin u ⊕ Fin v) k → Row
  | .and a b => ⟨address base a, address base b, false⟩
  | .not a => ⟨address base a, address base a, true⟩

/-- Read the gate at a specified position in the typed program. -/
def rows {u v : ℕ} (base : ℕ) : {k : ℕ} → Program (Fin u ⊕ Fin v) k → Fin k → Row
  | _, .nil => Fin.elim0
  | _, .snoc prog g => Fin.snoc (rows base prog) (gateRow base g)

/-- Set the unit, zero, first guess address and guess counter. -/
def setup : Code := .block [
  .constant 38 1, .constant 39 0, .constant 40 2,
  .binary .add 40 35 40, .binary .add 40 40 37, .copy 41 39]

/-- Guess one input bit, store it, and advance both counters. -/
def guessBody : Code := .block [
  .choose (.copy 42 38) (.copy 42 39),
  .store 40 42, .binary .add 40 40 38, .binary .add 41 41 38]

/-- Execute the three-word advice record, append its value and advance. -/
def gateBody : Code := .block [
  .load 43 42, .binary .add 42 42 38, .load 44 42, .binary .add 42 42 38,
  .load 45 42, .binary .add 42 42 38, .load 43 43, .load 44 44,
  .binary .bitAnd 46 43 44, .binary .bitXor 46 46 45, .store 40 46,
  .binary .add 40 40 38, .binary .add 41 41 38]

/-- The interpreter uses registers 32–46. On entry 32,33 hold the gate and
guess counts, 34,35 the advice and valuation bases, 36 the absolute output
address, and 37 the number of query bits. On return 42 holds the output. -/
def evaluate : Code := .block [
  setup, .whileLt 41 33 guessBody, .copy 41 39, .copy 42 34,
  .whileLt 41 32 gateBody, .load 42 36]

/-- An accepting path falls through. A zero result rejects. -/
def reader : Code := .seq evaluate (.ifEq 42 38 .nop .reject)

/-- The native table is fixed before the circuit, prime, lengths and input. -/
def machine : TeamOpcode.Program (reader.slots + 1) 64 32 8 := reader.program

/-- The fixed advice consists of three words per shared gate, and one header
word each for the dimensions, addresses and designated output. -/
def adviceWords (g : ℕ) : ℕ := 3 * g + 6

/-- Exact number of ordinary ticks through the final result test on a
successful path. The fall-through accept occupies the next PC. -/
def ticks (g v : ℕ) : ℕ := 6 * v + 14 * g + 13

/-- The RAM instruction and advice costs are linear in the bit verifier's size. -/
theorem costs_le (g v : ℕ) :
    ticks g v + adviceWords g ≤ 20 * (g + v + 1) := by
  unfold ticks adviceWords
  omega

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
