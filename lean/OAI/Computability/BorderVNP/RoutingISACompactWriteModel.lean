import OAI.Computability.BorderVNP.RoutingISATableState
import OAI.Computability.BorderVNP.RoutingISAHeader

/-! # Fixed native instructions for packing a private descriptor

The caller supplies the machine width, source base, payload length and destination base
in registers two through five. Each pair of payload instructions emits a one marker
followed by the actual Boolean word read from the source. Register nine accumulates
the current word, with register ten holding its next binary place value. The final store
writes the partially filled word containing the mandatory zero terminator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactWrite

/-- Zero the cursor and accumulator and initialize the binary place and word address. -/
def setup : Code := .block [.constant 0 0, .constant 1 1, .copy 6 0, .copy 7 5,
  .copy 8 0, .copy 9 0, .copy 10 1]

/-- Write a completed word, advance the output address and reset the binary place. -/
def flush : Code := .block [.store 7 9, .binary .add 7 7 1, .copy 8 0, .copy 9 0, .copy 10 1]

/-- Append a bit to the current little-endian word. Only the last bit triggers a store. -/
def emit (bit : Reg) : Code := .block [.ifEq bit 0 .nop (.binary .add 9 9 10),
  .binary .add 8 8 1, .ifEq 8 2 flush (.binary .add 10 10 10)]

/-- Read and check a Boolean payload word, emit the marker and digit, and advance the input cursor. -/
def step : Code := .block [.binary .add 12 3 6, .load 11 12,
  .ifEq 11 0 .nop (requireEq 11 1), emit 1, emit 11, .binary .add 6 6 1]

/-- The packed descriptor writer, including the single store for the terminator and padding. -/
def writer : Code := .seq setup (.seq (.whileLt 6 4 step) (.store 7 9))

/-- Original memory outside the completed prefix, target word values inside it. -/
def image (words original : ℕ → ℕ) (dst k a : ℕ) : ℕ :=
  if dst ≤ a ∧ a-dst < k then words (a-dst) else original a

/-- The numerical accumulator and actual memory image after emitting exactly `j` bits. -/
structure At (w dst : ℕ) (words original : ℕ → ℕ) (j : ℕ) (z : NatState) : Prop where
  /-- Current output address. -/
  address : z.reg 7 = dst+j/w
  /-- Bits filled in the current word. -/
  used : z.reg 8 = j%w
  /-- Low-order bits already written into the accumulator. -/
  value : z.reg 9 = words (j/w) % 2^(j%w)
  /-- Place value of the next bit in the current word. -/
  place : z.reg 10 = 2^(j%w)
  /-- Exact completed-word prefix and unchanged remainder of memory. -/
  memory : z.mem = image words original dst (j/w)

/-- Register values retained across all iterations of the payload scan. -/
structure Ready (w src n dst i : ℕ) (z : NatState) : Prop where
  /-- Zero. -/
  zero : z.reg 0 = 0
  /-- One. -/
  one : z.reg 1 = 1
  /-- Machine word width. -/
  width : z.reg 2 = w
  /-- Input base. -/
  source : z.reg 3 = src
  /-- Input word count. -/
  length : z.reg 4 = n
  /-- Output base. -/
  destination : z.reg 5 = dst
  /-- Current input index. -/
  index : z.reg 6 = i

end RoutingISA.CompactWrite

end BorderVNP
end Computability
end OAI
