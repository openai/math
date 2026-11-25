import OAI.Computability.BorderVNP.RoutingISAAddress

/-!
# Physical transmissions and local wire guesses

For each seven-word range the evaluator skips unrelated teams before scanning its bits.
The origin of a remote delivery compares the physical link to its own data. The receiver
reads its corresponding endpoint. A local shared wire chooses a bit once and writes that
bit to both consumers. Registers 0 through 16 carry the persistent range state, and the
fixed endpoint-address routine occupies the upper register bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

namespace Transmission

/-- Initialization of the local team, constants, range and prefix-directory cursors. -/
def setup : Code := .block [
  readFrame 0 27 28 0, .constant 1 1, .constant 2 0, readFrame 3 27 28 12,
  readFrame 4 27 28 13, .copy 5 2, readFrame 6 27 28 20]

/-- Load a directory word and advance the cursor by one. -/
def popWord (dst cursor : Reg) : Code := .seq (.load dst cursor) (.binary .add cursor cursor 1)

/-- The seven directory fields are kind, both teams, length, source, and two destinations.
The eighth word in the separate directory is this range's ordinal within its team pair. -/
def loadRange : Code := .block [
  popWord 8 3, popWord 9 3, popWord 10 3, popWord 11 3,
  popWord 12 3, popWord 13 3, popWord 14 3, popWord 15 6, .copy 16 2]

/-- Place the current bit at the same offset in one of the cell input arrays. -/
def writeBit (dest : Reg) : Code := .seq (.binary .add 17 dest 16) (.store 17 19)

/-- Fetch the origin's actual literal or prepared substituted pin bit. -/
def sourceBit : Code := .seq (.binary .add 17 12 16) (.load 19 17)

/-- Locally shared variables are unconstrained by physical links. Guess once, then fill both
slots from the same register. -/
def localShared : Code := .block [
  .choose (.copy 19 1) (.copy 19 2), writeBit 13, writeBit 14]

/-- When the delivery's two teams coincide, read the source directly. -/
def localData : Code := .seq sourceBit (writeBit 14)

/-- Call the physical address calculation for this range's current bit. -/
def endpoint (peer : Reg) : Code := .block [
  .copy 30 peer, .binary .add 31 15 16, endpointAddress]

/-- Copy a bit of the actual physical endpoint to a local consumer. -/
def receive (peer dest : Reg) : Code := .block [endpoint peer, .load 19 48, writeBit dest]

/-- A remote origin checks its data against the value supplied on the actual link. -/
def send : Code := .block [endpoint 10, .load 20 48, sourceBit, .ifEq 19 20 .nop .reject]

/-- Scan a range once, terminating after its declared number of bits. -/
def scan (bit : Code) : Code :=
  .whileLt 16 11 (.seq bit (.binary .add 16 16 1))

/-- A shared range uses two local slots, or one slot at each of two remote endpoints. -/
def shared : Code :=
  .ifEq 0 9 (.ifEq 9 10 (scan localShared) (scan (receive 10 13)))
    (.ifEq 0 10 (scan (receive 9 14)) .nop)

/-- A data range uses a source bit on team A and a single destination on team B. -/
def delivery : Code :=
  .ifEq 0 9 (.ifEq 9 10 (scan localData) (scan send))
    (.ifEq 0 10 (scan (receive 9 14)) .nop)

/-- Dispatch one decoded range, rejecting a malformed type tag. -/
def dispatch : Code := .ifEq 8 2 shared (.ifEq 8 1 delivery .reject)

/-- Load, process, and advance one public range descriptor. -/
def step : Code := .block [loadRange, dispatch, .binary .add 5 5 1]

end Transmission

/-- The fixed ISA program which handles every data and shared-wire range on one team. -/
def transmitRanges : Code := .seq Transmission.setup (.whileLt 5 4 Transmission.step)

end RoutingISA

end BorderVNP
end Computability
end OAI
