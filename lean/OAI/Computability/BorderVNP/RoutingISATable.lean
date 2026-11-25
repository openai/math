import OAI.Computability.BorderVNP.RoutingISAAddress

/-!
# The sparse physical scheduling program

Each transmission record is a seven-word interval. A first pass stores its
starting ordinal and accumulates a width for its unordered endpoint pair.
Three nested team loops tabulate all prefix offsets from lengths alone. The
code never visits individual wire bits while constructing the schedule.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- Reject when an unsigned loop counter is outside its declared interval. -/
def requireLt (x bound : Reg) : Code := .ifLt x bound .nop .reject

/-- Reject when the two unsigned operands differ. -/
def requireEq (x y : Reg) : Code := .ifEq x y .nop .reject

/-- Set register `out` to the lower of two team numbers, and `high` to the higher. -/
def orderPair (x y out high : Reg) : Code :=
  .ifLt x y (.block [.copy out x, .copy high y]) (.block [.copy out y, .copy high x])

/-- Common constants, sizes and the four writable tables for public scheduling. -/
def tableSetup : Code := .block [
  .constant 0 0, .constant 1 1, .constant 2 2, .constant 12 7,
  readFrame 3 62 63 1, requireLt 2 3, .binary .mul 4 3 3, .binary .sub 5 3 2,
  readFrame 6 62 63 12, readFrame 7 62 63 13, readFrame 8 62 63 16,
  readFrame 9 62 63 17, readFrame 10 62 63 18, readFrame 11 62 63 20]

/-- Clear one word per unordered-pair table address, including the unused
lower triangle. -/
def clearPairWidths : Code := .block [
  .copy 13 0, .whileLt 13 4 (.block [.binary .add 14 8 13, .store 14 0, .binary .add 13 13 1])]

/-- Process one public interval, saving the prior pair width as its first
ordinal. A co-located interval needs no paired transmission positions. -/
def tabulateInterval : Code := .block [
  .binary .mul 14 13 12, .binary .add 14 14 6, .load 15 14, requireLt 15 2,
  .binary .add 14 14 1, .load 16 14, requireLt 16 3,
  .binary .add 14 14 1, .load 17 14, requireLt 17 3,
  .binary .add 14 14 1, .load 18 14, .binary .add 29 11 13,
  .ifEq 16 17 (.store 29 0) (.block [
    orderPair 16 17 26 27, pairAddress 19 26 27 3 8, .load 20 19, .store 29 20,
    .binary .add 28 20 18, .ifLt 28 20 .reject .nop, .store 19 28]),
  .binary .add 13 13 1]

/-- Prefix the lists in record order, retaining their whole widths as word
descriptors instead of expanding their contents. -/
def intervalPass : Code := .block [.copy 13 0, .whileLt 13 7 tabulateInterval]

/-- Evaluate the arithmetic length formula for one partner. Registers 21,
22, 23 name the endpoint, relay and partner; register 28 receives the length.
Register 5 stores the strictly positive period `R−2`. -/
def scheduledLengthWord : Code := .block [
  .copy 28 0, .ifEq 21 22 .nop (.ifEq 21 23 .nop (.ifEq 22 23 .nop (.block [
    orderPair 21 23 26 27, pairAddress 19 26 27 3 8, .load 18 19,
    .copy 29 22, .ifLt 26 22 (.binary .sub 29 29 1) .nop,
    .ifLt 27 22 (.binary .sub 29 29 1) .nop,
    .ifLt 29 18 (.block [.binary .sub 28 18 1, .binary .sub 28 28 29,
      .binary .div 28 28 5, .binary .add 28 28 1]) .nop])))]

/-- Store one prefix and update the running count by quotient arithmetic. -/
def tabulatePartner : Code := .block [
  tripleAddress 24 21 22 23 3 9, .store 24 20, scheduledLengthWord,
  .binary .add 29 20 28, .ifLt 29 20 .reject .nop, .copy 20 29, .binary .add 23 23 1]

/-- Tabulate all prefix offsets for one oriented physical block, then store
its total width so that the reverse use can be placed after it. -/
def tabulateLeg : Code := .block [
  .copy 20 0, .copy 23 0, .whileLt 23 3 tabulatePartner,
  pairAddress 25 21 22 3 10, .store 25 20, .binary .add 22 22 1]

/-- The whole public cubic table; all traversal counters are held in the
fixed register bank and the only large objects are addressable arrays. -/
def offsetPass : Code := .block [
  .copy 21 0, .whileLt 21 3 (.block [
    .copy 22 0, .whileLt 22 3 tabulateLeg, .binary .add 21 21 1])]

/-- Compute the actual public schedule from interval descriptors, using the
two possible orientations of each physical block. -/
def scheduleTable : Code := .block [tableSetup, clearPairWidths, intervalPass, offsetPass]

end RoutingISA

end BorderVNP
end Computability
end OAI
