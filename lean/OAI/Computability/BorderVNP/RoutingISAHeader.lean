import OAI.Computability.BorderVNP.RoutingISATable

/-!
# Reading the common branch and checking physical relay bits

Each team checks its incident prefix words, each occupied relay position,
and every padding bit directly in its own input segment. The reference
partner is team zero except at team zero, which uses team one. The canonical
unit branch is encoded by zero and the evaluation branch by one.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- Load the common physical sizes and verify the positive divisor, available
reference partner, and nonempty prefix. -/
def headerSetup : Code := .block [
  .constant 0 0, .constant 1 1, .constant 14 2,
  readFrame 2 62 63 0, readFrame 3 62 63 1, readFrame 4 62 63 4,
  readFrame 5 62 63 2, readFrame 6 62 63 5, readFrame 9 62 63 25,
  requireLt 14 3, requireLt 2 3, requireLt 0 4, requireLt 0 5, requireLt 0 6,
  .binary .mul 7 4 5, .ifLt 7 6 .reject .nop,
  .ifEq 2 0 (.copy 8 1) (.copy 8 0)]

/-- Read one physical block word using the partner and flat position registers. -/
def readPhysical (partner position dst : Reg) : Code :=
  .block [.copy 30 partner, .copy 31 position, physicalAddress, .load dst 48]

/-- Range-check and save a reference bit, then increment the bit cursor. -/
def saveHeaderBit : Code := .block [
  requireLt 12 14, .binary .add 13 9 10, .store 13 12, .binary .add 10 10 1]

/-- One iteration copying the common header, including its bit-range check. -/
def copyHeaderBit : Code := .seq (readPhysical 8 10 12) saveHeaderBit
/-- Copy the reference block's common header bit by bit into contiguous memory.
The live word is checked to encode a bit at every position. -/
def copyHeader : Code := .block [
  .copy 10 0, .whileLt 10 6 copyHeaderBit]

/-- Load the reference copy, compare the two bits, and advance the cursor. -/
def compareSavedBit : Code := .block [
  .binary .add 13 9 10, .load 15 13, requireEq 12 15, .binary .add 10 10 1]

/-- One equality test against a previously stored reference bit. -/
def compareHeaderBit : Code := .seq (readPhysical 11 10 12) compareSavedBit
/-- Process a complete incident prefix, skipping the absent self block. -/
def compareHeaderPartner : Code := .block [
  .ifEq 11 2 .nop (.block [.copy 10 0, .whileLt 10 6 compareHeaderBit]),
  .binary .add 11 11 1]

/-- Compare every other incident prefix against the reference copy. A
disagreement rejects before any evaluation instruction runs. -/
def compareHeaders : Code := .block [
  .copy 11 0, .whileLt 11 3 compareHeaderPartner]

/-- Obtain one common header before branching. -/
def readBroadcast : Code := .block [headerSetup, copyHeader, compareHeaders]

/-- Check all positions of the team's physical input blocks against zero on
the unit branch. There are no branch guesses or private macro calls. -/
def unitLinks : Code := .block [
  headerSetup, .copy 11 0, .whileLt 11 3 (.block [
    .ifEq 11 2 .nop (.block [.copy 10 0, .whileLt 10 7 (.block [
      .copy 30 11, .copy 31 10, physicalAddress, .load 12 48, requireEq 12 0, .binary .add 10 10 1])]),
    .binary .add 11 11 1])]

/-- At a relay, compare the endpoint legs using their two actual addresses,
one check per occupied local quotient. Registers 21 and 23 are the endpoints,
22 is the current team (relay), and 28 is the count for this ordered list. -/
def compareRelayPositions : Code := .block [
  .copy 16 0, .whileLt 16 28 (.block [
    .copy 32 21, .copy 33 22, .copy 34 23, .copy 35 16, legAddress, .load 17 48,
    .copy 32 23, .copy 33 22, .copy 34 21, .copy 35 16, legAddress, .load 14 48,
    requireEq 17 14, requireLt 17 2, .binary .add 16 16 1])]

/-- Scan the sparse endpoint-pair table and expand only local relay positions.
A pair in which this team is an endpoint has scheduled length zero. -/
def checkRelays : Code := .block [
  tableSetup, readFrame 22 62 63 0, .copy 21 0,
  .whileLt 21 3 (.block [
    .binary .add 23 21 1, .whileLt 23 3 (.block [
      scheduledLengthWord, compareRelayPositions, .binary .add 23 23 1]),
    .binary .add 21 21 1])]

/-- Validate the sum of the header and both direction widths, then check all
unused physical positions to the end of each incident block. -/
def checkPadding : Code := .block [
  headerSetup, readFrame 19 62 63 18, .copy 11 0, .whileLt 11 3 (.block [
    .ifEq 11 2 .nop (.block [
      pairAddress 13 2 11 3 19, .load 16 13, pairAddress 13 11 2 3 19, .load 17 13,
      .binary .add 10 6 16, .ifLt 10 6 .reject .nop,
      .binary .add 18 10 17, .ifLt 18 10 .reject .nop, .copy 10 18, .ifLt 7 10 .reject .nop,
      .whileLt 10 7 (.block [
        .copy 30 11, .copy 31 10, physicalAddress, .load 12 48, requireEq 12 0,
        .binary .add 10 10 1])]),
    .binary .add 11 11 1])]

namespace CellDispatch

/-- Load the team number and the base and length of the cell directory. -/
def setup : Code := .block [
  .constant 0 0, .constant 1 1, .constant 2 3, readFrame 3 62 63 0,
  readFrame 4 62 63 14, readFrame 5 62 63 15, .copy 6 0]

/-- Compute the next row address and read its owner. -/
def readOwner : Code := .block [.binary .mul 7 6 2, .binary .add 7 7 4, .load 8 7]

/-- Read the base and the length of the argument interval. -/
def readArgs : Code := .block [.binary .add 7 7 1, .load 9 7, .binary .add 7 7 1, .load 10 7]

/-- Advance one directory row. -/
def increment : Code := .binary .add 6 6 1

/-- Conditional private call for the row followed by the common cursor advance. -/
def body : Code := .seq readOwner (.seq
  (.ifEq 3 8 (.seq readArgs (.call 0 9 10)) .nop) increment)

end CellDispatch

/-- Visit the word-level public cell-call directory. Each row is (owner,
argument address, argument length), and only its assigned owner calls
private routine zero on that contiguous word interval. -/
def callOwnedCells : Code := .seq CellDispatch.setup (.whileLt 6 5 CellDispatch.body)

end RoutingISA

end BorderVNP
end Computability
end OAI
