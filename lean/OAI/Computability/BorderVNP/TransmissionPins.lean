import OAI.Computability.BorderVNP.RoutingISAHeader

/-!
# Preparing the live and substituted indices in §11

Frame fields 21 and 22 locate the substituted bit array and the live-column copy.
Field 23 gives the index width and field 24 locates the selected nonzero residue
coordinate. The second literal-sized field of each processor follows all its exterior
bits. The program never writes to these physical inputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- Address of bit `x` in the actual secondary pin fields, flattened in processor order. -/
def livePinAddress (teams literal link x : ℕ) : ℕ :=
  (x/literal)*(2*literal+(teams-1)*link) + (literal+(teams-1)*link) + x%literal

/-- Register initialization shared by the two branches. Registers 3, 4 and 5 contain
the literal width, the processor stride and the extra-field offset. Registers 6, 7
and 8 hold the flat cursor, its full limit, and the real index width. -/
def pinSetup : Code := .block [
  readFrame 0 62 63 0, .constant 1 1, .constant 2 0,
  readFrame 3 62 63 3, readFrame 17 62 63 1, readFrame 18 62 63 4,
  .binary .sub 17 17 1, .binary .mul 17 17 18,
  .binary .add 5 3 17, .binary .add 4 5 3,
  .copy 6 2, readFrame 7 62 63 2, .binary .mul 7 7 3,
  readFrame 8 62 63 23, readFrame 9 62 63 21, readFrame 10 62 63 22, readFrame 11 62 63 24]

/-- Read the live bit from the second field of its processor. -/
def fetchLivePin : Code := .block [
  .binary .div 12 6 3, .binary .mul 12 12 4, .binary .add 12 12 5,
  .binary .mod 13 6 3, .binary .add 12 12 13, .load 14 12]

/-- Copy a real live bit to H, then choose the independently substituted bit for I. -/
def chooseRealPin : Code := .block [
  fetchLivePin, .binary .add 16 10 6, .store 16 14,
  .choose (.copy 15 1) (.copy 15 2)]

/-- The loop writes each substituted position once. Only team zero may choose a bit,
and it does so only before the index width. -/
def preparePinStep : Code := .block [
  .ifEq 0 2 (.ifLt 6 8 chooseRealPin (.copy 15 2)) (.copy 15 2),
  .binary .add 16 9 6, .store 16 15, .binary .add 6 6 1]

/-- The evaluation branch's preparation of the entire substituted pin array. -/
def preparePins : Code := .seq pinSetup (.whileLt 6 7 preparePinStep)

/-- Compare one physical input bit with the corresponding bit of the advised H*. -/
def identityPinStep : Code := .block [
  fetchLivePin, .binary .add 16 11 6, .load 15 16, requireEq 14 15, .binary .add 6 6 1]

/-- Unit-branch check after `unitLinks`. The other teams skip the index comparison.
The team holding the index checks H=H* directly against the true input, without guesses. -/
def checkIdentityPins : Code := .seq pinSetup
  (.ifEq 0 2 (.whileLt 6 8 identityPinStep) .nop)

end RoutingISA

end BorderVNP
end Computability
end OAI
