import OAI.Computability.BorderVNP.RoutingISABroadcastModel
import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Copying one literal advice bit per processor to a consecutive array -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- Read the literal geometry and the destination directory from the true
scratch frame. One word at the designated offset is consumed per processor. -/
def literalAdviceSetup : Code := .block [
  readFrame 30 62 63 1, readFrame 31 62 63 2, readFrame 32 62 63 3, readFrame 33 62 63 4,
  readFrame 34 62 63 26, readFrame 35 62 63 27, readFrame 36 62 63 28,
  .constant 39 0, .constant 40 1, .constant 41 2, requireLt 34 32, .ifLt 31 35 .reject .nop,
  .binary .sub 38 30 40, .binary .mul 38 38 33, .binary .mul 37 32 41, .binary .add 38 38 37]

/-- Read the selected literal bit of the current processor, test its Boolean
word encoding and store the word at its consecutive advice-array address. -/
def literalAdviceBit : Code := .block [
  .binary .mul 42 39 38, .binary .add 42 42 34, .load 43 42, requireLt 43 41,
  .binary .add 44 36 39, .store 44 43, .binary .add 39 39 40]

/-- The finite startup fragment that copies strided program advice into
contiguous addressed memory for the entry-circuit reader. -/
def readLiteralAdvice : Code := .seq literalAdviceSetup (.whileLt 39 35 literalAdviceBit)

end RoutingISA

end BorderVNP
end Computability
end OAI
