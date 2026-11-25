import OAI.Computability.BorderVNP.CubeISALocalRowScan
import OAI.Computability.BorderVNP.CubeISADeclaredRowFrame
import OAI.Computability.BorderVNP.CubeISAOwnedRowSetupPacket

/-! # Native per-role verification of the cube declaration

The row is addressed by its two sorted symbols, while its raw subtotal is
recomputed from zero for each owner role. Eight native words after the entire
packet bank describe the tallier and the next words hold its decoded digits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open BorderVNP.Cube BorderVNP.Cube.Tally Constants

/-- Keep the outgoing vertex cursor and the two actual singleton radix powers
before converting those powers to the strict packet-loop dimensions. -/
def snapshot : Code := .block [.copy 61 7,.copy 6 11,.copy 7 12]

/-- Store one metadata field and advance the descriptor cursor. -/
def push (src : Reg) : Code := .block [.store 51 src,.binary .add 51 51 1]

/-- Append a fixed-template natural to the actual descriptor. -/
def pushLiteral (value : ℕ) : Code := .seq (literal (digits value)) (push 58)

/-- Derive the descriptor address from the sparse packet-trial allocation and
write the first two fields from the fixed selector parameters. -/
def beginHeader : Code := .block [.binary .mul 50 19 11,.binary .mul 50 50 16,.binary .add 50 17 50,
  .copy 51 50,push 8,push 9]

/-- Materialize the complete packet descriptor and the digit scratch pointer.
The raw row always occupies the first dimension words at H[0]. -/
def metadata (n h s : ℕ) : Code := .block [beginHeader,pushLiteral (Fintype.card (Edge (n+1))),
  CubeLengths.field 9 0,push 9,.binary .add 53 5 1,push 53,
  .constant 53 8,.binary .add 53 50 53,push 53,pushLiteral h,pushLiteral s,.copy 8 50]

/-- Read H[1] and derive its actual row-major address. Install the coordinate
count and the raw row for clearing before the selected-role subtotal traversal. -/
def rowAddress : Code := .block [CubeLengths.field 59 1,.binary .mul 53 14 10,.binary .add 53 53 15,
  .binary .add 57 5 1,.binary .mul 53 53 57,.binary .add 59 59 53,.copy 56 0,.copy 58 9]

/-- Read the scalar shape, retain its native radix powers and install packet parameters. -/
def prime (n b h K s : ℕ) : Code := .block [OwnedRowSetup.single,snapshot,OwnedRowSetup.packetRadices,
  OwnedRowSetup.parameters n b h K s]

/-- Install all shape, packet, scalar, metadata and row address registers. -/
def setup (n b h K s : ℕ) : Code := .seq (prime n b h K s) (.seq (metadata n h s) rowAddress)

/-- Prepare the direct guarded comparison and restore the caller's vertex cursor. -/
def finish : Code := .block [.copy 7 61,.copy 56 0,.binary .add 57 5 1,.copy 58 9,.copy 60 1]

/-- Strict row verifier for an already assembled incident packet bank. The two
singleton orientations are followed by restoring the ordered symbol registers. -/
def strictChecked (n b h K s : ℕ) : Code :=
  .seq (setup n b h K s) (.seq clear (.seq (DeclaredRow.strict n)
    (.seq SingleTally.swap (.seq finish compare))))

/-- Diagonal row verifier for one scalar orientation of an incident symbol. -/
def diagonalChecked (n b h K s : ℕ) : Code :=
  .seq (setup n b h K s) (.seq clear (.seq (SingleTally.oriented n) (.seq finish compare)))

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
