import OAI.Computability.BorderVNP.CubeISAOwnedRows
import OAI.Computability.BorderVNP.RoutingISATableSetup
import OAI.Computability.BorderVNP.RoutingISAAddressProof

/-! # Addressed inputs of the physical cube row iterators -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedRowSetup

open VPVNP.BurstRAM Cube.Physical.Owned

/-- Primary and secondary scalars needed by the row setup code. -/
structure Layout where
  /-- Symbol alphabet. -/
  d : ℕ
  /-- Number of physical blocks. -/
  blocks : ℕ
  /-- Scalar block width. -/
  bc : ℕ
  /-- Base of the table of alphabet powers. -/
  power : ℕ
  /-- Secondary header base. -/
  header : ℕ
  /-- Packet bank base. -/
  bank : ℕ

/-- Real frame and table words read by the native setup. -/
structure Layout.Loaded (l : Layout) (n : ℕ) (pub : Arg → ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Alphabet. -/
  d : frameField pub mem 59 = l.d
  /-- Direction count. -/
  axes : frameField pub mem 60 = n+1
  /-- Scalar width. -/
  bc : frameField pub mem 61 = l.bc
  /-- Power table pointer. -/
  power : frameField pub mem 62 = l.power
  /-- Header pointer. -/
  header : frameField pub mem 63 = l.header
  /-- Physical blocks. -/
  blocks : mem (l.header+7) = l.blocks
  /-- Actual bank pointer. -/
  bank : mem (l.header+8) = l.bank
  /-- Every table entry used by a valid axis, including the last. -/
  powers : ∀ j ≤ n, mem (l.power+j) = l.d^j

/-- Address and arithmetic bounds for the mixed-radix row loop setup. -/
structure Layout.Fits (l : Layout) (w n frame : ℕ) : Prop where
  /-- Last primary-frame address read. -/
  primary : frame+63 < 2^w
  /-- Last secondary field read. -/
  header : l.header+8 < 2^w
  /-- Last addressed power. -/
  powers : l.power+n < 2^w
  /-- Symbol square radix. -/
  square : l.d*l.d < 2^w
  /-- Whole singleton trial bound. -/
  endpoints : l.d^n*l.d^n < 2^w
  /-- Bits in the oriented scalar-block rectangle. -/
  single : l.blocks*l.bc < 2^w

/-- Calling registers kept across each row setup. -/
abbrev Held (j : Reg) : Prop := j ∈ ([0,1,3,4,7,14,15,22,23,36,37] : List Reg)

/-- Native setup common to the packet and singleton iterators. It also computes the
singleton trial count and the per-orientation number of scalar bits. -/
def single : Code := .block [readFrame 10 62 63 59,readFrame 5 62 63 60,.binary .sub 5 5 1,
  readFrame 51 62 63 63,.constant 54 7,.binary .add 54 51 54,.load 13 54,
  .constant 54 8,.binary .add 54 51 54,.load 17 54,readFrame 52 62 63 62,
  .binary .add 53 52 4,.load 12 53,.binary .add 53 52 5,.load 11 53,
  .binary .mul 19 11 11,readFrame 55 62 63 61,.binary .mul 21 13 55,
  .copy 18 0,.constant 2 2]

/-- Read-only register result before selecting an orientation or a packet stride. -/
structure Prepared (l : Layout) (n i : ℕ) (reg : Reg → ℕ) : Prop where
  /-- Orientation radix. -/
  two : reg 2 = 2
  /-- Number of other coordinates. -/
  dim : reg 5 = n
  /-- Symbol radix. -/
  radix : reg 10 = l.d
  /-- Number of other-coordinate labels. -/
  labels : reg 11 = l.d^n
  /-- Grouping coordinate place. -/
  place : reg 12 = l.d^i
  /-- Packet blocks. -/
  blocks : reg 13 = l.blocks
  /-- Packet-bank base. -/
  bank : reg 17 = l.bank
  /-- Initial trial cursor. -/
  cursor : reg 18 = 0
  /-- Ordered endpoint label trial count. -/
  trials : reg 19 = singlePairTrials n l.d
  /-- Bits at one singleton orientation. -/
  bits : reg 21 = l.blocks*l.bc

end RoutingISA.OwnedRowSetup

end BorderVNP
end Computability
end OAI
