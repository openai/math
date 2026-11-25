import OAI.Computability.BorderVNP.DiagonalTallyOperandArray

/-! # Native descriptor and bit-reference expressions for compact cell reports -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyOperandArray

open VPVNP.BurstRAM RoutingISA

/-- A fixed gadget-count field or all copies of the marked unary rows in one bottom bundle. -/
inductive Kind | count | unary deriving DecidableEq

/-- Registers kept live while a count block or one decoded bundle is being emitted. -/
structure Frame where
  /-- Number of parameter coordinates. -/
  parameters : ℕ
  /-- Number of fixed gadget coordinates. -/
  gadgets : ℕ
  /-- Number of bits per gadget count. -/
  width : ℕ
  /-- Address of a zero word in ordinary memory. -/
  zeroAddr : ℕ
  /-- Start of the packed sidecar including its count. -/
  side : ℕ
  /-- Number of marked positions in that original site. -/
  marked : ℕ
  /-- Number of copies in the current bundle. -/
  copies : ℕ
  /-- Absolute first report-bit address for this stage. -/
  external : ℕ
  /-- First output descriptor word. -/
  descriptors : ℕ
  /-- First output reference word. -/
  refs : ℕ
  /-- Previously emitted operand count. -/
  prior : ℕ

/-- Values of the stable caller registers. -/
structure Frame.Loaded (f : Frame) (r : Reg → ℕ) : Prop where
  /-- Parameter-coordinate offset. -/
  parameters : r 9=f.parameters
  /-- Fixed gadget count. -/
  gadgets : r 10=f.gadgets
  /-- Bit width of each gadget count. -/
  width : r 11=f.width
  /-- Physical zero-word address. -/
  zeroAddr : r 12=f.zeroAddr
  /-- Decoded metadata base. -/
  side : r 20=f.side
  /-- Current bundle multiplicity. -/
  copies : r 21=f.copies
  /-- Current absolute report cursor. -/
  external : r 22=f.external
  /-- Current five-word descriptor cursor. -/
  descriptors : r 30=f.descriptors
  /-- Current reference cursor. -/
  refs : r 31=f.refs
  /-- Number of previously appended operands. -/
  prior : r 32=f.prior

/-- Each selected unary copy has one reference; each count has a full bit field. -/
def Frame.nrefs (f : Frame) : Kind → ℕ
  | .count => f.gadgets*f.width
  | .unary => f.marked*f.copies

/-- Number of five-word descriptors actually appended. -/
def Frame.nrows (f : Frame) : Kind → ℕ
  | .count => f.gadgets
  | .unary => f.marked*f.copies

/-- Sufficient physical word headroom for this block's dynamic cursors and indirect addresses. -/
structure Frame.Fits (f : Frame) (k : Kind) (w : ℕ) : Prop where
  /-- The small immediate five fits. -/
  small : 5<2^w
  /-- Last decoded triple and its end sentinel fit. -/
  sideEnd : f.side+1+3*f.marked<2^w
  /-- The entire external report interval fits. -/
  externalEnd : f.external+f.nrefs k<2^w
  /-- The reference array fits. -/
  refsEnd : f.refs+f.nrefs k<2^w
  /-- The descriptor array fits. -/
  descEnd : f.descriptors+5*f.nrows k<2^w
  /-- All gadget coordinates fit. -/
  coordinateEnd : f.parameters+f.gadgets<2^w
  /-- The final operand count fits. -/
  countEnd : f.prior+f.nrows k<2^w

/-- Word at the given index of the bit-reference vector. Count bits are physically
little-endian and are enumerated most-significant first by the gather operation. -/
def Frame.refValue (f : Frame) (k : Kind) (i : ℕ) : ℕ :=
  match k with
  | .unary => f.external+i
  | .count => f.external+(i-i%f.width+(f.width-1-i%f.width))

/-- The five ordinary descriptor fields at the given flattened index. -/
def Frame.field (f : Frame) (k : Kind) (i : ℕ) : ℕ :=
  let g := i/5
  let j := i%5
  match k with
  | .unary =>
    let p := f.side+3*(g/f.copies)+1
    if j=0 then 0 else if j=1 then p else if j=2 then f.refs+g
    else if j=3 then f.refs+g+1 else p+1
  | .count =>
    let a := f.refs+g*f.width
    if j=0 then f.parameters+g else if j=1 then f.zeroAddr else if j=2 then a
    else if j=3 then a+f.width else f.zeroAddr

/-- Compile one bit-reference expression, using the actual physical index and live cursors. -/
def refExpr : Kind → Code
  | .unary => .binary .add 50 22 40
  | .count => .block [.binary .mod 44 40 11,.binary .sub 45 40 44,.binary .sub 46 11 43,
      .binary .sub 46 46 44,.binary .add 45 45 46,.binary .add 50 22 45]

/-- Decode the flattened field index once, then read the relevant static or dynamic operands. -/
def fieldExpr (k : Kind) : Code :=
  let index := Code.block [.constant 46 5,.binary .div 44 40 46,.binary .mod 45 40 46,
    .constant 47 0,.constant 48 2,.constant 49 3]
  let assign (a b c d e : Code) := Code.ifEq 45 47 a
    (.ifEq 45 43 b (.ifEq 45 48 c (.ifEq 45 49 d e)))
  .seq index (match k with
  | .unary => .block [.binary .div 51 44 21,.binary .mul 51 49 51,.binary .add 51 20 51,
      .binary .add 51 51 43,.binary .add 52 31 44,
      assign (.copy 50 47) (.copy 50 51) (.copy 50 52) (.binary .add 50 52 43) (.binary .add 50 51 43)]
  | .count => .block [.binary .mul 51 44 11,.binary .add 52 31 51,
      assign (.binary .add 50 9 44) (.copy 50 12) (.copy 50 52) (.binary .add 50 52 11) (.copy 50 12)])

end DiagonalTallyOperandArray

end BorderVNP
end Computability
end OAI
