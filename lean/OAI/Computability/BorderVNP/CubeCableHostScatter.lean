import OAI.Computability.BorderVNP.RoutingISATableState

/-! # The per-bit host scatter of a packed crossing cable -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Cached descriptor of one cable at one owned endpoint and its bank layout. -/
structure BitFields where
  /-- Width of this cable. -/
  width : ℕ
  /-- Directed bin index. -/
  key : ℕ
  /-- First physical ordinal of this cable in its bin. -/
  start : ℕ
  /-- Zero for a singleton bin, nonzero for a packet bin. -/
  kind : ℕ
  /-- First packet number of this oriented bin. -/
  first : ℕ
  /-- Cube vertex at this endpoint. -/
  vertex : ℕ
  /-- Zero or one for the selected port at this vertex. -/
  side : ℕ
  /-- First destination bit of this cable's incident port. -/
  dest : ℕ
  /-- Base of the singleton banks. -/
  singletonBase : ℕ
  /-- Base of the packet banks. -/
  packetBase : ℕ
  /-- Number of blocks in each bin. -/
  blocks : ℕ
  /-- Number of bits in one block. -/
  bc : ℕ
  /-- Width of one packet bank. -/
  bankWidth : ℕ
  /-- Size of the selector prefix of one packet bank. -/
  selectorWidth : ℕ

/-- Decode the actual cached words of the native row-stage ABI. -/
def BitFields.read (r : Reg → ℕ) : BitFields :=
  ⟨r 15,r 16,r 17,r 18,r 19,r 20,r 21,r 22,r 12,r 24,r 25,r 26,r 27,r 28⟩

/-- The two physical banks use the ordinal within the entire directed bin. -/
def BitFields.source (f : BitFields) (j : ℕ) : ℕ :=
  let ord := f.start+j
  if f.kind = 0 then f.singletonBase + f.key*(f.blocks*f.bc) + ord
  else f.packetBase + (f.first + ord/f.bc)*f.bankWidth + f.selectorWidth +
    (2*f.vertex+f.side)*f.bc + ord%f.bc

/-- The cached row fields and the three arithmetic constants have been loaded. -/
def BitFields.Ready (f : BitFields) (z : NatState) : Prop :=
  z.reg 0 = 0 ∧ z.reg 1 = 1 ∧ z.reg 2 = 2 ∧ read z.reg = f

/-- Physical word bounds needed by one cable's bit traversal. -/
structure BitFields.Fits (f : BitFields) (w : ℕ) : Prop where
  /-- The last actual within-bin ordinal fits. -/
  ordinals : f.start+f.width ≤ 2^w
  /-- The contiguous destination range fits. -/
  destination : f.dest+f.width ≤ 2^w
  /-- The singleton bin stride fits when the singleton branch runs. -/
  stride : f.kind = 0 → f.blocks*f.bc < 2^w
  /-- Every divisor on an executed packet branch is nonzero. -/
  divisor : f.kind ≠ 0 → 0 < f.width → 0 < f.bc
  /-- Every packet-number computation fits. -/
  packet : ∀ j < f.width, f.kind ≠ 0 → f.first+(f.start+j)/f.bc < 2^w
  /-- The doubled vertex and port index fit. -/
  port : f.kind ≠ 0 → 0 < f.width → 2*f.vertex+f.side < 2^w
  /-- Each actual bit source address fits. -/
  source : ∀ j < f.width, f.source j < 2^w

/-- All row and configuration registers, including the outer cable cursor, survive. -/
def Kept (r t : Reg → ℕ) := ∀ i : Reg, i.val < 30 → i ≠ 23 → t i = r i

/-- Contents after exactly the first `k` bits have been copied. -/
def BitFields.image (f : BitFields) (before : ℕ → ℕ) (k a : ℕ) :=
  if f.dest ≤ a ∧ a < f.dest+k then before (f.source (a-f.dest)) else before a

/-- Computing one singleton bit address uses the full directed-bin capacity. -/
def singletonSource : Code := .block [.binary .mul 31 25 26,.binary .mul 31 16 31,
  .binary .add 31 12 31,.binary .add 31 31 30]

/-- Compute the packet number, the endpoint's port and its lane within the block. -/
def packetSource : Code := .block [.binary .div 31 30 26,.binary .add 31 19 31,
  .binary .mul 31 31 27,.binary .add 31 24 31,.binary .add 31 31 28,
  .binary .mul 32 2 20,.binary .add 32 32 21,.binary .mul 32 32 26,
  .binary .add 31 31 32,.binary .mod 32 30 26,.binary .add 31 31 32]

/-- Read one source bit and write it to its cable-relative port position. -/
def copyBit : Code := .block [.binary .add 30 17 23,.ifEq 18 0 singletonSource packetSource,
  .load 32 31,.binary .add 33 22 23,.store 33 32]

/-- Advance only the within-cable cursor after the source read and destination store. -/
def scatterStep : Code := copyBit.seq (.binary .add 23 23 1)

/-- Scatter all real bits of this owned cable; zero-width cables only pay setup and the guard. -/
def scatterBits : Code := .seq (.copy 23 0) (.whileLt 23 15 scatterStep)

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
