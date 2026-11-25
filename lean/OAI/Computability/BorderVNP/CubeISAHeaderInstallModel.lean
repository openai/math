import OAI.Computability.BorderVNP.RoutingISATableSetup
import OAI.Computability.BorderVNP.RoutingISAAddressProof
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log

/-! # Static header for the dense cube declarations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeHeaderInstall

/-- The scalar values supplied by the primary routing frame. -/
structure Inputs where
  /-- Address of the first secondary word. -/
  header : ℕ
  /-- Alphabet size. -/
  d : ℕ
  /-- Number of directions. -/
  a : ℕ
  /-- Number of packet blocks. -/
  blocks : ℕ
  /-- Length of the geometry profile preceding the declaration. -/
  profile : ℕ
  /-- Largest legal declaration. -/
  cap : ℕ

/-- Primary-frame words read before any secondary store. -/
structure Inputs.Loaded (l : Inputs) (pub : Arg → ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Secondary header pointer. -/
  header : frameField pub mem 63 = l.header
  /-- Alphabet size. -/
  d : frameField pub mem 59 = l.d
  /-- Direction count. -/
  a : frameField pub mem 60 = l.a
  /-- Packet block count. -/
  blocks : frameField pub mem 109 = l.blocks
  /-- Geometry profile length. -/
  profile : frameField pub mem 110 = l.profile
  /-- Declaration cap. -/
  cap : frameField pub mem 111 = l.cap

/-- Number of words in one dense array, including the zero lower triangle. -/
def Inputs.entries (l : Inputs) : ℕ := l.d*l.d*l.a

/-- First packet-bank address after both dense arrays and the directional totals. -/
def Inputs.packetBase (l : Inputs) : ℕ := l.header+13+2*l.entries+l.a

/-- Number of selector bits per complete packet row. -/
def Inputs.volume (l : Inputs) (n bits : ℕ) : ℕ := 2*l.blocks*(l.d.choose 2)^n*bits

/-- Static contents of the secondary header. Field five is the initial coordinate. -/
def Inputs.value (l : Inputs) (n bits : ℕ) : ℕ → ℕ
  | 0 => l.header+13
  | 1 => l.header+13+l.entries
  | 2 => l.entries
  | 3 => l.header+13+2*l.entries
  | 4 => l.a
  | 5 => 0
  | 6 => l.volume n bits
  | 7 => l.blocks
  | 8 => l.packetBase
  | 9 => l.profile
  | 10 => Nat.clog 2 l.a
  | 11 => Nat.clog 2 (l.cap+1)
  | 12 => l.cap
  | _ => 0

/-- Static installation replaces exactly the thirteen secondary words. -/
def Inputs.image (l : Inputs) (n bits : ℕ) (old : ℕ → ℕ) (addr : ℕ) : ℕ :=
  if l.header ≤ addr ∧ addr < l.header+13 then l.value n bits (addr-l.header) else old addr

/-- Word bounds for the concrete installation instructions, including intermediate products. -/
structure Inputs.Fits (l : Inputs) (w n bits frame : ℕ) : Prop where
  /-- Last primary-frame read. -/
  primary : frame+111 < 2^w
  /-- First packet-bank address, stored as a word. -/
  bank : l.packetBase < 2^w
  /-- Symbol-pair square used to compute the unordered-pair count. -/
  square : l.d*l.d < 2^w
  /-- All partial oriented packet counts fit, including the zero-digit prefix. -/
  packets : 2*l.blocks*max 1 ((l.d.choose 2)^n) < 2^w
  /-- Complete row length in selector bits. -/
  volume : l.volume n bits < 2^w
  /-- Exclusive bound for the row decoder. -/
  cap : l.cap+1 < 2^w

end RoutingISA.CubeHeaderInstall

end BorderVNP
end Computability
end OAI
