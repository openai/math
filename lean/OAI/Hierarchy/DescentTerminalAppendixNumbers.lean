import OAI.Hierarchy.DescentTerminalBinFormat
import OAI.Hierarchy.DescentTerminalDenseWindow
import OAI.Hierarchy.DescentTerminalPrimitiveSpace

namespace OAI
/-! # Numerical sizes of the original terminal chip and its physical appendix -/
noncomputable section

namespace Hierarchy.DescentTerminalChipBootWords
open DescentTerminalDenseWindow DescentTerminalBinReaddress
open scoped BigOperators Classical
noncomputable section
variable (K W q p codes:ℕ)
local notation "n" => K*W
local notation "d" => q*(W*p)
local notation "R" => 2^d
local notation "M" => Menus q (W*p)
local notation "c" => DescentTerminalBinFormat.controlBits W q
local notation "sw" => sliceWidth W q p

def need (col:Fin 10) : ℕ :=
  match col.val with
  | 0 | 1 | 2 | 3 => n
  | 4=>R | 5=>M | 6=>M*(R*R) | 7=>2^c | 8=>2^c*2^sw | _=>codes+1

def bits (col:Fin 10) := Nat.clog 2 (need K W q p codes col)
def «begin» (col:Fin 10) := ∑f:Fin 10,if f<col then 2^(bits K W q p codes f) else 0
def total := ∑f:Fin 10,2^(bits K W q p codes f)
end
end Hierarchy.DescentTerminalChipBootWords

namespace Hierarchy.DescentTerminalDenseHeader

def profiles (q p : ℕ) := (p+1)^q
end Hierarchy.DescentTerminalDenseHeader

namespace Hierarchy.DescentTerminalDenseHeaderBoot
open DescentTerminalDenseHeader

def strideBits (q p : ℕ) := Nat.clog 2 (profiles q p * (q*p))
def stride (q p : ℕ) := 2^(strideBits q p)
def extent (q p : ℕ) := 4*stride q p
end Hierarchy.DescentTerminalDenseHeaderBoot

namespace Hierarchy.DescentTerminalBoot

def total (K W q piece codes : ℕ) :=
  DescentTerminalChipBootWords.total K W q piece codes + DescentTerminalDenseHeaderBoot.extent q (W*piece)
end Hierarchy.DescentTerminalBoot

namespace Hierarchy.DescentTerminalPaidBoot

def total (K W q piece codes rows : ℕ) :=
  DescentTerminalBoot.total K W q piece codes + DescentTerminalPrimitiveArena.pad rows
end Hierarchy.DescentTerminalPaidBoot

namespace Hierarchy.DescentTerminalPublicIdentity
open DescentTerminalPrimitiveArena

def total (K W q piece codes rows publicRows : ℕ) :=
  DescentTerminalPaidBoot.total K W q piece codes rows+pad publicRows
end Hierarchy.DescentTerminalPublicIdentity

end

end OAI
