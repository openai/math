import OAI.Hierarchy.DescentTerminalEpochBits
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Address interval for the shared epoch validity lookup -/
namespace Hierarchy
namespace DescentPackedProfileValidity
def bankShift (C grain q : ℕ) := q*2^(DescentTerminalEpochBits.width C*grain)
def tariff (C grain : ℕ) := bankShift C grain (grain+1)
end DescentPackedProfileValidity

namespace DescentPackedProfileInstall
open DescentPackedProfileValidity ProtocolRAM
def shifts (lo grain : ℕ) : Bank:=⟨lo,Nat.clog 2 (grain+1)⟩
def dict (lo C grain : ℕ) : Bank:=⟨lo+(shifts lo grain).size,Nat.clog 2 (tariff C grain)⟩
def end_ (lo C grain : ℕ) := (dict lo C grain).base+(dict lo C grain).size
end DescentPackedProfileInstall
end Hierarchy

end OAI
