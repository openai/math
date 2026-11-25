import OAI.Hierarchy.DescentSeedNarrowTokens
import OAI.Hierarchy.DescentSeedTokenColumns

namespace OAI
/-! # The address range and output banks of the seed token transposition -/
namespace Hierarchy.DescentSeedTokenTransposition
open DescentSIMDLookup ProtocolRAM
noncomputable section
variable (base O H G X a A M : ℕ)
abbrev cut := Narrow.cut base O G X a A M
local notation "splitAt" => cut base O G X a A M
local notation "length_" => H*chunks G M

def out := DescentSeedTokenColumns.out splitAt a M H G
def endAddress :=out base O H G X a A M+X*length_+2^Nat.clog 2 length_
def page (x : Fin X) := DescentSeedTokenColumns.page splitAt a M H G x.val

end
end Hierarchy.DescentSeedTokenTransposition

end OAI
