import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Public addresses used by the signed and operand pitches of the initial machine -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSIMDLookup
/-- The first ordinary phase consumes the physically transposed seven-field planes. All
three possible input ports get `N` chunk arguments. The unique initial node is slot zero. -/
def issuedFloor (base vertices H G M operandM d N : ℕ) :=
  let rows:=H*chunks G M
  let operandRows:=H*chunks G operandM
  let args:=2^d*chunks G operandM
  base+(2^(Nat.clog 2 (vertices*(2*3)+1))+2*2^(Nat.clog 2 (((2*256)*H)*chunks G M)))+
    ((2*256)*H)*chunks G M+vertices*(3*2)+(vertices*3)+2^(Nat.clog 2 args)+2^(Nat.clog 2 args)+
    (7*(3*N))*(2^d*operandRows)+2^Nat.clog 2 (operandRows+1)+(3+8)*2^Nat.clog 2 (max H (max (H*3) rows))

def seededFloor (base vertices H G M operandM d N : ℕ) :=
  issuedFloor base vertices H G M operandM d N+(2*2^d)*(H*chunks G operandM)+2^Nat.clog 2 (H*chunks G operandM+1)

end Hierarchy.DescentDatedSeedStartup

end OAI
