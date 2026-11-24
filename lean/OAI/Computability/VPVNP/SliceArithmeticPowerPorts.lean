import OAI.Computability.VPVNP.SliceArithmeticMultiplyCall
import OAI.Computability.VPVNP.SliceArithmeticPower

/-! # Ports of the binary powering and inversion control -/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.InverseCall

open RAMTape

set_option backward.isDefEq.respectTransparency false in
/-- Extra inversion ports for the saved base and exponent, the live bit stream, the zero-test
flag, and temporary stacks. -/
inductive Extra where
  | base | exponent | bits | flag | scratch | temp
  deriving DecidableEq, Fintype

/-- The multiplier's full port bank extended with the ports for binary powering and inversion. -/
abbrev Port := MultiplyCall.Port ⊕ Extra

/-- Caller-visible scalar advice and operands, together with the exponent
scan's remaining bits and the temporary zero-test flag. -/
def frame (p e w : ℕ) (cb base exponent bits acc flag : List Bool) : Stacks Port :=
  Sum.elim (MultiplyCall.clean (MultiplyCall.external p e w cb [] acc)) fun
    | .base => base
    | .exponent => exponent
    | .bits => bits
    | .flag => flag
    | .scratch | .temp => []

end SliceArithmetic.InverseCall

end VPVNP
end Computability
end OAI
