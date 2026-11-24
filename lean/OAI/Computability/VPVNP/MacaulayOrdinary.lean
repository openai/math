import OAI.Computability.VPVNP.MacaulayBaseAdvice
import OAI.Computability.VPVNP.MacaulaySignedCoefficient
import OAI.Computability.VPVNP.MacaulayPinArm
import OAI.Computability.VPVNP.MacaulayEntryExecution

/-! # The fixed scalar-entry program for the augmented Macaulay matrix

All three arms run literal finite stack programs. The original row evaluates
two signed counts, the affine row consults the pin table, and the appended
row compares its powered source monomial with the column. Matrix dimensions,
scalar field data, and coefficient circuits enter only through the caller's
stack bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead

open RAMTape MacaulayRowDispatch

set_option synthInstance.maxSize 3000 in
/-- The three scalar-entry routines. Equation rows use signed counts, affine rows use pin
advice, and powered rows compare exponent vectors. -/
def ordinaryArms : Kind → FiniteRoutine (Port BaseAdvice.RawPort)
  | .equation => Arms.phase false (JointScalar.Leaf.machine.onPorts (SignedLeaf.ports Function.Embedding.inl))
  | .affine => Arms.phase false (Arms.Pin.machine Function.Embedding.inr)
  | .power => Arms.phase true (Arms.emit true)

set_option synthInstance.maxSize 3000 in
/-- Fixed row decoder and dispatch program with the equation, affine and powered scalar-entry
arms installed. -/
def ordinaryReader : FiniteRoutine (Port BaseAdvice.RawPort) := reader ordinaryArms

end RankQuery.Stack.MacaulayRead

end VPVNP
end Computability
end OAI
