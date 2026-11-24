import OAI.Computability.VPVNP.TallyPrograms
import OAI.Computability.VPVNP.TallyConstantRoutines

/-! # Constant writes and clearing for packaged tally programs -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Tally.Program

variable {K : Type} [DecidableEq K]

/-- Adds the fixed constant to one unary register in one push per mark followed by a return. -/
@[simps eval work ready]
def addConst (k : K) (a : ℕ) : Program K where
  Q := Fin (a+1)
  code := addConstant k a
  eval s := Function.update s k (s k+a)
  work _ := a+1
  ready _ := True
  spec s _ := addConstant_runs k a s

/-- Empties one unary register in twice its initial value plus one stack instructions. -/
@[simps eval work ready]
def clear (k : K) : Program K where
  Q := _
  code := Tally.clear k
  eval s := Function.update s k 0
  work s := 2*s k+1
  ready _ := True
  spec s _ := clear_runs k s

end RAMTape.Tally.Program

end VPVNP
end Computability
end OAI
