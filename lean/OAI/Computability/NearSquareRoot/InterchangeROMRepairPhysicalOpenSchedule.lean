import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalBounded
import OAI.Computability.NearSquareRoot.InterchangeROMWordLedger

/-! # The actual recursive requests of a sequential, parked repair command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom InterchangeROM
  InterchangeSpace Space

/-- Requests concatenate in tape execution order. Each leaf reads the current
active suffix, after the preceding leaves have transformed it. -/
def docket {E Q : Type} (leaf : Leaf → List E → List E) (emit : Leaf → List E → List Q) :
    List Step → List E → List Q
  | [], _ => []
  | s::ss, xs => emit s.2 (xs.drop s.1) ++ docket leaf emit ss (applyStep leaf xs s)

def withChildren {Q : Type} (a : Allowance) (q : List Q) (time data depth : Q → ℕ) : Allowance :=
  ⟨a.time+(q.map time).sum,a.cap+childPeak data q,a.depth+childPeak depth q⟩

end InterchangeROMRepair.Physical

end NearSquareRoot
end Computability
end OAI
