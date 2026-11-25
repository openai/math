import OAI.Computability.BorderVNP.CellCQFMeter
import OAI.Computability.BorderVNP.CellCQFPairCost

/-! # Charging a quoted pair at its actual component words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {A B C : Type} {ea : A → List Bool} {eb : B → List Bool} {ec : C → List Bool}
variable {f : A → B} {g : A → C}

/-- Pairing subroutine results only changes the constant in their summed charge. -/
theorem meter_pair (p : Procedure ea eb f) (q : Procedure ea ec g) (a : A) :
    (p.pair q).meter a ≤ 2*10^9*(p.meter a + q.meter a) := by
  have h := cost_pair p q a
  simp only [meter,prodCode,pairBits_length]
  omega

/-- The code of a pair fits within twice the two source charges. -/
theorem pair_words_le (p : Procedure ea eb f) (q : Procedure ea ec g) (a : A) :
    (prodCode eb ec (f a,g a)).length+1 ≤ 2*(p.meter a+q.meter a) := by
  simp only [prodCode,pairBits_length,meter]
  omega

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  meter_pair
  pair_words_le)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
