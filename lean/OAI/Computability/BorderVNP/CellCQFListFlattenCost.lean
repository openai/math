import OAI.Computability.BorderVNP.CellCQFPolynomialDegree
import OAI.Computability.QuantumFactoring.BitStackListWords
import OAI.Computability.QuantumFactoring.BitStackListFlatten

/-! # Clocks of the physical word and list concatenation procedures

The measured clocks of the installed bit-stack programs depend on the actual encoded
input size. Their fixed clock coefficients are evaluated at one.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

/-- The installed word join has a quadratic clock in its list-coded input. -/
theorem listJoinWords_degree : listJoinWords.bound.natDegree ≤ 2 := by cqf_degree

/-- The physical transitions to flatten the supplied list of bit strings. -/
theorem cost_listJoinWords (xs : List (List Bool)) :
    listJoinWords.cost xs ≤ listJoinWords.bound.eval 1 * ((listCode id xs).length+1)^2 :=
  listJoinWords.cost_pow xs listJoinWords_degree

/-- The nested list-code concatenator has clock degree at most five, for any element
encoding and its designated default. -/
theorem listFlatten_degree {α : Type} (ea : α → List Bool) (d : α) :
    (listFlatten ea d).bound.natDegree ≤ 5 := by cqf_degree

/-- The actual transitions on a given nested list are bounded in its own encoded length. -/
theorem cost_listFlatten {α : Type} (ea : α → List Bool) (d : α) (xss : List (List α)) :
    (listFlatten ea d).cost xss ≤ (listFlatten ea d).bound.eval 1 * ((listCode (listCode ea) xss).length+1)^5 :=
  (listFlatten ea d).cost_pow xss (listFlatten_degree ea d)

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  listJoinWords_degree
  cost_listJoinWords
  listFlatten_degree
  cost_listFlatten)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
