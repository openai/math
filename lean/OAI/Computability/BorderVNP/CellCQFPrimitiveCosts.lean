import OAI.Computability.BorderVNP.CellCQFPolynomialDegree
import OAI.Computability.QuantumFactoring.BitStackListOps
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength
import OAI.Computability.QuantumFactoring.BitStackBoundedUnary
import OAI.Computability.QuantumFactoring.BitStackOptions
import OAI.Computability.QuantumFactoring.NativeAIGAddWrapper

/-! # Certified clock degrees of scalar and list primitives for the cell printer

These exponents are upper bounds obtained from the installed stack programs. The coefficient
is the sum of the coefficients of the corresponding certified polynomial clock. Input lengths
are those of the actual words supplied to each primitive.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {α : Type}

set_option maxRecDepth 40000
set_option maxHeartbeats 6000000

/-- Actual clean-run time for `binaryAdd` at degree 8 of its input encoding length. -/
theorem cost_binaryAdd (x : ℕ × ℕ) :
    binaryAdd.cost x ≤ binaryAdd.bound.eval 1*((prodCode Nat.bits Nat.bits x).length+1)^8 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `binarySub` at degree 8 of its input encoding length. -/
theorem cost_binarySub (x : ℕ × ℕ) :
    binarySub.cost x ≤ binarySub.bound.eval 1*((prodCode Nat.bits Nat.bits x).length+1)^8 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `binaryMul` at degree 9 of its input encoding length. -/
theorem cost_binaryMul (x : ℕ × ℕ) :
    binaryMul.cost x ≤ binaryMul.bound.eval 1*((prodCode Nat.bits Nat.bits x).length+1)^9 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `binaryEq` at degree 16 of its input encoding length. -/
theorem cost_binaryEq (x : ℕ × ℕ) :
    binaryEq.cost x ≤ binaryEq.bound.eval 1*((prodCode Nat.bits Nat.bits x).length+1)^16 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `binaryLe` at degree 4 of its input encoding length. -/
theorem cost_binaryLe (x : ℕ × ℕ) :
    binaryLe.cost x ≤ binaryLe.bound.eval 1*((prodCode Nat.bits Nat.bits x).length+1)^4 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `binaryLt` at degree 4 of its input encoding length. -/
theorem cost_binaryLt (x : ℕ × ℕ) :
    binaryLt.cost x ≤ binaryLt.bound.eval 1*((prodCode Nat.bits Nat.bits x).length+1)^4 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `unaryToBits` at degree 2 of its input encoding length. -/
theorem cost_unaryToBits (x : ℕ) :
    unaryToBits.cost x ≤ unaryToBits.bound.eval 1*((unaryCode x).length+1)^2 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `clippedUnary` at degree 9 of its input encoding length. -/
theorem cost_clippedUnary (x : ℕ × ℕ) :
    clippedUnary.cost x ≤ clippedUnary.bound.eval 1*((prodCode unaryCode Nat.bits x).length+1)^9 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `listHead` at degree 1 of its input encoding length. -/
theorem cost_listHead (ea : α → List Bool) (d : α) (x : List α) :
    (listHead ea d).cost x ≤ (listHead ea d).bound.eval 1*((listCode ea x).length+1)^1 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `listTail` at degree 1 of its input encoding length. -/
theorem cost_listTail (ea : α → List Bool) (x : List α) :
    (listTail ea).cost x ≤ (listTail ea).bound.eval 1*((listCode ea x).length+1)^1 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `listGet` at degree 9 of its input encoding length. -/
theorem cost_listGet (ea : α → List Bool) (d : α) (x : ℕ × List α) :
    (listGet ea d).cost x ≤ (listGet ea d).bound.eval 1*((prodCode Nat.bits (listCode ea) x).length+1)^9 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `listDrop` at degree 9 of its input encoding length. -/
theorem cost_listDrop (ea : α → List Bool) (x : ℕ × List α) :
    (listDrop ea).cost x ≤ (listDrop ea).bound.eval 1*((prodCode Nat.bits (listCode ea) x).length+1)^9 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `listLength` at degree 4 of its input encoding length. -/
theorem cost_listLength (ea : α → List Bool) (d : α) (x : List α) :
    (listLength ea d).cost x ≤ (listLength ea d).bound.eval 1*((listCode ea x).length+1)^4 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `listReverse` at degree 2 of its input encoding length. -/
theorem cost_listReverse (ea : α → List Bool) (d : α) (x : List α) :
    (listReverse ea d).cost x ≤ (listReverse ea d).bound.eval 1*((listCode ea x).length+1)^2 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `listRevAppend` at degree 2 of its input encoding length. -/
theorem cost_listRevAppend (ea : α → List Bool) (d : α) (x : List α × List α) :
    (listRevAppend ea d).cost x ≤ (listRevAppend ea d).bound.eval 1*((prodCode (listCode ea) (listCode ea) x).length+1)^2 :=
  cost_pow _ _ (by cqf_degree)

/-- Actual clean-run time for `listUnaryLength` at degree 2 of its input encoding length. -/
theorem cost_listUnaryLength (ea : α → List Bool) (d : α) (x : List α) :
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength ea d).cost x ≤ (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength ea d).bound.eval 1*((listCode ea x).length+1)^2 :=
  cost_pow _ _ (by cqf_degree)

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  cost_binaryAdd
  cost_binarySub
  cost_binaryMul
  cost_binaryEq
  cost_binaryLe
  cost_binaryLt
  cost_unaryToBits
  cost_clippedUnary
  cost_listHead
  cost_listTail
  cost_listGet
  cost_listDrop
  cost_listLength
  cost_listReverse
  cost_listRevAppend
  cost_listUnaryLength)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
