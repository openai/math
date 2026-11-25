import OAI.Optimization.LinearProgramming.Lattice.BitMatrixProcedures
import OAI.Optimization.LinearProgramming.Compression.DetCircuit

/-! A fixed bit-stack procedure for one division-free determinant pass on signed binary matrices. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open scoped BigOperators

abbrev MatrixPair := IntMatrix × IntMatrix
def matrixPairCode := prodCode intMatrixCode intMatrixCode

def birdSum (n i : ℕ) (f : ℕ → ℤ) := ((List.range n).map fun k => if i < k then f k else 0).sum

def birdCell (A F : IntMatrix) (i j : ℕ) : ℤ :=
  -(birdSum A.length i fun k => entryAt F k k) * entryAt A i j +
    birdSum A.length i (fun k => entryAt F i k * entryAt A k j)

def birdStepLists (A F : IntMatrix) : IntMatrix := squareTable A.length (birdCell A F)

def birdUpdate (p : MatrixPair) : MatrixPair := (p.1,birdStepLists p.1 p.2)

private noncomputable def untilSumP {α : Type} (e : α → List Bool) {n i : α → ℕ}
    (nP : Procedure e unaryCode n) (iP : Procedure e Nat.bits i) {f : α → ℕ → ℤ}
    (fP : Procedure (prodCode unaryCode e) intCode (fun x => f x.2 x.1)) :
    Procedure e intCode (fun x => birdSum (n x) (i x) (f x)) := by
  let ce := prodCode unaryCode e
  let ctx := second unaryCode e
  let k := unaryToBits.comp (first unaryCode e)
  let test := binaryLt.comp ((iP.comp ctx).pair k)
  let term := conditional test fP (constant ce intCode (0:ℤ))
  let terms := tabulate (f := fun x : α => fun j => if i x < j then f x j else 0) (0:ℤ)
    (term.congrFun (by intro p; simp))
  exact intListSumP.comp (terms.comp (nP.pair (identity e)))

private noncomputable def birdCellP : Procedure (squareArgCode matrixPairCode) intCode
    (fun p => birdCell p.2.1 p.2.2 p.1.1 p.1.2) := by
  let e := squareArgCode matrixPairCode
  let sub := second unaryCode e
  let k := unaryToBits.comp (first unaryCode e)
  let ij := first (prodCode unaryCode unaryCode) matrixPairCode
  let i := unaryToBits.comp ((first unaryCode unaryCode).comp ij)
  let j := unaryToBits.comp ((second unaryCode unaryCode).comp ij)
  let mats := second (prodCode unaryCode unaryCode) matrixPairCode
  let A := (first intMatrixCode intMatrixCode).comp mats
  let F := (second intMatrixCode intMatrixCode).comp mats
  let size := (OAI.Optimization.LinearProgramming.PriceGame.Learning.GenerationCost.lengthUnaryP intRowCode []).comp A
  let diagTerm := matrixEntryP.comp ((k.pair k).pair (F.comp sub))
  let left := matrixEntryP.comp (((i.comp sub).pair k).pair (F.comp sub))
  let right := matrixEntryP.comp ((k.pair (j.comp sub)).pair (A.comp sub))
  let aij := matrixEntryP.comp ((i.pair j).pair A)
  let diag := untilSumP e size i (f := fun x k => entryAt x.2.2 k k) diagTerm
  let dot := untilSumP e size i (f := fun x k => entryAt x.2.2 x.1.1 k * entryAt x.2.1 k x.1.2)
    (intMul.comp (left.pair right))
  exact intAdd.comp ((intMul.comp ((intNeg.comp diag).pair aij)).pair dot)

noncomputable def birdUpdateP : Procedure matrixPairCode matrixPairCode birdUpdate := by
  let A := first intMatrixCode intMatrixCode
  let size := (OAI.Optimization.LinearProgramming.PriceGame.Learning.GenerationCost.lengthUnaryP intRowCode []).comp A
  exact A.pair (squareTableP matrixPairCode size (f := fun x => birdCell x.1 x.2) birdCellP)

def denseAt (n : ℕ) (A : IntMatrix) : Matrix (Fin n) (Fin n) ℤ := fun i j => entryAt A i.val j.val

private theorem range_sum (n : ℕ) (f : ℕ → ℤ) : ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem birdSum_eq (n : ℕ) (i : Fin n) (f : ℕ → ℤ) :
    birdSum n i.val f = ∑ k ∈ Finset.Ioi i, f k.val := by
  unfold birdSum
  rw [range_sum]
  simp [← Finset.sum_filter,Finset.filter_lt_eq_Ioi]

/-- The list pass agrees entry by entry with the verified algebraic determinant recurrence. -/
theorem denseAt_birdStepLists (A F : IntMatrix) :
    denseAt A.length (birdStepLists A F) = BirdDet.Spec.stepEntry (denseAt A.length A) (denseAt A.length F) := by
  ext i j
  change entryAt (squareTable A.length (birdCell A F)) i.val j.val = _
  rw [squareTable_entryAt, BirdDet.Spec.stepEntry_eq]
  simp only [birdCell,birdSum_eq,denseAt,Matrix.of_apply]

theorem birdStepLists_length (A F : IntMatrix) : (birdStepLists A F).length = A.length :=
  squareTable_length _ _

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
