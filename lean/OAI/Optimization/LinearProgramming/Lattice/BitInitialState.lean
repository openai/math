import OAI.Optimization.LinearProgramming.Lattice.BitBirdDet
import OAI.Optimization.LinearProgramming.Lattice.BitInitCorrespondence

/-! Initialization of the native fraction-free LLL state by a single polynomial-time, finite
bit-stack program. Every mixed Gram determinant is constructed from the input basis rows. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

def mixedGramTable (A : IntMatrix) (i j : ℕ) : IntMatrix := squareTable (j+1) fun a b =>
  rowDot (rowAt A (if a<j then a else i)) (rowAt A b)

private noncomputable def mixedGramTableP : Procedure (squareArgCode intMatrixCode) intMatrixCode
    (fun x => mixedGramTable x.2 x.1.1 x.1.2) := by
  let arg := squareArgCode intMatrixCode
  let ij := first (prodCode unaryCode unaryCode) intMatrixCode
  let i := (first unaryCode unaryCode).comp ij
  let j := (second unaryCode unaryCode).comp ij
  let A := second (prodCode unaryCode unaryCode) intMatrixCode
  let c := second (prodCode unaryCode unaryCode) arg
  let ab := first (prodCode unaryCode unaryCode) arg
  let a := (first unaryCode unaryCode).comp ab
  let b := (second unaryCode unaryCode).comp ab
  let test := binaryLt.comp ((unaryToBits.comp a).pair (unaryToBits.comp (j.comp c)))
  let r := (conditional test a (i.comp c)).congrFun (by
    intro x; change (if decide (x.1.1 < x.2.1.2) = true then x.1.1 else x.2.1.1) =
      (if x.1.1 < x.2.1.2 then x.1.1 else x.2.1.1); simp)
  let row := (listGet intRowCode []).comp ((unaryToBits.comp r).pair (A.comp c))
  let col := (listGet intRowCode []).comp ((unaryToBits.comp b).pair (A.comp c))
  exact squareTableP arg (unarySuccessor.comp j)
    (f := fun x a b => rowDot (rowAt x.2 (if a<x.1.2 then a else x.1.1)) (rowAt x.2 b))
    (rowDotP.comp (row.pair col))

theorem listDet_mixedGramTable (A : IntMatrix) (i j : ℕ) :
    listDet (mixedGramTable A i j) = mixedGramDet A i j := by
  rw [listDet_eq_det]
  have h : (mixedGramTable A i j).length = j+1 := squareTable_length _ _
  rw [h]
  apply congrArg Matrix.det
  ext a b
  change entryAt (squareTable (j+1) _) a.val b.val = gramDotAt A (if a.val<j then a.val else i) b.val
  rw [squareTable_entryAt, gramDotAt_eq_range_sum]; rfl

/-- Both the leading and the mixed minors use the same encoded determinant machine. -/
noncomputable def mixedGramDetP : Procedure (squareArgCode intMatrixCode) intCode
    (fun x => mixedGramDet x.2 x.1.1 x.1.2) :=
  (listDetP.comp mixedGramTableP).congrFun (fun x => listDet_mixedGramTable x.2 x.1.1 x.1.2)

private noncomputable def nuCellP : Procedure (squareArgCode intMatrixCode) intCode
    (fun x => if x.1.1<x.1.2 then 0 else mixedGramDet x.2 x.1.1 x.1.2) := by
  let ij := first (prodCode unaryCode unaryCode) intMatrixCode
  let i := unaryToBits.comp ((first unaryCode unaryCode).comp ij)
  let j := unaryToBits.comp ((second unaryCode unaryCode).comp ij)
  let test := binaryLt.comp (i.pair j)
  exact (conditional test (constant (squareArgCode intMatrixCode) intCode (0:ℤ)) mixedGramDetP).congrFun
    (by intro x; change (if decide (x.1.1<x.1.2)=true then _ else _) = _; simp)

private noncomputable def toNatP : Procedure intCode Nat.bits Int.toNat :=
  (conditional intSign (constant intCode Nat.bits 0) intAbs).congrFun (by intro z; cases z <;> simp)

private theorem range_map_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp

noncomputable abbrev initState := mixedGramInitializer

/-- The initializer obtains its dimension from the encoded row list and materializes
`(basis,(ν,d))` in the shared LLL ABI, including `d[0]=1` for the empty basis. -/
noncomputable def initStateP : Procedure intMatrixCode stateCode initState := by
  let input := identity intMatrixCode
  let n := OAI.Optimization.LinearProgramming.PriceGame.Learning.GenerationCost.lengthUnaryP intRowCode ([] : List ℤ)
  let nu := squareTableP intMatrixCode n (f := fun A i j => if i<j then 0 else mixedGramDet A i j) nuCellP
  let i := first unaryCode intMatrixCode
  let A := second unaryCode intMatrixCode
  let one := constant intMatrixCode Nat.bits 1
  let entry := toNatP.comp (mixedGramDetP.comp ((i.pair i).pair A))
  let diag := (tabulate (f := fun A i => (mixedGramDet A i i).toNat) 0 entry).comp (n.pair input)
  let d := (listCons Nat.bits).comp (one.pair diag)
  refine (input.pair (nu.pair d)).congrFun ?_
  intro A
  change (A, squareTable A.length _, 1::(List.range A.length).map _) = mixedGramInitializer A
  simp [squareTable,mixedGramInitializer,range_map_ofFn]

/-- The output is exactly the native Hex state, including every Gram denominator. -/
theorem initState_packMatrix {n m : ℕ} (A : Hex.Matrix ℤ n m) :
    initState (packMatrix A) = packState (Hex.Internal.LLLState.ofBasis A) := mixedGramInitializer_packMatrix A

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
