import OAI.Optimization.LinearProgramming.Lattice.BitState
import OAI.Optimization.LinearProgramming.PriceGame.ControlRatListSum
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost

/-! Signed row arithmetic and uniform matrix construction on the explicit bit-stack machine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- One finite bit-stack program for an arbitrary list of signed integers. -/
noncomputable def intListSumP : Procedure intRowCode intCode (List.sum : List ℤ → ℤ) := by
  let cast := listMap 0 0 intToRat
  let total := OAI.Optimization.LinearProgramming.PriceGame.Control.Native.ratListSumP.comp cast
  refine (ratNum.comp total).congrFun ?_
  intro xs
  change (xs.map (fun x : ℤ => (x : ℚ))).sum.num = xs.sum
  have h : (xs.map (fun x : ℤ => (x : ℚ))).sum = (xs.sum : ℚ) := by
    induction xs with
    | nil => simp
    | cons x xs ih => exact (congrArg (fun y : ℚ => (x : ℚ)+y) ih).trans (Int.cast_add x xs.sum).symm
  exact (congrArg Rat.num h).trans (Rat.num_intCast _)

/-- The dot product uses all entries of the first row, with zero padding on the second row. -/
def rowDot (x y : List ℤ) : ℤ := ((List.range x.length).map fun k => readAt 0 x k * readAt 0 y k).sum

noncomputable def rowDotP : Procedure (prodCode intRowCode intRowCode) intCode
    (fun p : List ℤ × List ℤ => rowDot p.1 p.2) := by
  let ctx := prodCode intRowCode intRowCode
  let x := first intRowCode intRowCode
  let y := second intRowCode intRowCode
  let k := unaryToBits.comp (first unaryCode ctx)
  let input := second unaryCode ctx
  let xi := (listGet intCode 0).comp (k.pair (x.comp input))
  let yi := (listGet intCode 0).comp (k.pair (y.comp input))
  let entries := tabulate (f := fun z : List ℤ × List ℤ => fun i => readAt 0 z.1 i * readAt 0 z.2 i)
    (0:ℤ) (intMul.comp (xi.pair yi))
  let n := (OAI.Optimization.LinearProgramming.PriceGame.Learning.GenerationCost.lengthUnaryP intCode 0).comp x
  exact intListSumP.comp (entries.comp (n.pair (identity ctx)))

/-- All entries of an arbitrary square list matrix are materialized in increasing row/column order. -/
def squareTable (n : ℕ) (f : ℕ → ℕ → ℤ) : IntMatrix :=
  (List.range n).map fun i => (List.range n).map fun j => f i j

def squareArgCode {α : Type} (e : α → List Bool) := prodCode (prodCode unaryCode unaryCode) e

/-- Both generated indices have unary encodings, of length bounded by the dimension supplied
by the size procedure. The entry evaluator and the emitted matrix use signed binary integers. -/
noncomputable def valueSquareTableP {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (d : β) {dim : α → ℕ}
    (sizeP : Procedure ea unaryCode dim) {f : α → ℕ → ℕ → β}
    (entryP : Procedure (squareArgCode ea) eb (fun p => f p.2 p.1.1 p.1.2)) :
    Procedure ea (listCode (listCode eb)) (fun x => (List.range (dim x)).map fun i =>
      (List.range (dim x)).map (f x i)) := by
  let ctx := prodCode unaryCode ea
  let i := first unaryCode ea
  let x := second unaryCode ea
  let j := first unaryCode ctx
  let ix := second unaryCode ctx
  let cell := entryP.comp (((i.comp ix).pair j).pair (x.comp ix))
  let row := (tabulate (f := fun p : ℕ × α => fun c => f p.2 p.1 c) d cell).comp
    ((sizeP.comp x).pair (identity ctx))
  let out := tabulate (f := fun x : α => fun i => (List.range (dim x)).map (f x i)) ([] : List β) row
  exact out.comp (sizeP.pair (identity ea))

noncomputable def squareTableP {α : Type} (ea : α → List Bool) {dim : α → ℕ}
    (sizeP : Procedure ea unaryCode dim) {f : α → ℕ → ℕ → ℤ}
    (entryP : Procedure (squareArgCode ea) intCode (fun p => f p.2 p.1.1 p.1.2)) :
    Procedure ea intMatrixCode (fun x => squareTable (dim x) (f x)) :=
  valueSquareTableP ea intCode 0 sizeP entryP

@[simp] theorem squareTable_length (n : ℕ) (f : ℕ → ℕ → ℤ) : (squareTable n f).length = n := by
  simp [squareTable]

theorem squareTable_entryAt {n : ℕ} (f : ℕ→ℕ→ℤ) (i j : Fin n) :
    entryAt (squareTable n f) i.val j.val = f i.val j.val := by
  simp [squareTable,entryAt,rowAt,readAt,List.head?_drop,i.isLt,j.isLt]

/-- The Gram matrix has one row and column for each encoded input row. -/
def gramTable (B : IntMatrix) : IntMatrix := squareTable B.length (fun i j => rowDot (rowAt B i) (rowAt B j))

noncomputable def gramTableP : Procedure intMatrixCode intMatrixCode gramTable := by
  let e := intMatrixCode
  let ij := first (prodCode unaryCode unaryCode) e
  let i := unaryToBits.comp ((first unaryCode unaryCode).comp ij)
  let j := unaryToBits.comp ((second unaryCode unaryCode).comp ij)
  let m := second (prodCode unaryCode unaryCode) e
  let x := (listGet intRowCode []).comp (i.pair m)
  let y := (listGet intRowCode []).comp (j.pair m)
  exact squareTableP e (OAI.Optimization.LinearProgramming.PriceGame.Learning.GenerationCost.lengthUnaryP intRowCode [])
    (f := fun b i j => rowDot (rowAt b i) (rowAt b j)) (rowDotP.comp (x.pair y))

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
