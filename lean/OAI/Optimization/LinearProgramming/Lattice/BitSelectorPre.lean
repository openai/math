import OAI.Optimization.LinearProgramming.Lattice.BitClearRows
import OAI.Optimization.LinearProgramming.Lattice.ShortSelectorCore

/-! Build the exact integral graph basis for the first-row LLL selector on framed words. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Selector
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- Retain the normalized vector, graph parameter and common positive integer scale
alongside the table given to the integer LLL program. -/
abbrev Context := List ℚ × (ℚ × ℕ)
abbrev Frame := Context × IntMatrix
def contextCode := prodCode vectorCode (prodCode ratCode Nat.bits)
def frameCode := prodCode contextCode intMatrixCode

def graphTable (x : Input) : RatTable :=
  (graphAlpha x :: x.2) :: (List.range x.2.length).map fun i =>
    0 :: (List.range x.2.length).map fun j => if i=j then -1 else 0

def graphContext (x : Input) : Context := (x.2,graphAlpha x,graphScale x)
def prepare (x : Input) : Frame := (graphContext x, integralRowsList (graphTable x))

noncomputable def graphTableP : Procedure inputCode ratTableCode graphTable := by
  let vec := second Nat.bits vectorCode
  let rowCode := prodCode Nat.bits inputCode
  let cellCode := prodCode Nat.bits rowCode
  let i := (first Nat.bits inputCode).comp (second Nat.bits rowCode)
  let j := first Nat.bits rowCode
  let diagonal : Procedure cellCode ratCode (fun x : ℕ × (ℕ × Input) =>
      if x.2.1=x.1 then -1 else 0) :=
    (conditional (natEqP i j) (constant cellCode ratCode (-1)) (constant cellCode ratCode 0)).congrFun
      (by intro x; simp)
  let body := tabulateBinaryAlongP (ed:=ratCode)
    (cell:=fun (x : ℕ × Input) j => if x.1=j then (-1:ℚ) else 0)
    (0:ℚ) (0:ℚ) (vec.comp (second Nat.bits inputCode)) diagonal
  let lowerRow := (listCons (ea:=ratCode)).comp ((constant rowCode ratCode 0).pair body)
  let lower := tabulateBinaryAlongP (ed:=vectorCode)
    (cell:=fun (x : Input) i => (0:ℚ) :: (List.range x.2.length).map (fun j => if i=j then -1 else 0))
    (0:ℚ) ([]:List ℚ) vec lowerRow
  let upper := (listCons (ea:=ratCode)).comp (graphAlphaP.pair vec)
  exact (listCons (ea:=vectorCode)).comp (upper.pair lower)

noncomputable def graphContextP : Procedure inputCode contextCode graphContext :=
  (second Nat.bits vectorCode).pair (graphAlphaP.pair graphScaleP)

noncomputable def prepareP : Procedure inputCode frameCode prepare :=
  graphContextP.pair (integralRowsListP.comp graphTableP)

theorem graphAlphaPack {p : ℕ} (u : Fin p → ℚ) (M : ℕ) :
    graphAlpha (M,List.ofFn u) = 1 / (searchDenominator p M : ℚ)^(p+1) := by
  simp [graphAlpha]

theorem graphTablePack {p : ℕ} (u : Fin p → ℚ) (M : ℕ) :
    graphTable (M,List.ofFn u) = packedTable (rationalGraphMatrix (graphAlpha (M,List.ofFn u)) u) := by
  let a := graphAlpha (M,List.ofFn u)
  change (a :: List.ofFn u) :: (List.range (List.ofFn u).length).map _ = _
  simp only [List.length_ofFn]
  unfold packedTable
  rw [List.ofFn_succ]
  congr 1
  · rw [List.ofFn_succ]; simp [rationalGraphMatrix,a]
  · apply List.ext_getElem (by simp)
    intro i hi _
    have hi' : i < p := by simpa using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [List.ofFn_succ]
    simp only [rationalGraphMatrix,Fin.cons_succ,Fin.cons_zero,List.cons.injEq,true_and]
    apply List.ext_getElem (by simp)
    intro j hj _
    simp [Fin.ext_iff]

theorem graphMatrix_denominator {p : ℕ} (a : ℚ) (u : Fin p → ℚ) :
    matrixDenominator (rationalGraphMatrix a u) = a.den * ∏ i, (u i).den := by
  have lower (i : Fin p) : (∏ j, (rationalGraphMatrix a u i.succ j).den) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · by_cases h : i=k <;> simp [rationalGraphMatrix,h]
  unfold matrixDenominator
  rw [Fin.prod_univ_succ]
  simp only [lower,Finset.prod_const_one,mul_one]
  rw [Fin.prod_univ_succ]
  simp [rationalGraphMatrix]

theorem graphScalePack {p : ℕ} (u : Fin p → ℚ) (M : ℕ) :
    graphScale (M,List.ofFn u) = matrixDenominator (rationalGraphMatrix (graphAlpha (M,List.ofFn u)) u) := by
  rw [graphMatrix_denominator]
  simp [graphScale,List.map_ofFn,List.prod_ofFn,Function.comp_def]

theorem preparePack {p : ℕ} (u : Fin p → ℚ) (M : ℕ) :
    (prepare (M,List.ofFn u)).2 =
      packedTable (integralRows (rationalGraphMatrix (1 / (searchDenominator p M : ℚ)^(p+1)) u)) := by
  change integralRowsList (graphTable (M,List.ofFn u)) = _
  rw [graphTablePack,graphAlphaPack]
  exact integralRowsListPack (fun i j => rationalGraphMatrix (1 / (searchDenominator p M : ℚ)^(p+1)) u i j)

end Selector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
