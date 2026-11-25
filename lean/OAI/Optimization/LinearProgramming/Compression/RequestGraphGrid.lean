import OAI.Optimization.LinearProgramming.Compression.RequestGraphTable
import OAI.Optimization.LinearProgramming.Compression.RequestDyadic
import OAI.Optimization.LinearProgramming.Lattice.BitClearRows
import OAI.Optimization.LinearProgramming.Lattice.BitArithmetic

/-! Construct both integer grid-query rows from the selected integer vector,
and decode the returned normalized midpoint into the rational offset. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

abbrev GridArg := ℕ × List ℤ
def gridArgCode := prodCode Nat.bits intRowCode
def orderSize (x : GridArg) := requestCutoff x.2.length * x.1
def gridDepth (x : GridArg) := (2*orderSize x).log2+1
def gridWidth (x : GridArg) := 2^(gridDepth x)
def gridLower (x : GridArg) : ℤ := -(orderSize x:ℤ)
def newCoeff (x : GridArg) : ℤ := readAt (0:ℤ) x.2 (x.2.length-1)
def gridSign (x : GridArg) : ℤ := if 0<newCoeff x then 1 else -1

def gridRows (x : GridArg) : List ℤ × List ℤ :=
  let c := 2*(x.1:ℤ)*gridSign x
  let w : ℤ := gridWidth x
  let h := |newCoeff x|
  (x.2.map (fun y => c*y) ++ [-(2*gridLower x+w)*h], x.2.map (fun _ => 0) ++ [w*h])

def gridOffset (x : GridArg) (ratio : ℚ) : ℚ :=
  let w := gridWidth x
  let mid := (ratio * (w:ℚ)).num
  ((gridLower x + (mid+(w:ℤ)-1)/2 : ℤ) : ℚ)/(x.1:ℚ)

noncomputable def orderSizeP : Procedure gridArgCode Nat.bits orderSize :=
  binaryMul.comp (((listCutoffP intCode 0).comp (second Nat.bits intRowCode)).pair (first Nat.bits intRowCode))

private theorem bit_length_positive {n : ℕ} (hn : n≠0) : n.bits.length=n.log2+1 := by
  rw [Nat.size_eq_bits_len]
  exact le_antisymm (Nat.size_le.mpr Nat.lt_log2_self) (Nat.lt_size.mpr (Nat.log2_self_le hn))

noncomputable def depthOfP : Procedure Nat.bits unaryCode (fun n => n.log2+1) := by
  let run := conditional binaryZero (constant Nat.bits unaryCode 1) (length.precompose Nat.bits)
  refine run.congrFun ?_
  intro n
  by_cases h : n=0
  · subst n; rfl
  · simpa [h] using bit_length_positive h

noncomputable def gridDepthP : Procedure gridArgCode unaryCode gridDepth :=
  depthOfP.comp (binaryMul.comp ((constant gridArgCode Nat.bits 2).pair orderSizeP))

noncomputable def gridWidthP : Procedure gridArgCode Nat.bits gridWidth :=
  Selector.powTwoP.comp gridDepthP

noncomputable def gridLowerP : Procedure gridArgCode intCode gridLower :=
  intNeg.comp (natToInt.comp orderSizeP)

noncomputable def newCoeffP : Procedure gridArgCode intCode newCoeff := by
  let z := second Nat.bits intRowCode
  exact getAtP (0:ℤ) z ((predIndexP (listLength intCode 0)).comp z)

noncomputable def gridSignP : Procedure gridArgCode intCode gridSign := by
  let cond := OracleSpec.Arithmetic.intLt.comp ((constant gridArgCode intCode (0:ℤ)).pair newCoeffP)
  exact (conditional cond (constant gridArgCode intCode (1:ℤ)) (constant gridArgCode intCode (-1:ℤ)))
    |>.congrFun (by intro x; simp [gridSign])

noncomputable def gridRowsP : Procedure gridArgCode (prodCode intRowCode intRowCode) gridRows := by
  let q := natToInt.comp (first Nat.bits intRowCode)
  let z := second Nat.bits intRowCode
  let twiceQ := intMul.comp ((constant gridArgCode intCode (2:ℤ)).pair q)
  let factor := intMul.comp (twiceQ.pair gridSignP)
  let left := Selector.mapWithContextP (f := fun x : GridArg => fun y : ℤ => 2*(x.1:ℤ)*gridSign x*y)
    (0:ℤ) (0:ℤ) z (intMul.comp ((factor.comp (second intCode gridArgCode)).pair (first intCode gridArgCode)))
  let right := (listMap (0:ℤ) (0:ℤ) (constant intCode intCode (0:ℤ))).comp z
  let w := natToInt.comp gridWidthP
  let h := natToInt.comp (intAbs.comp newCoeffP)
  let twoLo := intMul.comp ((constant gridArgCode intCode (2:ℤ)).pair gridLowerP)
  let a := intMul.comp ((intNeg.comp (intAdd.comp (twoLo.pair w))).pair h)
  let b := intMul.comp (w.pair h)
  let empty := constant gridArgCode intRowCode ([]:List ℤ)
  let lhs := (listAppend intCode 0).comp (left.pair ((listCons intCode).comp (a.pair empty)))
  let rhs := (listAppend intCode 0).comp (right.pair ((listCons intCode).comp (b.pair empty)))
  exact (lhs.pair rhs).congrFun (by intro x; simp [gridRows])

noncomputable def gridOffsetP : Procedure (prodCode gridArgCode ratCode) ratCode
    (fun x => gridOffset x.1 x.2) := by
  let arg := first gridArgCode ratCode
  let y := second gridArgCode ratCode
  let w := gridWidthP.comp arg
  let mid := ratNum.comp (ratMul.comp (y.pair (natToRat.comp w)))
  let sum := intAdd.comp (mid.pair (natToInt.comp w))
  let num := intSub.comp (sum.pair (constant _ intCode (1:ℤ)))
  let half := intDivNatP.comp (num.pair (constant _ Nat.bits 2))
  let total := intToRat.comp (intAdd.comp ((gridLowerP.comp arg).pair half))
  exact ratDiv.comp (total.pair (natToRat.comp ((first Nat.bits intRowCode).comp arg)))

theorem newCoeff_pack {n : ℕ} (q : ℕ) (z : Fin (n+1) → ℤ) :
    newCoeff (q,List.ofFn z) = z (Fin.last n) := by
  simp only [newCoeff,List.length_ofFn,Nat.add_sub_cancel]
  exact readAt_ofFn 0 z (Fin.last n)

theorem gridRows_pack {n : ℕ} (q : ℕ) (z : Fin (n+1) → ℤ) :
    let x : GridArg := (q,List.ofFn z)
    let rows := requestDyadicRows z (Fin.last n) q (gridLower x) (gridWidth x)
    gridRows x = (List.ofFn rows.1,List.ofFn rows.2) := by
  intro x rows
  have hz : newCoeff x=z (Fin.last n) := newCoeff_pack q z
  rw [List.ofFn_succ_last (f := rows.1),List.ofFn_succ_last (f := rows.2)]
  simp only [gridRows,gridSign,hz]
  simp [x,rows,requestDyadicRows,List.map_ofFn,Function.comp_def]

theorem gridOffset_of_midpoint (x : GridArg) (mid : ℤ) :
    gridOffset x ((mid:ℚ)/(gridWidth x : ℚ)) =
      ((gridLower x+(mid+(gridWidth x:ℤ)-1)/2 : ℤ):ℚ)/(x.1:ℚ) := by
  have hn : (gridWidth x : ℚ)≠0 := by unfold gridWidth; positivity
  simp [gridOffset,div_mul_cancel₀ _ hn]

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
