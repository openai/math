import OAI.Optimization.LinearProgramming.Lattice.BitClearRows
import OAI.Optimization.LinearProgramming.Lattice.LLLNative
import OAI.Computability.QuantumFactoring.BitStackRationalDivision

/-! A common denominator on the framed input, one integral reduction, and full
output rescaling realize rational LLL at variable input and output dimensions. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Selector

abbrev RatMatrix := List (List ℚ)
abbrev ratMatrixCode := ratTableCode

def unscaleRows (A : IntMatrix) (d : ℕ) : RatMatrix :=
  A.map fun row => row.map fun z : ℤ => (z:ℚ)/(d:ℚ)

noncomputable def unscaleValueP : Procedure (prodCode intCode Nat.bits) ratCode
    (fun x : ℤ × ℕ => (x.1:ℚ)/(x.2:ℚ)) :=
  ratDiv.comp ((intToRat.comp (first intCode Nat.bits)).pair (natToRat.comp (second intCode Nat.bits)))

noncomputable def unscaleRowP : Procedure (prodCode intRowCode Nat.bits) vectorCode
    (fun x => x.1.map fun z : ℤ => (z:ℚ)/(x.2:ℚ)) := by
  let code := prodCode intRowCode Nat.bits
  let v := first intRowCode Nat.bits
  let d := (second intRowCode Nat.bits).comp (second intCode code)
  exact mapWithContextP (0:ℤ) (0:ℚ) v (unscaleValueP.comp ((first intCode code).pair d))

noncomputable def unscaleRowsP : Procedure (prodCode intMatrixCode Nat.bits) ratMatrixCode
    (fun x => unscaleRows x.1 x.2) := by
  let code := prodCode intMatrixCode Nat.bits
  let A := first intMatrixCode Nat.bits
  let d := (second intMatrixCode Nat.bits).comp (second intRowCode code)
  exact mapWithContextP ([]:List ℤ) ([]:List ℚ) A
    (unscaleRowP.comp ((first intRowCode code).pair d))

def lllRatRowsWith (reduce : IntMatrix → IntMatrix) (A : RatMatrix) : RatMatrix :=
  unscaleRows (reduce (integralRowsList A)) (matrixDenominatorList A)

noncomputable def lllRatRowsWithP {reduce : IntMatrix → IntMatrix}
    (r : Procedure intMatrixCode intMatrixCode reduce) :
    Procedure ratMatrixCode ratMatrixCode (lllRatRowsWith reduce) :=
  unscaleRowsP.comp ((r.comp integralRowsListP).pair matrixDenominatorListP)

theorem packMatrix_eq_table {p n : ℕ} (A : Hex.Matrix ℤ p n) :
    packMatrix A = packedTable (HexMatrixMathlib.matrixEquiv A) := by
  unfold packMatrix packVector packedTable
  congr 1
  funext i
  congr 1
  funext j
  rw [HexMatrixMathlib.matrixEquiv_apply]
  rfl

theorem unscaleRows_pack {p n : ℕ} (d : ℕ) (A : Fin p → Fin n → ℤ) :
    unscaleRows (packedTable A) d = packedTable (fun i => unscaleIntegerRow d (A i)) := by
  simp [unscaleRows,packedTable,List.map_ofFn,Function.comp_def,unscaleIntegerRow]

theorem lllRatRowsWith_pack {p n : ℕ} (reduce : IntMatrix → IntMatrix)
    (A : Matrix (Fin (p+1)) (Fin n) ℚ) (ha : LinearIndependent ℝ (fun i => euclideanRow (A i)))
    (hr : ∀ b : Hex.Matrix ℤ (p+1) n, b.independent →
      reduce (packMatrix b) = packMatrix (Hex.lllNative b (3/4))) :
    lllRatRowsWith reduce (packedTable A) = packedTable (reduceRational A) := by
  let b := HexMatrixMathlib.matrixEquiv.symm (integralRows A)
  have he : HexMatrixMathlib.matrixEquiv b = integralRows A :=
    HexMatrixMathlib.matrixEquiv.apply_symm_apply _
  have hi : b.independent := native_independent_of_rows b (he.symm ▸ integralRows_linearIndependent A ha)
  have hp : packedTable (integralRows A) = packMatrix b := by rw [packMatrix_eq_table,he]
  let F := fun (i : Fin (p+1)) (j : Fin n) => A i j
  calc
    _ = unscaleRows (reduce (packMatrix b)) (matrixDenominator A) :=
      congrArg₂ (fun t D => unscaleRows (reduce t) D)
        ((integralRowsListPack F).trans hp) (matrixDenominatorListPack F)
    _ = unscaleRows (packMatrix (Hex.lllNative b (3/4))) (matrixDenominator A) :=
      congrArg (fun t => unscaleRows t (matrixDenominator A)) (hr b hi)
    _ = _ := (congrArg (fun t => unscaleRows t (matrixDenominator A)) (packMatrix_eq_table _)).trans
      (unscaleRows_pack (matrixDenominator A) (HexMatrixMathlib.matrixEquiv _))

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
