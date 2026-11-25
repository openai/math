import OAI.Optimization.LinearProgramming.Lattice.BitSelectorPost
import OAI.Optimization.LinearProgramming.Lattice.ShortSelector

/-! Composition of the native integer row-reduction ABI with the exact graph setup and decoder. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Selector
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

def PackedNativeLLL (red : IntMatrix → IntMatrix) : Prop :=
  ∀ {p n : ℕ} (b : Hex.Matrix ℤ (p+1) n), b.independent →
    red (packMatrix b) = packMatrix (Hex.lllNative b (3/4) (hn:=by omega))

def selectWith (red : IntMatrix → IntMatrix) (x : Input) : ℕ × List ℤ :=
  let f := prepare x
  finish (f.1,red f.2)

noncomputable def selectWithP {red : IntMatrix → IntMatrix} (reduceP : Procedure intMatrixCode intMatrixCode red) :
    Procedure inputCode outputCode (selectWith red) := by
  let run := (first contextCode intMatrixCode).pair (reduceP.comp (second contextCode intMatrixCode))
  exact finishP.comp (run.comp prepareP)

theorem packedTable_hex {n m : ℕ} (b : Hex.Matrix ℤ n m) :
    packedTable (HexMatrixMathlib.matrixEquiv b) = packMatrix b := by
  unfold packedTable packMatrix packVector
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  exact HexMatrixMathlib.matrixEquiv_apply b i j

theorem packedTable_toHex {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℤ) :
    packedTable B = packMatrix (HexMatrixMathlib.matrixEquiv.symm B) := by
  rw [← packedTable_hex,Equiv.apply_symm_apply]

theorem integralReductionWithPack (red : IntMatrix → IntMatrix) (hs : PackedNativeLLL red) {p n : ℕ} (B : Matrix (Fin (p+1)) (Fin n) ℤ)
    (hB : LinearIndependent ℝ (fun i => euclideanIntegerRow (B i))) :
    red (packedTable B) = packedTable (reduceInteger B) := by
  let b := HexMatrixMathlib.matrixEquiv.symm B
  have he : HexMatrixMathlib.matrixEquiv b = B := Equiv.apply_symm_apply _ _
  have hi := native_independent_of_rows b (he.symm ▸ hB)
  rw [packedTable_toHex B]
  exact (hs b hi).trans (packedTable_hex _).symm

/-- A polynomial-time literal word computation agrees on every input vector with the
native rational-matrix graph selector, including the recovered sign of every coefficient. -/
theorem selectWithPack (red : IntMatrix → IntMatrix) (hs : PackedNativeLLL red) {p : ℕ} (M : ℕ) (u : Fin p → ℚ) :
    selectWith red (M,List.ofFn u) = ((lllShortSelector M u).1, List.ofFn (lllShortSelector M u).2) := by
  let a : ℚ := 1/(searchDenominator p M : ℚ)^(p+1)
  let A := rationalGraphMatrix a u
  have ha : 0 < a := by dsimp [a]; have h := searchDenominator_pos p M; positivity
  have hA : LinearIndependent ℝ (fun i => euclideanRow (A i)) := by
    rw [show (fun i => euclideanRow (A i)) = _ from rationalGraphMatrix_rows a u]
    exact graphGenerators_independent (by exact_mod_cast ha.ne') _
  have hB := integralRows_linearIndependent A hA
  change finish (graphContext (M,List.ofFn u), red (prepare (M,List.ofFn u)).2) = _
  rw [preparePack, integralReductionWithPack red hs (integralRows A) hB]
  change finish ((List.ofFn u,graphAlpha (M,List.ofFn u),graphScale (M,List.ofFn u)),
    packedTable (reduceInteger (integralRows A))) = _
  rw [graphScalePack, graphAlphaPack,finishPack]
  rfl

end Selector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
