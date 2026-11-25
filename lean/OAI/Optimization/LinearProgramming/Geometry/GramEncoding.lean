import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-! The ordinary row-major scalar tape for a rectangular matrix. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

def gramInputMatrix {K : Type} [Zero K] (r n : ℕ) (input : List K) :
    Matrix (Fin r) (Fin n) K := fun i j => input[i.val*n+j.val]?.getD 0

def encodedGramInput {K : Type} {r n : ℕ} (D : Matrix (Fin r) (Fin n) K) : List K :=
  List.ofFn (fun q : Fin (r*n) => D (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)

@[simp] theorem length_encodedGramInput {K : Type} {r n : ℕ} (D : Matrix (Fin r) (Fin n) K) :
    (encodedGramInput D).length = r*n := by simp [encodedGramInput]

@[simp] theorem gramInputMatrix_encoded {K : Type} [Zero K] {r n : ℕ} (D : Matrix (Fin r) (Fin n) K) :
    gramInputMatrix r n (encodedGramInput D) = D := by
  ext i j
  let q := finProdFinEquiv (i,j)
  have hv : q.val=i.val*n+j.val := by change j.val+n*i.val = _; ring
  change ((List.ofFn (fun q : Fin (r*n) => D (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2))[i.val*n+j.val]?).getD 0 = _
  rw [← hv, List.getElem?_ofFn, dite_eq_left q.isLt]
  change D (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 = _
  simp only [q,Equiv.symm_apply_apply]

end Geometry
end LinearProgramming
end Optimization
end OAI
