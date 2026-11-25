import OAI.Optimization.LinearProgramming.Geometry.GramEncoding
import OAI.Optimization.LinearProgramming.OracleSpec.Compression
import Mathlib.Data.List.OfFn

/-! The row-major arithmetic input and the minor oracle's row-by-row encoding agree. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open OracleSpec

theorem encodedGramInput_eq_entries {r n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ) :
    encodedGramInput D = MinorLog.entries D := by
  unfold encodedGramInput MinorLog.entries
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have same (h : i.val*n+j.val<r*n) : (⟨i.val*n+j.val,h⟩ : Fin (r*n))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*n+j.val=j.val+n*i.val
    ac_rfl
  simp only [same,Equiv.symm_apply_apply]


end Geometry
end LinearProgramming
end Optimization
end OAI
