import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The closed convex hull of norming functionals

In finite dimension every linear functional on the dual is evaluation at a
vector. Separation then shows that the dual unit ball is contained in the
closed convex hull of any family which recovers the norm pointwise.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem mem_closure_convexHull_of_norming {S : Set (E →L[ℝ] ℝ)}
    (hS : ∀ x : E, ∀ r < ‖x‖, ∃ g ∈ S, r < g x) {f : E →L[ℝ] ℝ} (hf : ‖f‖ ≤ 1) :
    f ∈ closure (convexHull ℝ S) := by
  by_contra hout
  obtain ⟨L, r, hsep, hr⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ S).closure isClosed_closure hout
  let L' : Module.Dual ℝ (Module.Dual ℝ E) :=
    L.toLinearMap.comp LinearMap.toContinuousLinearMap.toLinearMap
  let x := (Module.evalEquiv ℝ E).symm L'
  have heval (g : E →L[ℝ] ℝ) : g x = L g :=
    Module.apply_evalEquiv_symm_apply ℝ E g.toLinearMap L'
  have hfx : f x ≤ ‖x‖ := calc
    f x ≤ ‖f x‖ := le_abs_self _
    _ ≤ 1 * ‖x‖ := f.le_of_opNorm_le hf x
    _ = ‖x‖ := one_mul _
  rw [← heval f] at hr
  obtain ⟨g, hg, hrg⟩ := hS x r (hr.trans_le hfx)
  rw [heval g] at hrg
  exact (hsep g (subset_closure (subset_convexHull ℝ S hg))).not_gt hrg

end SpectralBooks
end LinearAlgebra
end OAI
