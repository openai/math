import OAI.Hierarchy.Models

namespace OAI
/-! # Uniform rescaling of variables in an affine branching program

Substituting `X i ↦ C t * X i` multiplies each linear coefficient of an edge label
by `t`. The graph, including its sink and the number of parallel edges, is preserved.
-/

namespace Hierarchy
open MvPolynomial
noncomputable section

variable {F : Type*} {σ : Type} [CommSemiring F]

private def Affine.scaleVars (a : Affine F σ) (t : F) : Affine F σ :=
  ⟨a.constant, fun i => a.coeff i * t⟩

private theorem Affine.polynomial_scaleVars [Fintype σ] (a : Affine F σ) (t : F) :
    (a.scaleVars t).polynomial = aeval (fun i => C t * X i) a.polynomial := by
  simp [Affine.scaleVars, Affine.polynomial, map_sum, algebraMap_eq, mul_assoc]

private def Rows.scaleVars (t : F) : {n : ℕ} → Rows F σ n → Rows F σ n
  | _, .source => .source
  | _, .snoc prev edges =>
    .snoc (prev.scaleVars t) (edges.map fun e => (e.1, e.2.scaleVars t))

private theorem Rows.edgeCount_scaleVars {n : ℕ} (rows : Rows F σ n) (t : F) :
    (rows.scaleVars t).edgeCount = rows.edgeCount := by
  induction rows <;> simp [Rows.scaleVars, Rows.edgeCount, *]

private theorem Rows.values_scaleVars [Fintype σ] {n : ℕ} (rows : Rows F σ n) (t : F)
    (j : Fin n) : (rows.scaleVars t).values j = aeval (fun i => C t * X i) (rows.values j) := by
  induction rows with
  | source => simp [Rows.scaleVars, Rows.values]
  | snoc prev edges ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Rows.scaleVars, Rows.values, map_list_sum, List.map_map, Function.comp_def,
        Affine.polynomial_scaleVars, ih]
    · simp [Rows.scaleVars, Rows.values, ih]

/-- Rescale the input variables on every edge of the branching program. -/
def ABP.scaleVars (g : ABP F σ) (t : F) : ABP F σ :=
  ⟨g.vertices, g.rows.scaleVars t, g.sink⟩

@[simp] theorem ABP.size_scaleVars (g : ABP F σ) (t : F) : (g.scaleVars t).size = g.size := by
  simp [ABP.scaleVars, ABP.size, Rows.edgeCount_scaleVars]

@[simp] theorem ABP.polynomial_scaleVars [Fintype σ] (g : ABP F σ) (t : F) :
    (g.scaleVars t).polynomial = aeval (fun i => C t * X i) g.polynomial :=
  Rows.values_scaleVars g.rows t g.sink

end
end Hierarchy

end OAI
