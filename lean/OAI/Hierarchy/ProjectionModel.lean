import OAI.Hierarchy.FormulaProjection

namespace OAI
/-! # Variable-or-constant projections of affine branching programs

Each projected affine label collects the weights of source variables that land on the
same target variable. A source variable mapped to a scalar contributes to the new
constant coefficient. All vertices and incoming edges can then be kept.
-/

namespace Hierarchy

open MvPolynomial
open scoped BigOperators Classical

noncomputable section

variable {F : Type*} {σ τ : Type} [CommSemiring F]

private def scalarContribution (r : F) (image : τ ⊕ F) : F :=
  image.elim (fun _ => 0) (fun c => r * c)

private def variableContribution (r : F) (image : τ ⊕ F) (j : τ) : F :=
  image.elim (fun k => if j = k then r else 0) (fun _ => 0)

/-- Substitute projected variables in an affine label, combining coincident images. -/
def Affine.project [Fintype σ] (l : Affine F σ) (φ : Computability.VPVNP.Projection F σ τ) : Affine F τ :=
  ⟨l.constant + ∑ i, scalarContribution (l.coeff i) (φ i),
    fun j => ∑ i, variableContribution (l.coeff i) (φ i) j⟩

private theorem contribution [Fintype τ] (φ : Computability.VPVNP.Projection F σ τ) (r : F) (i : σ) :
    C (scalarContribution r (φ i)) + ∑ j, C (variableContribution r (φ i) j) * X j =
      φ.hom (C r * X i) := by
  cases h : φ i with
  | inl k => simp [scalarContribution, variableContribution, Computability.VPVNP.Projection.hom, h, apply_ite, ite_mul]
  | inr c => simp [scalarContribution, variableContribution, Computability.VPVNP.Projection.hom, h]

@[simp] theorem Affine.polynomial_project [Fintype σ] [Fintype τ]
    (l : Affine F σ) (φ : Computability.VPVNP.Projection F σ τ) :
    (l.project φ).polynomial = φ.hom l.polynomial := by
  calc
    _ = C l.constant + ∑ i, (C (scalarContribution (l.coeff i) (φ i)) +
        ∑ j, C (variableContribution (l.coeff i) (φ i) j) * X j) := by
      simp only [Affine.project, Affine.polynomial, map_add, map_sum, Finset.sum_mul,
        Finset.sum_add_distrib, add_assoc]
      rw [Finset.sum_comm (s := (Finset.univ : Finset τ))]
    _ = _ := by
      simp only [contribution, Affine.polynomial, map_add, map_sum, Computability.VPVNP.Projection.hom,
        MvPolynomial.eval₂Hom_C]

def Rows.project [Fintype σ] (φ : Computability.VPVNP.Projection F σ τ) : {n : ℕ} → Rows F σ n → Rows F τ n
  | _, .source => .source
  | _, .snoc prev edges => .snoc (prev.project φ) (edges.map fun e => (e.1, e.2.project φ))

@[simp] theorem Rows.edgeCount_project [Fintype σ] (φ : Computability.VPVNP.Projection F σ τ)
    {n : ℕ} (rows : Rows F σ n) : (rows.project φ).edgeCount = rows.edgeCount := by
  induction rows <;> simp [Rows.project, Rows.edgeCount, *]

@[simp] theorem Rows.values_project [Fintype σ] [Fintype τ] (φ : Computability.VPVNP.Projection F σ τ)
    {n : ℕ} (rows : Rows F σ n) (j : Fin n) : (rows.project φ).values j = φ.hom (rows.values j) := by
  induction rows with
  | source => simp [Rows.project, Rows.values]
  | snoc prev edges ih =>
    induction j using Fin.lastCases with
    | last => simp [Rows.project, Rows.values, map_list_sum, List.map_map, Function.comp_def, ih]
    | cast j => simp [Rows.project, Rows.values, ih]

/-- Substitute variables in each label without modifying the underlying branching program. -/
def ABP.project [Fintype σ] (g : ABP F σ) (φ : Computability.VPVNP.Projection F σ τ) : ABP F τ :=
  ⟨g.vertices, g.rows.project φ, g.sink⟩

@[simp] theorem ABP.size_project [Fintype σ] (g : ABP F σ) (φ : Computability.VPVNP.Projection F σ τ) :
    (g.project φ).size = g.size := by simp [ABP.project, ABP.size]

@[simp] theorem ABP.polynomial_project [Fintype σ] [Fintype τ]
    (g : ABP F σ) (φ : Computability.VPVNP.Projection F σ τ) :
    (g.project φ).polynomial = φ.hom g.polynomial := g.rows.values_project φ g.sink

end

noncomputable section
variable {F : Type*} {σ τ : Type} [Field F] [Fintype σ] [Fintype τ]

theorem HasABP.project {s : ℕ} {p : MvPolynomial σ F} (h : HasABP s p)
    (φ : Computability.VPVNP.Projection F σ τ) : HasABP s (φ.hom p) := by
  obtain ⟨g, rfl, hs⟩ := h
  exact ⟨g.project φ, g.polynomial_project φ, (g.size_project φ).trans_le hs⟩

end

end Hierarchy

end OAI
