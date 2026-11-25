import OAI.Hierarchy.Models

namespace OAI
/-! # Scalar parameters of an algebraic branching program

Replacing every occurrence of a coefficient by a parameter preserves the graph.
Specializing its output polynomial thus realizes an entire polynomially parameterized
family of outputs at the original size.
-/

namespace Hierarchy

open scoped BigOperators
noncomputable section

variable {C R S : Type*} {σ : Type}

/-- Replace every coefficient in an affine edge label, retaining its variable slots. -/
def Affine.relabel (v : C → R) (l : Affine C σ) : Affine R σ :=
  ⟨v l.constant, fun i => v (l.coeff i)⟩

@[simp] theorem Affine.relabel_id (l : Affine C σ) : l.relabel id = l := rfl

private theorem Affine.specialize_relabel [CommSemiring R] [CommSemiring S] [Fintype σ]
    (v : C → R) (φ : R →+* S) (l : Affine C σ) :
    MvPolynomial.map φ (l.relabel v).polynomial = (l.relabel (φ ∘ v)).polynomial := by
  simp [Affine.relabel, Affine.polynomial, map_sum]

/-- Retain every vertex and incoming edge and relabel all scalar entries. -/
def Rows.relabel (v : C → R) : {m : ℕ} → Rows C σ m → Rows R σ m
  | _, .source => .source
  | _, .snoc prev edges => .snoc (prev.relabel v) (edges.map fun e => (e.1, e.2.relabel v))

@[simp] theorem Rows.edgeCount_relabel {m : ℕ} (v : C → R) (rows : Rows C σ m) :
    (rows.relabel v).edgeCount = rows.edgeCount := by
  induction rows <;> simp [Rows.relabel, Rows.edgeCount, *]

@[simp] theorem Rows.relabel_id {m : ℕ} (rows : Rows C σ m) : rows.relabel id = rows := by
  induction rows <;> simp [Rows.relabel, *]

private theorem Rows.specialize_relabel [CommSemiring R] [CommSemiring S] [Fintype σ]
    {m : ℕ} (v : C → R) (φ : R →+* S) (rows : Rows C σ m) (j : Fin m) :
    MvPolynomial.map φ ((rows.relabel v).values j) = (rows.relabel (φ ∘ v)).values j := by
  induction rows with
  | source => simp [Rows.relabel, Rows.values]
  | snoc prev edges ih =>
    induction j using Fin.lastCases with
    | last =>
      simp [Rows.relabel, Rows.values, map_list_sum, List.map_map, Function.comp_def,
        Affine.specialize_relabel, ih]
    | cast j => simp [Rows.relabel, Rows.values, ih]

def ABP.relabel (v : C → R) (g : ABP C σ) : ABP R σ := ⟨g.vertices, g.rows.relabel v, g.sink⟩

@[simp] theorem ABP.size_relabel (v : C → R) (g : ABP C σ) : (g.relabel v).size = g.size := by
  simp [ABP.relabel, ABP.size]

@[simp] theorem ABP.relabel_id (g : ABP C σ) : g.relabel id = g := by simp [ABP.relabel]

theorem ABP.specialize_relabel [CommSemiring R] [CommSemiring S] [Fintype σ]
    (v : C → R) (φ : R →+* S) (g : ABP C σ) :
    MvPolynomial.map φ (g.relabel v).polynomial = (g.relabel (φ ∘ v)).polynomial :=
  Rows.specialize_relabel v φ g.rows g.sink

/-- Regard each scalar appearing in an ABP over the extension as an indeterminate over
the base. Evaluating those indeterminates at their original values recovers the target.
Every specialization to base-field values is realized by a program of the same size. -/
theorem abp_parameters {K E : Type*} [Field K] [Field E] [Algebra K E] [Fintype σ]
    {s : ℕ} {p : MvPolynomial σ E} (h : HasABP s p) :
    ∃ G : MvPolynomial σ (MvPolynomial E K),
      (∀ z : E → K, HasABP s (MvPolynomial.map (MvPolynomial.eval z) G)) ∧
      MvPolynomial.map (MvPolynomial.aeval (id : E → E) : MvPolynomial E K →ₐ[K] E).toRingHom G = p := by
  obtain ⟨g, rfl, hsize⟩ := h
  let v := MvPolynomial.X (R := K) (σ := E)
  use (g.relabel v).polynomial
  constructor
  · intro z
    rw [ABP.specialize_relabel]
    exact ⟨_, rfl, (g.size_relabel _).trans_le hsize⟩
  · rw [ABP.specialize_relabel]
    have hv : (MvPolynomial.aeval (id : E → E) : MvPolynomial E K →ₐ[K] E).toRingHom ∘ v = id := by
      funext e
      simp [v]
    rw [hv, ABP.relabel_id]

end
end Hierarchy

end OAI
