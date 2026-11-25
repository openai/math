import OAI.Hierarchy.Models

namespace OAI
/-! # Scalar parameters of a formula

A scalar leaf labelled by `c : E` becomes the indeterminate indexed by `c`.
Evaluating the parameters replaces only leaves of the formula and preserves
its operation count.
-/

namespace Hierarchy

open MvPolynomial

noncomputable section

variable {C R S : Type*} {σ : Type}

namespace Formula

/-- Replace the constants in a formula, leaving each gate and each variable in place. -/
def relabel (z : C → R) : Formula C σ → Formula R σ
  | .constant c => .constant (z c)
  | .input i => .input i
  | .add f g => .add (relabel z f) (relabel z g)
  | .sub f g => .sub (relabel z f) (relabel z g)
  | .mul f g => .mul (relabel z f) (relabel z g)

@[simp] theorem cost_relabel (z : C → R) (f : Formula C σ) : (f.relabel z).cost = f.cost := by
  induction f <;> simp_all [relabel, MatrixMultiplication.Arithmetic.Expression.cost]

@[simp] theorem relabel_id (f : Formula C σ) : f.relabel id = f := by
  induction f <;> simp_all [relabel]

/-- Interpret scalar leaves in a commutative ring, including a polynomial parameter ring. -/
private def scalarPolynomial [CommRing R] (v : C → R) : Formula C σ → MvPolynomial σ R
  | .constant c => MvPolynomial.C (v c)
  | .input i => X i
  | .add f g => scalarPolynomial v f + scalarPolynomial v g
  | .sub f g => scalarPolynomial v f - scalarPolynomial v g
  | .mul f g => scalarPolynomial v f * scalarPolynomial v g

private theorem scalarPolynomial_eq [Field R] (v : C → R) (f : Formula C σ) :
    scalarPolynomial v f = (f.relabel v).polynomial := by
  induction f <;> simp_all [scalarPolynomial, relabel, polynomial,
    LinearAlgebra.SpectralBooks.expressionPolynomial]

private theorem map_scalarPolynomial [CommRing R] [CommRing S]
    (v : C → R) (φ : R →+* S) (f : Formula C σ) :
    map φ (scalarPolynomial v f) = scalarPolynomial (φ ∘ v) f := by
  induction f <;> simp_all [scalarPolynomial]

theorem specialize_relabel [Field R] [Field S] (v : C → R) (φ : R →+* S) (f : Formula C σ) :
    MvPolynomial.map φ (f.relabel v).polynomial = (f.relabel (φ ∘ v)).polynomial := by
  rw [← scalarPolynomial_eq, map_scalarPolynomial, scalarPolynomial_eq]

end Formula

variable {K E : Type*} [Field K] [Field E]

/-- Every bounded formula over the extension is a specialization of a polynomial
whose ground-field specializations all admit formulas with the original gate bound. -/
theorem formula_parameters [Algebra K E] {s : ℕ} {p : MvPolynomial σ E} (h : HasFormula s p) :
    ∃ G : MvPolynomial σ (MvPolynomial E K),
      (∀ z : E → K, HasFormula s (map (eval z) G)) ∧
      map (aeval (id : E → E)).toRingHom G = p := by
  obtain ⟨f, rfl, hs⟩ := h
  let v := X (R := K) (σ := E)
  refine ⟨Formula.scalarPolynomial v f, ?_, ?_⟩
  · intro z
    rw [Formula.map_scalarPolynomial, Formula.scalarPolynomial_eq]
    exact ⟨_, rfl, (f.cost_relabel _).le.trans hs⟩
  · rw [Formula.map_scalarPolynomial, Formula.scalarPolynomial_eq]
    have hv : (aeval (id : E → E) : MvPolynomial E K →ₐ[K] E).toRingHom ∘ v = id := by
      funext e
      simp [v]
    rw [hv, Formula.relabel_id]

end

end Hierarchy

end OAI
