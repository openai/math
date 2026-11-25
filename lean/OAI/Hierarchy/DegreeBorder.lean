import OAI.Computability.BorderVNP.Model

namespace OAI
/-! # Degree-component border approximation for a bounded computation model

Only coordinates of total degree `d` are recorded. In particular the outputs
of the approximating computations are unrestricted in degree. For a target
over `F`, both the scalar parameters of the model and the polynomial equations
cutting out its closure range over the algebraic closure of `F`.
-/

namespace Hierarchy

open MvPolynomial

variable {σ F K : Type*} [Field F] [Field K]

/-- Zariski closure of the attainable degree-component vectors at size at most `s`.
The predicate `model s q` describes exact formal outputs over `K`. -/
def degreeModelClosure (model : ℕ → MvPolynomial σ K → Prop) (d s : ℕ) :
    Set (Computability.BorderVNP.DegreeMonomial σ d → K) :=
  Computability.BorderVNP.imageClosure (Computability.BorderVNP.coeffVector d '' {q | model s q})

/-- A target over `F` meets the degree-component border bound if its coefficient
vector after scalar extension belongs to the attainable image closure. -/
def DegreeBorderAtMost (model : ℕ → MvPolynomial σ (AlgebraicClosure F) → Prop)
    (d s : ℕ) (f : MvPolynomial σ F) : Prop :=
  Computability.BorderVNP.coeffVector d (map (algebraMap F (AlgebraicClosure F)) f) ∈
    degreeModelClosure model d s

/-- Exact realization implies membership in the closure at the same cost. -/
theorem mem_degreeModelClosure_of_exact {model : ℕ → MvPolynomial σ K → Prop}
    {d s : ℕ} {q : MvPolynomial σ K} (h : model s q) :
    Computability.BorderVNP.coeffVector d q ∈ degreeModelClosure model d s :=
  Computability.BorderVNP.subset_imageClosure _ ⟨q, h, rfl⟩

theorem degreeBorderAtMost_of_exact_map {model : ℕ → MvPolynomial σ (AlgebraicClosure F) → Prop}
    {d s : ℕ} {f : MvPolynomial σ F} (h : model s (map (algebraMap F (AlgebraicClosure F)) f)) :
    DegreeBorderAtMost model d s f :=
  mem_degreeModelClosure_of_exact h

/-- A simulation of all exact outputs extends to the degree-component border
models, with the same relation between the two size budgets. -/
theorem degreeModelClosure_mono {model other : ℕ → MvPolynomial σ K → Prop}
    {d s t : ℕ} (h : ∀ q, model s q → other t q) :
    degreeModelClosure model d s ⊆ degreeModelClosure other d t :=
  Computability.BorderVNP.imageClosure_mono (Set.image_mono (fun q hq => h q hq))

theorem DegreeBorderAtMost.mono {model other : ℕ → MvPolynomial σ (AlgebraicClosure F) → Prop}
    {d s t : ℕ} {f : MvPolynomial σ F} (h : DegreeBorderAtMost model d s f)
    (hmodel : ∀ q, model s q → other t q) : DegreeBorderAtMost other d t f :=
  degreeModelClosure_mono hmodel h

/-- An equation separating the target from all exact degree vectors
certifies a border lower bound. Conversely every failed border bound gives
such a polynomial equation over the algebraic closure. -/
theorem not_degreeBorderAtMost_iff
    (model : ℕ → MvPolynomial σ (AlgebraicClosure F) → Prop) (d s : ℕ)
    (f : MvPolynomial σ F) :
    ¬ DegreeBorderAtMost model d s f ↔
      ∃ q : MvPolynomial (Computability.BorderVNP.DegreeMonomial σ d) (AlgebraicClosure F),
        (∀ g, model s g → eval (Computability.BorderVNP.coeffVector d g) q = 0) ∧
        eval (Computability.BorderVNP.coeffVector d (map (algebraMap F (AlgebraicClosure F)) f)) q ≠ 0 := by
  classical
  simp only [DegreeBorderAtMost, degreeModelClosure, Computability.BorderVNP.imageClosure, Set.mem_ofPred_eq,
    Set.forall_mem_image, not_forall]
  constructor
  · rintro ⟨q, hq, hx⟩
    exact ⟨q, fun g hg => hq hg, hx⟩
  · rintro ⟨q, hq, hx⟩
    exact ⟨q, fun {g} hg => hq g hg, hx⟩

end Hierarchy

end OAI
