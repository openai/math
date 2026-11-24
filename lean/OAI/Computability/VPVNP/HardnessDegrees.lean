import OAI.Computability.VPVNP.CircuitGrammar
import OAI.Computability.VPVNP.PolynomialBounds

/-!
# Assembling the homogeneous parse layers

The graded grammar of §8.1 represents the positive-degree pieces of a circuit.
Its scalar output at degree zero must also be retained when expanding a general
VNP witness summand. The number of grammar states uses the variables and the
binary gates of the exact circuit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Hardness

open MvPolynomial
open scoped Classical

variable {V : Type*} {F : Type*} [Field F]

/-- The constant term plus all positive homogeneous components recover the formal polynomial. -/
theorem eq_constant_add_positive_components (p : MvPolynomial V F) :
    p = C p.constantCoeff +
      ∑ d : Fin p.totalDegree, homogeneousComponent (d.val + 1) p := by
  rw [Fin.sum_univ_eq_sum_range (fun i => homogeneousComponent (i + 1) p), add_comm]
  simpa only [Finset.sum_range_succ', homogeneousComponent_zero, constantCoeff_eq]
    using (sum_homogeneousComponent p).symm

variable [Fintype V]

/-- Choose a single table of labels from an exact circuit of minimum size. -/
noncomputable def grammarFor (p : MvPolynomial V F) :
    ParseGrammar F V (Circuit.GrammarSlots V (circuitSize p)) p.totalDegree :=
  ((circuitSize_spec p).choose.exists_parseGrammar p.totalDegree).choose

theorem eval_grammarFor (p : MvPolynomial V F) (d : Fin p.totalDegree) :
    (grammarFor p).eval d none = homogeneousComponent (d.val + 1) p := by
  rw [grammarFor, ((circuitSize_spec p).choose.exists_parseGrammar p.totalDegree).choose_spec d,
    (circuitSize_spec p).choose_spec]

theorem polynomial_eq_constant_add_grammar (p : MvPolynomial V F) :
    p = C p.constantCoeff + ∑ d : Fin p.totalDegree, (grammarFor p).eval d none := by
  simp only [eval_grammarFor]
  exact eq_constant_add_positive_components p

variable {X W : Type} [Fintype X] [Fintype W]

/-- Under witness specialization, a leaf either contributes a visible variable or
the field constant zero or one selected by the witness bit. -/
noncomputable def leafValue (y : W → Bool) : X ⊕ W → MvPolynomial X F :=
  Sum.elim MvPolynomial.X (fun i => C (if y i then 1 else 0))

/-- The exact specialization at any witness, as a sum of scalar-weighted ordered parses. -/
theorem witnessValue_eq_constant_add_parses (p : MvPolynomial (X ⊕ W) F) (y : W → Bool) :
    witnessValue y p = C p.constantCoeff + ∑ d : Fin p.totalDegree,
      ∑ t : ParseGrammar.OrderedParse (X ⊕ W) (Circuit.GrammarSlots (X ⊕ W) (circuitSize p)) d.val,
        C ((grammarFor p).weight d none t) * (t.leaves.map (leafValue y)).prod := by
  conv_lhs => rw [polynomial_eq_constant_add_grammar p]
  rw [map_add, map_sum]
  simp only [witnessValue, eval₂Hom_C]
  apply congrArg (_ + ·)
  apply Finset.sum_congr rfl
  intro d _
  exact (grammarFor p).eval₂_eq_sum C (leafValue y) d none

/-- A VP summand supplies polynomial bounds on both the number of positive layers
and the number of states, even when the intermediate circuit degrees are much larger. -/
theorem grammar_bounds_of_isVP {σ : ℕ → Type} [∀ n, Fintype (σ n)]
    {p : Family F σ} (hp : IsVP p) :
    PolynomiallyBounded (fun n => (p n).totalDegree) ∧
    PolynomiallyBounded (fun n => Fintype.card (Circuit.GrammarSlots (σ n) (circuitSize (p n)))) := by
  refine ⟨hp.1.2, ?_⟩
  simp only [Circuit.card_grammarSlots]
  exact (hp.1.1.add hp.2).add (.const 1)

end Hardness

end VPVNP
end Computability
end OAI
