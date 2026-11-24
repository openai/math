import OAI.Computability.VPVNP.VerifierSummand
import OAI.Computability.VPVNP.VerifierWeight

/-!
# Exact circuit and degree bounds for the §1.1 summand

The transcript check has eight arithmetic gates per Boolean gate, plus the
acceptance indicator. The selector product uses four operations per input bit
and one multiplication into the running product. All the bounds refer to the
unspecialized summand as a formal polynomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Verifier

open MvPolynomial

variable {R : Type*} [CommRing R] {n t g : ℕ}

private def selectorFormula (j : Fin n) : Formula R (Variables n t g) :=
  let x := Formula.var (Sum.inr (Sum.inl (Sum.inl j)))
  (((Formula.const 1).sub x).mul (.var (.inl (j, false)))).add (x.mul (.var (.inl (j, true))))

/-- Arithmetic formula for the unspecialized summand. -/
noncomputable def summandFormula (c : BooleanTranscript.Circuit (Inputs n t) g) :
    Formula R (Variables n t g) :=
  (c.weightFormula (fun i => .inr (.inl i)) (fun i => .inr (.inr i))).mul
    (Formula.prod selectorFormula)

theorem polynomial_summandFormula (c : BooleanTranscript.Circuit (Inputs n t) g) :
    (summandFormula (R := R) c).polynomial = summand c := by
  unfold summandFormula summand
  change _ * (Formula.prod _).polynomial = _
  rw [Formula.polynomial_prod]
  congr 1
  exact c.eval_weightFormula _ _ MvPolynomial.C MvPolynomial.X

theorem size_summandFormula_le (c : BooleanTranscript.Circuit (Inputs n t) g) :
    (summandFormula (R := R) c).size ≤ 8 * g + 5 * n + 2 := by
  have h := c.size_weightFormula_le (R := R)
    (fun i => Sum.inr (Sum.inl i) : Inputs n t → Variables n t g)
    (fun i => Sum.inr (Sum.inr i))
  simp [summandFormula, Formula.size, selectorFormula]
  omega

theorem degree_summandFormula_le (c : BooleanTranscript.Circuit (Inputs n t) g) :
    (summandFormula (R := R) c).degree ≤ 3 * g + 2 * n + 1 := by
  have h := c.degree_weightFormula_le (R := R)
    (fun i => Sum.inr (Sum.inl i) : Inputs n t → Variables n t g)
    (fun i => Sum.inr (Sum.inr i))
  simp [summandFormula, Formula.degree, selectorFormula]
  omega

theorem totalDegree_summand_le (c : BooleanTranscript.Circuit (Inputs n t) g) :
    (summand (R := R) c).totalDegree ≤ 3 * g + 2 * n + 1 := by
  rw [← polynomial_summandFormula]
  exact (Formula.totalDegree_le _).trans (degree_summandFormula_le _)

/-- The local checks and selectors admit an exact circuit over every coefficient ring. -/
theorem exists_circuit_summand (c : BooleanTranscript.Circuit (Inputs n t) g) :
    ∃ m ≤ 8 * g + 5 * n + 2, ∃ d : Circuit R (Variables n t g) m, d.polynomial = summand c :=
  ⟨_, size_summandFormula_le _, (summandFormula c).compile,
    (Formula.compile_polynomial _).trans (polynomial_summandFormula _)⟩

end Verifier

end VPVNP
end Computability
end OAI
