import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.BigOperators

/-!
# The two pin indices in the border diagonal

In equations (11.1)–(11.3) the polynomial obtained by substitution is indexed
by a row. The live input selects a column. The regularity test is applied to
the sum over all contraction assignments in a row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open MvPolynomial
open scoped BigOperators Classical

section Substitution

variable {Query Wire Proc : Type*} [Fintype Wire] [Fintype Proc]

/-- The polynomial `F_I` of (11.1). A shared physical wire has one Boolean
assignment in the outer sum, regardless of its number of processor uses. -/
noncomputable def queryPolynomial (k : Type*) [CommSemiring k]
    (query : (Wire → Bool) → Proc → Query) : MvPolynomial Query k := by
  classical
  exact ∑ links, ∏ proc, X (query links proc)

/-- Specializing the query variables at the live coefficient vector gives
the contraction with one factor per processor. -/
theorem eval_queryPolynomial {k : Type*} [CommSemiring k]
    (query : (Wire → Bool) → Proc → Query) (c : Query → k) :
    eval c (queryPolynomial k query) = ∑ links, ∏ proc, c (query links proc) := by
  classical
  simp [queryPolynomial]

/-- Substituting the full polynomial table for each queried coefficient gives
the contraction `A_I` over the parameter ring, before taking a boundary value. -/
theorem substitute_queryPolynomial {k E Param : Type*} [CommSemiring k] [CommSemiring E]
    (base : k →+* E) (Y : Query → MvPolynomial Param E)
    (query : (Wire → Bool) → Proc → Query) :
    eval₂Hom (C.comp base) Y (queryPolynomial k query) =
      ∑ links, ∏ proc, Y (query links proc) := by
  classical
  simp [queryPolynomial]

end Substitution

section Rows

variable {Param I k E : Type*} [CommRing k] [CommSemiring E]

/-- Apply the residue matrix for each monomial and add the entries at a
fixed pair of pins. Only additivity in the gadget coefficient is required. -/
noncomputable def pinEntry (W : (Param →₀ ℕ) → I → I → E →+ k) (i h : I) :
    MvPolynomial Param E →+ k :=
  (Finsupp.liftAddHom fun μ => W μ i h).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

/-- One assigned term contributes its own residue-matrix entry. -/
@[simp] theorem pinEntry_monomial (W : (Param →₀ ℕ) → I → I → E →+ k)
    (i h : I) (μ : Param →₀ ℕ) (a : E) :
    pinEntry W i h (monomial μ a) = W μ i h a :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- The entry of the whole polynomial is the coefficient-weighted sum from
equation (10.1), even if a coefficient arises by cancellation of assignments. -/
theorem pinEntry_eq_support_sum (W : (Param →₀ ℕ) → I → I → E →+ k)
    (i h : I) (A : MvPolynomial Param E) :
    pinEntry W i h A = ∑ μ ∈ A.support, W μ i h (A.coeff μ) := by
  nth_rw 1 [A.as_sum]
  simp only [map_sum, pinEntry_monomial]

variable [Fintype I]

/-- Pair the live column equation with the residue vector and use the
substituted row equations. The extra branch would force its chosen nonzero
residue coordinate to vanish. This holds also in characteristic two. -/
theorem incompatible_pin_equations [DecidableEq I] (hstar : I) (Ω Z : I → k)
    (K : I → I → k) (hnonzero : Ω hstar ≠ 0)
    (hrow : ∀ i, ∑ h, K i h * Ω h = Z i * Ω i)
    (hcol : ∀ h, Z h = (if h = hstar then 1 else 0) + ∑ i, K i h) : False := by
  have htotal :
      (∑ h, Z h * Ω h) = Ω hstar + ∑ i, Z i * Ω i := by
    calc
      (∑ h, Z h * Ω h) =
          ∑ h, ((if h = hstar then 1 else 0) + ∑ i, K i h) * Ω h := by
            simp_rw [← hcol]
      _ = (∑ h, (if h = hstar then (1 : k) else 0) * Ω h) +
          ∑ h, ∑ i, K i h * Ω h := by
            simp only [add_mul, Finset.sum_mul, Finset.sum_add_distrib]
      _ = Ω hstar + ∑ i, ∑ h, K i h * Ω h := by
            congr 1
            · simp [ite_mul]
            · exact Finset.sum_comm
      _ = Ω hstar + ∑ i, Z i * Ω i := by simp_rw [hrow]
  exact hnonzero ((add_eq_right.mp htotal.symm))

/-- In (11.3) the evaluator guesses one expansion assignment and evaluates
one matrix entry. Additivity converts this path sum into the column equation
for the same row polynomials tested by (10.1). -/
theorem incompatible_assignment_evaluator [DecidableEq I] {Path : I → Type*}
    [∀ i, Fintype (Path i)] (W : (Param →₀ ℕ) → I → I → E →+ k)
    (hstar : I) (Ω Z : I → k) (hnonzero : Ω hstar ≠ 0)
    (A : I → MvPolynomial Param E)
    (μ : ∀ i, Path i → Param →₀ ℕ) (a : ∀ i, Path i → E)
    (hexpand : ∀ i, A i = ∑ e, monomial (μ i e) (a i e))
    (hresidue : ∀ i, ∑ h, pinEntry W i h (A i) * Ω h = Z i * Ω i)
    (hlive : ∀ h, Z h = (if h = hstar then 1 else 0) + ∑ i, ∑ e, W (μ i e) i h (a i e)) :
    False := by
  apply incompatible_pin_equations hstar Ω Z (fun i h => pinEntry W i h (A i)) hnonzero hresidue
  intro h
  simpa only [hexpand, map_sum, pinEntry_monomial] using hlive h

end Rows

end Diagonal

end BorderVNP
end Computability
end OAI
