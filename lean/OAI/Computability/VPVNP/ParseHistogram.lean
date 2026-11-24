import OAI.Computability.VPVNP.GrammarLabels
import OAI.Computability.VPVNP.ParseQuery

/-!
# Production histograms for ordered grammar parses

In §§8.1 and 9.3 of *VP and VNP differ over every field*, each occurrence of a production
adds one to its label's exponent. The paired-word coefficient counts an ordered tree
together with a bijection from its leaves to the positions of the queried word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

open MvPolynomial

variable {V H : Type*} {n m : ℕ}

/-- The exponent of each terminal or binary production label in a given ordered parse. -/
noncomputable def histogram (d : Fin n) (h : H) (p : OrderedParse V H d.val) :
    GrammarLabel V H n →₀ ℕ :=
  match d, p with
  | ⟨0, _⟩, .leaf v => Finsupp.single (.inl (h, v)) 1
  | ⟨k + 1, hk⟩, .node b i j left right =>
    Finsupp.single (.inr ⟨⟨k + 1, hk⟩, h, b, i, j⟩) 1 +
      histogram (leftDegree ⟨k + 1, hk⟩ b) i left +
      histogram (rightDegree ⟨k + 1, hk⟩ b) j right
termination_by d.val
decreasing_by
  all_goals first | exact leftDegree_lt _ _ | exact rightDegree_lt _ _

/-- Every occurrence contributes its own label, and multiplication adds the occurrences. -/
theorem universalGrammar_weight_eq_histogram (d : Fin n) (h : H) (p : OrderedParse V H d.val) :
    (universalGrammar V H n).weight d h p = monomial (histogram d h p) (1 : ℤ) := by
  induction d using (measure (fun d : Fin n => d.val)).wf.induction generalizing h with
  | h d ih =>
    obtain ⟨k, hk⟩ := d
    cases k with
    | zero =>
      cases p with
      | leaf v =>
        rw [histogram, weight_leaf]
        rfl
    | succ k =>
      cases p with
      | node b i j l r =>
        let d : Fin n := ⟨k + 1, hk⟩
        rw [histogram, weight_node,
          ih (leftDegree d b) (leftDegree_lt d b) i l,
          ih (rightDegree d b) (rightDegree_lt d b) j r]
        simp [universalGrammar, X, d]

/-- A parse with `d.val + 1` leaves uses `d.val` internal labels and one terminal label per leaf. -/
theorem histogram_degree (d : Fin n) (h : H) (p : OrderedParse V H d.val) :
    (histogram d h p).degree = 2 * d.val + 1 := by
  classical
  have hom := universalGrammar_weight_isHomogeneous d h p
  rw [universalGrammar_weight_eq_histogram] at hom
  apply (hom.degree_eq_sum_deg_support (s := histogram d h p) ?_).symm
  simp

theorem histogram_sum [Fintype V] [Fintype H] (d : Fin n) (h : H) (p : OrderedParse V H d.val) :
    ∑ label, histogram d h p label = 2 * d.val + 1 := by
  rw [← Finsupp.degree_eq_sum, histogram_degree]

/-- One of the choices counted in the coefficient query, retaining the ordered tree
and its bijective assignment to the paired bit positions. -/
abbrev ParseChoice (H : Type*) (d : Fin n) (x : Fin m → Bool) :=
  Σ p : OrderedParse (Fin m × Bool) H d.val, LeafBijection p.leaves (fun i => (i, x i))

/-- The query polynomial `Bₓ` is the integer sum of the histogram monomials of its parses. -/
theorem labelQuery_eq_sum_histogram [Fintype H] (d : Fin n) (h : H) (x : Fin m → Bool) :
    labelQuery d h x = ∑ a : ParseChoice H d x, monomial (histogram d h a.1) 1 := by
  rw [labelQuery, coeff_eval_paired_bijections, Fintype.sum_sigma]
  simp_rw [universalGrammar_weight_eq_histogram]

end ParseGrammar

end VPVNP
end Computability
end OAI
