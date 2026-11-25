import OAI.Computability.BorderVNP.Model
import OAI.Computability.VPVNP.CircuitGrammar
import OAI.Computability.VPVNP.GrammarSize
import OAI.Computability.VPVNP.ParseHistogram

/-! # The integral coefficient map of Lemma 2.2

The same table describes every degree-`k + 1` coefficient, including monomials with
repeated variables. The number of states accommodates every shared circuit of size at
most the gate bound. Each coordinate is a sum of the parameter monomials of its parses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseTable

open MvPolynomial VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {V H : Type*} [Fintype V] [Fintype H]

/-- A full output coordinate of a universal integral grammar. -/
noncomputable def coordinate {n : ℕ} (d : Fin n) (h : H) (e : V →₀ ℕ) :
    MvPolynomial (GrammarLabel V H n) ℤ :=
  ((universalGrammar V H n).eval d h).coeff e

/-- Every coefficient polynomial has degree at most the number of nodes in its parses. -/
theorem coordinate_degree {n : ℕ} (d : Fin n) (h : H) (e : V →₀ ℕ) :
    (coordinate d h e).totalDegree ≤ 2 * d.val + 1 :=
  (universalGrammar_coeff_isHomogeneous d h e).totalDegree_le

/-- Every parse with the requested leaf exponents contributes exactly its label monomial. -/
theorem coordinate_eq_sum {n : ℕ} (d : Fin n) (h : H) (e : V →₀ ℕ) :
    coordinate d h e =
      ∑ p : OrderedParse V H d.val,
        if (p.leaves.map (fun i => Finsupp.single i 1)).sum = e then
          monomial (histogram d h p) (1 : ℤ) else 0 := by
  classical
  rw [coordinate, eval_eq_sum, coeff_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coeff_C_mul, list_prod_X_eq_monomial, coeff_monomial, universalGrammar_weight_eq_histogram]
  split_ifs <;> simp_all

/-- The coefficients count parses, so their absolute values sum to at most the number of
labelled parse trees. This gives the logarithmic coefficient norm bound in Lemma 2.2. -/
theorem coordinate_norm_le {n : ℕ} (d : Fin n) (h : H) (e : V →₀ ℕ) :
    ∑ a ∈ (coordinate d h e).support, |(coordinate d h e).coeff a| ≤
      ((4 ^ d.val * Fintype.card H ^ (2 * d.val) * Fintype.card V ^ (d.val + 1) : ℕ) : ℤ) := by
  classical
  have hpos (a) : 0 ≤ (coordinate d h e).coeff a := by
    rw [coordinate_eq_sum, coeff_sum]
    apply Finset.sum_nonneg
    intro p _
    split_ifs <;> simp [coeff_monomial, apply_ite]
  have hval : (eval (fun _ => (1 : ℤ))) (coordinate d h e) =
      ∑ a ∈ (coordinate d h e).support, |(coordinate d h e).coeff a| := by
    simp [eval_eq, abs_of_nonneg (hpos _)]
  rw [← hval, coordinate_eq_sum, map_sum]
  calc
    _ ≤ ∑ _ : OrderedParse V H d.val, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro p _
      split_ifs <;> simp [eval_monomial]
    _ ≤ _ := by simpa using (Int.ofNat_le.mpr (card_orderedParse_le V H d.val))

/-- Number of states for a table accepting circuits with at most `s` gates. -/
abbrev State (V : Type*) [Fintype V] (s : ℕ) := Fin (Fintype.card V + s + 1)

/-- The simultaneous polynomial map to all degree-`k + 1` coefficients. -/
noncomputable def table (V : Type*) [Fintype V] (k s : ℕ) (e : DegreeMonomial V (k + 1)) :
    MvPolynomial (GrammarLabel V (State V s) (k + 1)) ℤ :=
  coordinate (Fin.last k) (0 : State V s) e.val

/-- The table uses polynomially many parameters in the arity, size and output degree. -/
theorem parameter_count_le (V : Type*) [Fintype V] (k s : ℕ) :
    Fintype.card (GrammarLabel V (State V s) (k + 1)) ≤
      (Fintype.card V + s + 1) * Fintype.card V +
        (k + 1) ^ 2 * (Fintype.card V + s + 1) ^ 3 := by
  simpa only [State, Fintype.card_fin] using card_grammarLabel_le V (State V s) (k + 1)

/-- Every degree-component vector attainable with at most `s` gates has one simultaneous
parameter assignment to the universal table. This includes circuits with arbitrary constants. -/
theorem circuitImage_subset {K : Type*} [Field K] (V : Type*) [Fintype V] (k s : ℕ) :
    circuitImage K V (k + 1) s ⊆
      Set.range (fun v : GrammarLabel V (State V s) (k + 1) → K =>
        fun e => eval₂ (Int.castRingHom K) v (table V k s e)) := by
  rintro y ⟨m, hm, c, rfl⟩
  obtain ⟨g, hg⟩ := c.exists_parseGrammar_fin (k + 1) (Fintype.card V + s + 1) (by omega)
  refine ⟨g.labelValue, funext fun e => ?_⟩
  change g.specializeLabels (((universalGrammar V (State V s) (k+1)).eval (Fin.last k) 0).coeff e.val)
    = c.polynomial.coeff e.val
  rw [g.specialize_coefficient]
  have h : g.eval (Fin.last k) 0 = homogeneousComponent (k + 1) c.polynomial :=
    hg (Fin.last k)
  exact (congrArg (fun p : MvPolynomial V K => p.coeff e.val) h).trans
    (congrFun (coeffVector_homogeneousComponent (k + 1) c.polynomial) e)

/-- A border-size bound places the whole coefficient vector in the table's image closure. -/
theorem geometricApprox_mem_tableClosure {K : Type*} [Field K] (V : Type*) [Fintype V]
    {k s : ℕ} {p : MvPolynomial V K} (hp : geometricApprox (k + 1) s p) :
    coeffVector (k + 1) p ∈ imageClosure (Set.range
      (fun v : GrammarLabel V (State V s) (k + 1) → K =>
        fun e => eval₂ (Int.castRingHom K) v (table V k s e))) :=
  imageClosure_mono (circuitImage_subset V k s) hp

end ParseTable

end BorderVNP
end Computability
end OAI
