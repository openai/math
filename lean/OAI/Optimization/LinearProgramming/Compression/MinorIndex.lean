import OAI.Optimization.LinearProgramming.Compression.Bound
import OAI.Optimization.LinearProgramming.Compression.Counting
import OAI.Optimization.LinearProgramming.Compression.Separation
import Mathlib.Data.Fintype.Pi

/-! The determinant counting bound for the actual minor requests of the two input matrices. -/

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

variable {R : Type*} [CommRing R] {rD rE N : ℕ}

/-- The compression oracle is queried only for minors with nonzero determinant. -/
abbrev NonzeroPairMinor (D : Matrix (Fin rD) (Fin N) R) (E : Matrix (Fin rE) (Fin N) R) :=
  {u : PairMinorIndex rD rE N // pairMinorValue D E u ≠ 0}

/-- All candidate minor indices, including the empty minor, form a finite universe. -/
theorem finite_nonzeroPairMinor (D : Matrix (Fin rD) (Fin N) R) (E : Matrix (Fin rE) (Fin N) R) :
    Finite (NonzeroPairMinor D E) := by
  classical
  infer_instance

/-- Lemma 3.1 for any indexing of actual minors. The true logarithms are defined
using a real embedding of the input ring, which includes both rational and real inputs. -/
theorem dissociated_minor_card_le {ι : Type*}
    (D : Matrix (Fin rD) (Fin N) R) (E : Matrix (Fin rE) (Fin N) R)
    (hN : 1 ≤ N) (hrows : rD + rE = N) (v : R →+* ℝ)
    (minor : ι → PairMinorIndex rD rE N) (J : Finset ι) (l : ι → ℝ)
    (hn : ∀ i ∈ J, v (pairMinorValue D E (minor i)) ≠ 0)
    (herr : ∀ i ∈ J, |l i - Real.logb 2 (|v (pairMinorValue D E (minor i))|)| ≤
      1 / 2 ^ (100 * (N + 1)^3 + 7 : ℕ))
    (hd : IsDissociated l J) :
    (J.card : ℝ) ≤ (7 * (N : ℝ)^2 + 8) * Real.logb 2 (N + 1) := by
  classical
  apply log_bound_of_subset_counts hN J
  intro t ht hcard
  let η : ℝ := 1 / 2 ^ (100 * (N + 1)^3 + 7 : ℕ)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hc : (t.card : ℝ) ≤ ((N : ℝ) + 1)^6 := by exact_mod_cast hcard
  have hsmall : (t.card : ℝ) * η ≤ 1 := by
    have h₁ := mul_le_mul_of_nonneg_right hc hη
    have h₂ : 4 * ((N : ℝ) + 1)^6 * η ≤ 1 := proxy_error_at_cutoff N
    have h₃ : 0 ≤ ((N : ℝ) + 1)^6 * η := mul_nonneg (by positivity) hη
    linarith
  have hi := dissociated_subsetProduct_subsetSum_injOn (hd.mono ht) hη hsmall
    (fun i hit => hn i (ht hit)) (fun i hit => herr i (ht hit))
  rw [← card_pairVariable hrows]
  let ev := v.comp (MvPolynomial.eval₂Hom (Int.castRingHom R) (pairValuation D E))
  apply subset_product_count_of_mass t (fun i => pairMinorPolynomial (minor i)) ev N N.factorial
    (Nat.factorial_pos N) (fun i _ => totalDegree_pairMinorPolynomial_le (minor i))
    (fun i _ => coeffMass_pairMinorPolynomial_le (minor i))
  simpa only [ev, RingHom.comp_apply, eval_pairMinorPolynomial] using hi

/-- The paper's determinant-indexed dissociation bound with no nonzero side condition
on the set: admissibility is intrinsic to each minor request. -/
theorem dissociated_nonzeroPairMinor_card_le
    (D : Matrix (Fin rD) (Fin N) R) (E : Matrix (Fin rE) (Fin N) R)
    (hN : 1 ≤ N) (hrows : rD + rE = N) (v : R →+* ℝ) (hv : Function.Injective v)
    (J : Finset (NonzeroPairMinor D E)) (l : NonzeroPairMinor D E → ℝ)
    (herr : ∀ i ∈ J, |l i - Real.logb 2 (|v (pairMinorValue D E i.val)|)| ≤
      1 / 2 ^ (100 * (N + 1)^3 + 7 : ℕ))
    (hd : IsDissociated l J) :
    (J.card : ℝ) ≤ (7 * (N : ℝ)^2 + 8) * Real.logb 2 (N + 1) := by
  apply dissociated_minor_card_le D E hN hrows v Subtype.val J l _ herr hd
  intro i _
  exact fun h => i.property (hv (h.trans v.map_zero.symm))

end Compression
end LinearProgramming
end Optimization
end OAI
