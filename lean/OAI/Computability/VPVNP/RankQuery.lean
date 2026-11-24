import OAI.Computability.VPVNP.GreedyBasis
import OAI.Computability.VPVNP.RankMinors
import OAI.Computability.VPVNP.RankPolynomial

/-!
# Recovering rank from a weighted determinant

Appendix D.2 uses the degree in `u` of `det(1 - u D₁(z) M D₂(z) Mᵀ)` to
query the rank of a rectangular matrix. At the rank, every nonzero minor
comes from a row basis and a column basis. The first basis of each kind has
strictly smaller total index weight than any other. Its squared minor
therefore supplies an isolated nonzero coefficient in `z`, in every
characteristic.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

open Set VPVNP.Crossing
open Polynomial

/-- A unique nonzero summand at a specified weight prevents cancellation,
including over fields of characteristic two. -/
private theorem weight_sum_nonzero
    {F Row Col : Type*} [Field F] [Fintype Row] [Fintype Col]
    (rowWt : Row → ℕ) (colWt : Col → ℕ) (a : Row → Col → F) (r : Row) (c : Col)
    (hval : a r c ≠ 0)
    (huniq : ∀ i j, a i j ≠ 0 → rowWt i + colWt j = rowWt r + colWt c → i = r ∧ j = c) :
    (∑ i, ∑ j, X ^ (rowWt i + colWt j) * C (a i j) ^ 2 : F[X]) ≠ 0 := by
  classical
  intro hz
  have hc := congrArg (fun P : F[X] => P.coeff (rowWt r + colWt c)) hz
  simp only [finsetSum_coeff, coeff_zero, ← map_pow, mul_comm (X ^ _) (C _),
    coeff_C_mul_X_pow] at hc
  have hentry (i : Row) (j : Col) (h : i ≠ r ∨ j ≠ c) :
      (if rowWt r + colWt c = rowWt i + colWt j then a i j ^ 2 else 0) = 0 := by
    split_ifs with he
    · by_contra hne
      have hn : a i j ≠ 0 := fun ha => hne (by simp [ha])
      have hij := huniq i j hn he.symm
      exact h.elim (fun hi => hi hij.1) (fun hj => hj hij.2)
    · rfl
  have hi (i : Row) (hi : i ≠ r) :
      (∑ j, if rowWt r + colWt c = rowWt i + colWt j then a i j ^ 2 else 0) = 0 :=
    Finset.sum_eq_zero (fun j _ => hentry i j (.inl hi))
  rw [Fintype.sum_eq_single r hi, Fintype.sum_eq_single c (fun j hj => hentry r j (.inr hj)),
    ite_eq_left rfl] at hc
  exact pow_ne_zero _ hval hc

/-- At maximum rank the term indexed by the first row and column bases has a
unique weight among all nonzero terms in the minor expansion. -/
theorem isolated_maximal_minor {K : Type*} [Field K] {n m : ℕ} (M : Matrix (Fin n) (Fin m) K) :
    ∃ (R : powersetCard (Fin n) M.rank) (C : powersetCard (Fin m) M.rank),
      compound M.rank M R C ≠ 0 ∧
      ∀ I J, compound M.rank M I J ≠ 0 →
        indexWeight I + indexWeight J = indexWeight R + indexWeight C → I = R ∧ J = C := by
  obtain ⟨R, hr, _, hrow⟩ := exists_isolatedBasis K M.row M.rank_eq_finrank_span_row
  obtain ⟨C, hc, _, hcol⟩ := exists_isolatedBasis K M.col M.rank_eq_finrank_span_cols
  refine ⟨R, C, (compound_ne_zero_iff M rfl R C).mpr ⟨hr, hc⟩, ?_⟩
  intro I J hminor hw
  obtain ⟨hi, hj⟩ := (compound_ne_zero_iff M rfl I J).mp hminor
  have hR (hne : R ≠ I) : indexWeight R < indexWeight I := hrow I hi hne
  have hC (hne : C ≠ J) : indexWeight C < indexWeight J := hcol J hj hne
  by_cases heq : R = I
  · subst I
    refine ⟨rfl, ?_⟩
    by_contra hn
    exact (hC (Ne.symm hn)).ne (Nat.add_left_cancel hw).symm
  · have hlt := hR heq
    by_cases heq' : C = J
    · subst J
      omega
    · have hlt' := hC heq'
      omega

/-- The determinant rank test of Appendix D.2, including characteristic two
and matrices with zero rows, zero columns, or rank zero. -/
theorem rankPolynomial_natDegree {K : Type*} [Field K] {n m : ℕ} (M : Matrix (Fin n) (Fin m) K) :
    (rankPolynomial M).natDegree = M.rank := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro q hq
    rw [rankPolynomial_coeff]
    simp [compound_eq_zero_of_rank_lt M hq]
  · obtain ⟨R, C, hval, huniq⟩ := isolated_maximal_minor M
    rw [rankPolynomial_coeff]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (weight_sum_nonzero indexWeight indexWeight (compound M.rank M) R C hval huniq)

end RankQuery

end VPVNP
end Computability
end OAI
