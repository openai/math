import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # The graph used for effective Nullstellensatz certificates

When the equations `F i` have no common zero, the functions `x_j` and
`t * F i` generate the polynomial algebra in `x,t`. A linear Noether
normalization of this generating system keeps each normalized coordinate
linear in `t` and of bounded total degree. This is the graph construction
of Jelonek's proof of the effective Nullstellensatz, specialized to affine
space.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate

open MvPolynomial

variable {E I : Type*} [Field E] {n : ℕ}

/-- The original coordinates and the equation values multiplied by an extra variable. -/
noncomputable def graphGenerator (F : I → MvPolynomial (Fin n) E) :
    Fin n ⊕ I → MvPolynomial (Fin (n+1)) E
  | .inl j => X j.succ
  | .inr i => X 0 * rename Fin.succ (F i)

/-- Qualitative Nullstellensatz gives a certificate before any degree bound is imposed. -/
theorem exists_certificate_of_inconsistent [IsAlgClosed E] [Fintype I]
    (F : I → MvPolynomial (Fin n) E) (hno : ¬ ∃ x : Fin n → E, ∀ i, eval x (F i) = 0) :
    ∃ A : I → MvPolynomial (Fin n) E, ∑ i, A i * F i = 1 := by
  let J := Ideal.span (Set.range F)
  have hzero : zeroLocus E J = ∅ := by
    rw [zeroLocus_span]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply hno
    exact ⟨x, fun i => by simpa only [aeval_eq_eval] using hx (F i) ⟨i, rfl⟩⟩
  have hrad : (1 : MvPolynomial (Fin n) E) ∈ J.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := E), hzero]
    intro x hx
    exact False.elim hx
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hrad
  exact Ideal.mem_span_range_iff_exists_fun.mp (by simpa using hm : 1 ∈ J)

/-- The graph functions generate the full polynomial algebra if the system is inconsistent. -/
theorem graphGenerator_adjoin [IsAlgClosed E] [Fintype I] (F : I → MvPolynomial (Fin n) E)
    (hno : ¬ ∃ x : Fin n → E, ∀ i, eval x (F i) = 0) :
    Algebra.adjoin E (Set.range (graphGenerator F)) = ⊤ := by
  let S := Algebra.adjoin E (Set.range (graphGenerator F))
  have gen (i : Fin n ⊕ I) : graphGenerator F i ∈ S :=
    Algebra.subset_adjoin ⟨i, rfl⟩
  have hrename (p : MvPolynomial (Fin n) E) : rename Fin.succ p ∈ S := by
    induction p using MvPolynomial.induction_on with
    | C c => simpa using S.algebraMap_mem c
    | add p q hp hq => simpa using S.add_mem hp hq
    | mul_X p j hp => simpa [graphGenerator] using S.mul_mem hp (gen (.inl j))
  obtain ⟨u, hu⟩ := exists_certificate_of_inconsistent F hno
  have ht : X (0 : Fin (n+1)) ∈ S := by
    have h := congrArg (fun p => X (0 : Fin (n+1)) * rename Fin.succ p) hu
    simp only [map_sum, map_mul, map_one, mul_one, Finset.mul_sum] at h
    rw [← h]
    apply S.sum_mem
    intro i _
    simpa only [graphGenerator, mul_left_comm] using S.mul_mem (hrename (u i)) (gen (.inr i))
  apply top_unique
  rw [← adjoin_range_X (σ := Fin (n+1)) (R := E)]
  apply Algebra.adjoin_le
  rintro _ ⟨j, rfl⟩
  exact Fin.cases ht (fun i => gen (.inl i)) j

/-- Every linear combination of the graph functions has the displayed affine-in-`t` form. -/
theorem graphGenerator_span_decompose [Fintype I] (F : I → MvPolynomial (Fin n) E)
    {q : MvPolynomial (Fin (n+1)) E} (hq : q ∈ Submodule.span E (Set.range (graphGenerator F))) :
    ∃ (l : Fin n → E) (c : I → E), q = (∑ j, C (l j) * X j.succ) +
      X 0 * ∑ i, C (c i) * rename Fin.succ (F i) := by
  obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hq
  refine ⟨fun j => v (.inl j), fun i => v (.inr i), ?_⟩
  rw [← hv, Fintype.sum_sum_type, Finset.mul_sum]
  simp only [graphGenerator, smul_eq_C_mul, mul_left_comm]

/-- Normalization by linear combinations increases the equation degree by at most one. -/
theorem graphGenerator_span_degree [Fintype I] (F : I → MvPolynomial (Fin n) E) {D : ℕ}
    (hF : ∀ i, (F i).totalDegree ≤ D) {q : MvPolynomial (Fin (n+1)) E}
    (hq : q ∈ Submodule.span E (Set.range (graphGenerator F))) : q.totalDegree ≤ D + 1 := by
  obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hq
  rw [← hv]
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_smul_le ..).trans
  cases i with
  | inl j => simp [graphGenerator]
  | inr i =>
    apply (totalDegree_mul ..).trans
    have h := (totalDegree_rename_le Fin.succ (F i)).trans (hF i)
    rw [totalDegree_X]
    omega

end RadicalCertificate

end VPVNP
end Computability
end OAI
