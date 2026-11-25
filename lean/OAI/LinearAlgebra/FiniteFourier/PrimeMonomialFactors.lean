import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! # Bounded-degree polynomials as sums of fixed-length products -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open MvPolynomial
noncomputable section

variable {K σ : Type*} [CommRing K] [Nontrivial K]

/-- Including a scalar in one factor and padding by ones gives exactly `b`
affine factors even for constant terms and monomials of degree exactly `b`. -/
theorem monomial_eq_prod_affine {d : σ →₀ ℕ} (c : K) {b : ℕ} (hb : 0 < b)
    (hd : d.sum (fun _ n => n) ≤ b) :
    ∃ f : Fin b → MvPolynomial σ K, (∀ i, (f i).totalDegree ≤ 1) ∧ monomial d c = ∏ i, f i := by
  classical
  have aux (m : Multiset σ) : ∀ n : ℕ, 0 < n → m.card ≤ n →
      ∃ f : Fin n → MvPolynomial σ K, (∀ i, (f i).totalDegree ≤ 1) ∧
        monomial m.toFinsupp c = ∏ i, f i := by
    induction m using Multiset.induction_on with
    | empty =>
      intro n hn _
      let j : Fin n := ⟨0, hn⟩
      refine ⟨fun i => if j = i then C c else 1, ?_, ?_⟩
      · intro i
        by_cases hi : j = i <;> simp [hi]
      · simp [Multiset.toFinsupp_zero, ← C_apply]
    | cons a m ih =>
      rintro (_ | n) hn hm
      · omega
      by_cases hn0 : n = 0
      · subst n
        refine ⟨fun _ => monomial (a ::ₘ m).toFinsupp c, ?_, by simp⟩
        intro _
        apply (totalDegree_monomial_le _ _).trans
        simpa only [← Finsupp.card_toMultiset, Multiset.toFinsupp_toMultiset] using hm
      · obtain ⟨f, hdeg, hf⟩ := ih n (Nat.pos_of_ne_zero hn0) (by simpa using hm)
        refine ⟨Fin.cons (X a) f, ?_, ?_⟩
        · intro i
          exact Fin.cases (by simp) (fun j => hdeg j) i
        · rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, ← hf]
          rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
            X, monomial_mul_monomial, one_mul]
  simpa only [Finsupp.toMultiset_toFinsupp] using aux d.toMultiset b hb
    (by simpa only [Finsupp.card_toMultiset, Function.id_def] using hd)

/-- A family of polynomials of bounded degree has factorizations with a common
number of product terms. A monomial absent from a polynomial receives coefficient zero. -/
theorem family_eq_sum_prod_affine {B : Type*} [Fintype B] (p : B → MvPolynomial σ K)
    {b : ℕ} (hb : 0 < b) (hp : ∀ v, (p v).totalDegree ≤ b) :
    ∃ (h : ℕ) (f : B → Fin h → Fin b → MvPolynomial σ K),
      (∀ v i j, (f v i j).totalDegree ≤ 1) ∧ ∀ v, p v = ∑ i, ∏ j, f v i j := by
  classical
  let S := Finset.univ.biUnion fun v => (p v).support
  let e := S.equivFin.symm
  have hd (i : Fin S.card) : (e i).val.sum (fun _ n => n) ≤ b := by
    obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp (e i).property
    exact (le_totalDegree hv).trans (hp v)
  choose f hdeg hf using fun v (i : Fin S.card) =>
    monomial_eq_prod_affine ((p v).coeff (e i).val) hb (hd i)
  refine ⟨_, f, hdeg, fun v => ?_⟩
  simp_rw [← hf]
  rw [e.sum_comp (fun t => monomial t.val ((p v).coeff t.val))]
  apply (p v).as_sum.trans
  apply Eq.trans _ (Finset.sum_attach S (fun t => monomial t ((p v).coeff t))).symm
  apply Finset.sum_subset (Finset.subset_biUnion_of_mem _ (Finset.mem_univ v))
  intro d _ hd
  simp [notMem_support_iff.mp hd]

end

end FiniteFourier
end LinearAlgebra
end OAI
