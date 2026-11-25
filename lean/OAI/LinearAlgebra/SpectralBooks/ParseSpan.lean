import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Homogeneous components of arithmetic circuits in the parse table

For each degree, expand linear dependencies between gates in topological order.
In degree one only variable inputs remain. In a higher degree only products of
positive-degree components of earlier registers remain.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial Finset.HasAntidiagonal

noncomputable section

variable {K σ : Type*} [CommRing K]

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- Multiplication of homogeneous components is convolution in the total degree. -/
theorem homogeneousComponent_product (d : ℕ) (f g : MvPolynomial σ K) :
    homogeneousComponent d (f * g) =
      ∑ uv ∈ antidiagonal d,
        homogeneousComponent uv.1 f * homogeneousComponent uv.2 g := by
  let A := homogeneousSubmodule σ K
  have h (x : MvPolynomial σ K) (j : ℕ) :
      (DirectSum.decompose A x j : MvPolynomial σ K) = homogeneousComponent j x :=
    MvPolynomial.decomposition.decompose'_apply x j
  rw [← h]
  rw [DirectSum.decompose_mul, DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  simp_rw [h]

/-- The generators admitted by `M` only need to involve registers older than the output.
In the program's register convention, the most recent register has index zero. -/
private theorem homogeneousComponent_register_mem {r d : ℕ} (p : Program K σ r) (o : Fin r)
    (hd : 0 < d) (M : Submodule K (MvPolynomial σ K))
    (hX : d = 1 → ∀ x : σ, X x ∈ M)
    (hprod : ∀ a b : Fin r, o < a → o < b → ∀ u v : ℕ, 0 < u → 0 < v → u + v = d →
      homogeneousComponent u (registerPolynomial p a) *
        homogeneousComponent v (registerPolynomial p b) ∈ M) :
    homogeneousComponent d (registerPolynomial p o) ∈ M := by
  induction p with
  | nil => exact o.elim0
  | @step r p gate ih =>
    refine Fin.cases (motive := fun o ↦ (∀ a b : Fin (r+1), o < a → o < b →
        ∀ u v : ℕ, 0 < u → 0 < v → u + v = d →
          homogeneousComponent u (registerPolynomial (p.step gate) a) *
            homogeneousComponent v (registerPolynomial (p.step gate) b) ∈ M) →
        homogeneousComponent d (registerPolynomial (p.step gate) o) ∈ M)
        ?_ (fun i hi ↦ ?_) o hprod
    · intro h
      have hprev (i : Fin r) : homogeneousComponent d (registerPolynomial p i) ∈ M :=
        ih i fun a b _ _ ↦ h a.succ b.succ (Fin.succ_pos _) (Fin.succ_pos _)
      rw [registerPolynomial_zero]
      cases gate with
      | constant z =>
        simp [gatePolynomial, homogeneousComponent_of_mem (isHomogeneous_C σ z), hd.ne']
      | input x =>
        by_cases h1 : d = 1
        · simpa [gatePolynomial, homogeneousComponent_of_mem (isHomogeneous_X K x), h1] using hX h1 x
        · simp [gatePolynomial, homogeneousComponent_of_mem (isHomogeneous_X K x), h1]
      | add i j => simpa only [gatePolynomial, map_add] using M.add_mem (hprev i) (hprev j)
      | sub i j => simpa only [gatePolynomial, map_sub] using M.sub_mem (hprev i) (hprev j)
      | mul i j =>
        simp only [gatePolynomial, homogeneousComponent_product]
        apply M.sum_mem
        rintro ⟨u, v⟩ huv
        have huv' : u + v = d := mem_antidiagonal.mp huv
        by_cases hu : u = 0
        · subst u
          simp only [zero_add] at huv'
          subst v
          simpa only [homogeneousComponent_zero, MvPolynomial.smul_eq_C_mul] using
            M.smul_mem ((registerPolynomial p i).coeff 0) (hprev j)
        by_cases hv : v = 0
        · subst v
          simp only [add_zero] at huv'
          subst u
          simpa only [homogeneousComponent_zero, MvPolynomial.smul_eq_C_mul, mul_comm] using
            M.smul_mem ((registerPolynomial p j).coeff 0) (hprev i)
        exact h i.succ j.succ (Fin.succ_pos _) (Fin.succ_pos _) u v
          (Nat.pos_of_ne_zero hu) (Nat.pos_of_ne_zero hv) huv'
    · exact ih i fun a b ha hb ↦ hi a.succ b.succ (Fin.succ_lt_succ_iff.mpr ha)
          (Fin.succ_lt_succ_iff.mpr hb)

/-- Linear coefficients for a register's degree-one parse table entry. -/
theorem exists_parse_linear [Fintype σ] {r : ℕ} (p : Program K σ r) (g : Fin r) :
    ∃ c : σ → K, homogeneousComponent 1 (registerPolynomial p g) = ∑ i, C (c i) * X i := by
  let M := Submodule.span K (Set.range (X : σ → MvPolynomial σ K))
  have h := homogeneousComponent_register_mem p g (by decide : 0 < 1) M
    (fun _ x ↦ Submodule.subset_span ⟨x, rfl⟩) (fun a b _ _ u v hu hv hsum ↦ by omega)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp h
  exact ⟨c, by simpa only [MvPolynomial.smul_eq_C_mul] using hc.symm⟩

/-- Product coefficients for a register's degree-`k + 2` parse table entry. -/
theorem exists_parse_product {r : ℕ} (p : Program K σ r) (g : Fin r) (k : ℕ) :
    ∃ c : Fin (k+1) × Fin r × Fin r → K,
      homogeneousComponent (k+2) (registerPolynomial p g) = ∑ q, C (c q) *
        homogeneousComponent (q.1.val+1) (registerPolynomial p q.2.1) *
        homogeneousComponent (k-q.1.val+1) (registerPolynomial p q.2.2) := by
  let product (q : Fin (k+1) × Fin r × Fin r) :=
    homogeneousComponent (q.1.val+1) (registerPolynomial p q.2.1) *
      homogeneousComponent (k-q.1.val+1) (registerPolynomial p q.2.2)
  let M := Submodule.span K (Set.range product)
  have h := homogeneousComponent_register_mem p g (by omega : 0 < k+2) M (by omega)
    (fun a b _ _ u v hu hv huv ↦ by
      apply Submodule.subset_span
      refine ⟨(⟨u-1, by omega⟩, a, b), ?_⟩
      simp only [product]
      rw [show u - 1 + 1 = u by omega, show k - (u - 1) + 1 = v by omega])
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp h
  exact ⟨c, by simpa only [product, MvPolynomial.smul_eq_C_mul, mul_assoc] using hc.symm⟩

end

end SpectralBooks
end LinearAlgebra
end OAI
