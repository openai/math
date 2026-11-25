import OAI.Computability.BorderVNP.BranchPoleMinor
import OAI.Computability.VPVNP.EffectiveNullstellensatz
import OAI.Computability.VPVNP.MacaulayReduction

/-! # Bounded equations for the values on a generic finite fiber

Treat the parameter as an element of the algebraic closure of its rational function
field and the proposed target value as a second indeterminate. The effective weak
Nullstellensatz gives a single bounded Macaulay matrix. Its maximal minor supplies a
bivariate equation before specializing the parameter, including a bound for every
coefficient's degree in the parameter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate VPVNP.CertificateReduction

/-- Upper bound for the number of Macaulay columns at the effective certificate cutoff. -/
def eliminantWidth (h d : ℕ) : ℕ := ((2 * d) ^ (4 * (h + 2)) + d + 1) ^ h

private theorem row_notMem_iff_rank {L I J : Type*} [Field L] [Fintype I] [Fintype J]
    (M : Matrix I J L) (v : J → L) :
    v ∉ Submodule.span L (Set.range M.row) ↔
      M.rank < Matrix.rank (Option.elim' v M : Matrix (Option I) J L) := by
  let N : Matrix (Option I) J L := Option.elim' v M
  have he : Set.range N.row = insert v (Set.range M.row) := by
    ext a
    constructor
    · rintro ⟨(_ | i), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨i, rfl⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some i, rfl⟩
  change _ ↔ M.rank < N.rank
  rw [M.rank_eq_finrank_span_row, N.rank_eq_finrank_span_row, he]
  constructor
  · intro hv
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne (Submodule.span_mono (Set.subset_insert ..)) fun eq ↦ hv ?_
    rw [eq]
    exact Submodule.subset_span (Set.mem_insert ..)
  · intro hr hv
    rw [Submodule.span_insert_eq_span hv] at hr
    exact hr.false

/-- Existence of a generic root at `w` is exactly a rank jump of the matrix augmented by
the coefficient vector of one. -/
private theorem fiber_iff_rank_jump {K L I : Type*} [Field K] [Field L] [IsAlgClosed L]
    [Fintype I] {h d : ℕ} (φ : Polynomial K →+* L)
    (G : I → MvPolynomial (Fin h) (Polynomial (Polynomial K))) (hd : 3 ≤ d)
    (hx : ∀ i, (G i).totalDegree ≤ d) (w : L) :
    let H := (2 * d) ^ (4 * (h + 2))
    let M := macaulayMatrix G H (H + d)
    let v := coefficientRow (H + d) (1 : MvPolynomial (Fin h) (Polynomial (Polynomial K)))
    let N : Matrix (Option (I × BoundedMonomial h H)) (BoundedMonomial h (H+d))
        (Polynomial (Polynomial K)) := Option.elim' v M
    (∃ x : Fin h → L, ∀ i, eval₂ (Polynomial.eval₂RingHom φ w) x (G i) = 0) ↔
      (M.map (Polynomial.eval₂RingHom φ w)).rank < (N.map (Polynomial.eval₂RingHom φ w)).rank := by
  dsimp only
  let H := (2 * d) ^ (4 * (h + 2))
  let ρ := Polynomial.eval₂RingHom φ w
  let F := fun i ↦ map ρ (G i)
  let M := macaulayMatrix F H (H+d)
  let v := coefficientRow (H+d) (1 : MvPolynomial (Fin h) L)
  let N : Matrix (Option (I × BoundedMonomial h H)) (BoundedMonomial h (H+d)) L := Option.elim' v M
  have hm := macaulayMatrix_map ρ G H (H+d)
  have hn : Matrix.map (Option.elim' (coefficientRow (H+d)
      (1 : MvPolynomial (Fin h) (Polynomial (Polynomial K)))) (macaulayMatrix G H (H+d))
      : Matrix _ _ _) ρ = N := by
    ext (i | i) j
    · change ρ ((1 : MvPolynomial (Fin h) _).coeff j.val) =
        (1 : MvPolynomial (Fin h) L).coeff j.val
      simp [MvPolynomial.coeff_one, apply_ite]
    · exact congrFun (congrFun hm.symm i) j
  rw [hn, ← hm]
  change _ ↔ M.rank < N.rank
  rw [← row_notMem_iff_rank M v]
  have hdeg (i : I) : (F i).totalDegree ≤ d := (Finset.sup_mono (support_map_subset ρ _)).trans (hx i)
  constructor
  · rintro ⟨x, hx⟩ hmem
    have hv (i : I) : aeval x (F i) = 0 := by
      simpa only [aeval_eq_eval, F, ← eval₂_eq_eval_map] using hx i
    have h := aeval_eq_zero_of_row_mem F hdeg 1 (by simp) hmem x hv
    simp at h
  · intro hmem
    obtain ⟨x, hx⟩ := commonZero_of_one_notMem (E := L) F H d hdeg hmem
      (effective_weakCertificateBound L _ hd)
    exact ⟨x, fun i ↦ by simpa only [aeval_eq_eval, F, ← eval₂_eq_eval_map] using hx i⟩

/-- A finite target-value image on the generic fiber has an eliminant over the original
coefficient field with singly exponential degree in both the target and the parameter.
The input equations may include the inverse of a denominator as an auxiliary variable. -/
theorem generic_fiber_eliminant {K L I : Type*} [Field K] [Field L] [IsAlgClosed L]
    [Fintype I] {h d e : ℕ} (φ : Polynomial K →+* L)
    (G : I → MvPolynomial (Fin h) (Polynomial (Polynomial K))) (hd : 3 ≤ d)
    (hx : ∀ i, (G i).totalDegree ≤ d) (hw : ∀ i μ, ((G i).coeff μ).natDegree ≤ 1)
    (ht : ∀ i μ j, (((G i).coeff μ).coeff j).natDegree ≤ e)
    (hfinite : {w : L | ∃ x : Fin h → L, ∀ i, eval₂ (Polynomial.eval₂RingHom φ w) x (G i) = 0}.Finite) :
    ∃ Q : Polynomial (Polynomial K), Q ≠ 0 ∧ Q.natDegree ≤ eliminantWidth h d ∧
      (∀ j, (Q.coeff j).natDegree ≤ eliminantWidth h d * e) ∧
      ∀ (w : L) (x : Fin h → L), (∀ i, eval₂ (Polynomial.eval₂RingHom φ w) x (G i) = 0) →
        Q.eval₂ φ w = 0 := by
  let H := (2 * d) ^ (4 * (h + 2))
  let M := macaulayMatrix G H (H+d)
  let v := coefficientRow (H+d) (1 : MvPolynomial (Fin h) (Polynomial (Polynomial K)))
  let N : Matrix (Option (I × BoundedMonomial h H)) (BoundedMonomial h (H+d))
      (Polynomial (Polynomial K)) := Option.elim' v M
  have hf : {a : L | (M.map (Polynomial.eval₂RingHom φ a)).rank <
      (N.map (Polynomial.eval₂RingHom φ a)).rank}.Finite :=
    hfinite.subset (fun _ h ↦ (fiber_iff_rank_jump φ G hd hx _).mpr h)
  have hm (i j) : (M i j).natDegree ≤ 1 := by
    rw [show M = macaulayMatrix G H (H+d) from rfl, macaulayMatrix_apply]
    split_ifs <;> simp [hw]
  have he (i j k) : ((M i j).coeff k).natDegree ≤ e := by
    rw [show M = macaulayMatrix G H (H+d) from rfl, macaulayMatrix_apply]
    split_ifs <;> simp [ht]
  obtain ⟨Q, hn, hQ, hQe, hz⟩ := rank_jump_eliminant φ M N hm he hf
  have hcols : Fintype.card (BoundedMonomial h (H+d)) ≤ eliminantWidth h d :=
    card_boundedMonomial_le h (H+d)
  exact ⟨Q, hn, hQ.trans hcols, fun j ↦ (hQe j).trans (Nat.mul_le_mul_right _ hcols),
    fun w x h ↦ hz w ((fiber_iff_rank_jump φ G hd hx w).mp ⟨x, h⟩)⟩

end Branch

end BorderVNP
end Computability
end OAI
