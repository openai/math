import OAI.Hierarchy.BallWidth
import OAI.Hierarchy.ForcePartition
import OAI.Hierarchy.OneSummandForces

namespace OAI
/-! # The force bound for a family of partitioned rank decompositions -/

noncomputable section

namespace Hierarchy.HomogeneousFlat

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical BigOperators InnerProductSpace

variable {I B : Type} [Fintype I] [Fintype B] [Nonempty B] {d : ℕ}

omit [Nonempty B] in
/-- Passing to disjoint blocks introduces no multiplicity in the force error. -/
theorem block_force_error (σ : I → B) (f g : I → (EuclideanSpace ℝ (Fin d))) :
    (∑ k, ‖blockForce σ f k‖) ≤ (∑ k, ‖blockForce σ g k‖) + ∑ i, ‖g i - f i‖ := by
  have split (k : B) : ‖blockForce σ f k‖ ≤ ‖blockForce σ g k‖ +
      ∑ i : {i // σ i = k}, ‖g i.val - f i.val‖ := by
    have h : blockForce σ f k =
        blockForce σ g k - ∑ i : {i // σ i = k}, (g i.val - f i.val) := by
      simp [blockForce, Finset.sum_sub_distrib]
    rw [h]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le Finset.univ _))
  calc
    _ ≤ _ := Finset.sum_le_sum fun k _ => split k
    _ = _ := by
      rw [Finset.sum_add_distrib]
      exact congrArg (fun a => (∑ k, ‖blockForce σ g k‖) + a)
        (Fintype.sum_fiberwise σ (fun i : I => ‖g i - f i‖))

private theorem logb_nat_nonneg (n : ℕ) : 0 ≤ Real.logb 2 (n : ℝ) := by
  cases n with
  | zero => simp
  | succ k => exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))

variable {F : Type*} [Field F] [Nonempty I] [DecidableEq I]
    {A : I → Type} [∀ i, Fintype (A i)] {J : Type*} [Fintype J]

/-- In a border family of sums, each member can have a different partition at
each summand. At least one such partition bounds the sum of prescribed block
loads by its rank cost and the single terminal error budget. -/
theorem path_force (P : HomogeneousFlat F d) (x : I → (EuclideanSpace ℝ (Fin d))) (hx : ∀ i, ‖x i‖ = 1)
    {S : Set (J → (∀ i, A i) → F)} {t : (∀ i, A i) → F}
    (cl : t ∈ affineZariskiClosure ((fun Y => ∑ j, Y j) '' S)) (ht : t ≠ 0)
    (price : P.prices.price (ForceSelection.raw t) x = ∑ i, Real.logb 2 (Fintype.card (A i)))
    {ε : ℝ} (hε : 0 < ε) (σ : J → I → B) (R : ℕ)
    (cp : ∀ Y ∈ S, ∀ j, Y j ≠ 0 →
      ∃ factor : Fin R → (k : B) → ((i : {i // σ j i = k}) → A i.val) → F,
        ∀ a, Y j a = ∑ r, ∏ k, factor r k (fun i => a i.val)) :
    ∃ Y ∈ S, ∃ j, Y j ≠ 0 ∧
      (∑ k, ‖blockForce (σ j) (fun i => Real.logb 2 (Fintype.card (A i)) • x i) k‖) ≤
        Real.sqrt (2*Real.pi) * Real.sqrt (Fintype.card B : ℝ) * Real.logb 2 R +
        Real.sqrt (2 * (∑ i, Real.logb 2 (Fintype.card (A i))) *
          (ε + Real.sqrt (2*Real.pi) * Real.sqrt (Fintype.card I : ℝ) *
            Real.logb 2 (Fintype.card J))) := by
  obtain ⟨Y,hY,j,hj,g,_,supp,err,_⟩ := P.one_summand_forces x hx cl ht price hε
  obtain ⟨f,hf⟩ := cp Y hY j hj
  obtain ⟨y,hy,rank⟩ := P.force_partition_cp (ForceSelection.raw (Y j)) g supp (σ j) R f hf
  have hgroup := rank.trans (mul_le_mul_of_nonneg_right (P.diagonal_image_le_sqrt_card y hy)
    (logb_nat_nonneg R))
  have sites := P.binary_price_le_sqrt_card x (fun i => (hx i).le)
  have terminal := err.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl ε) (mul_le_mul_of_nonneg_right sites (logb_nat_nonneg (Fintype.card J))))
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => logb_nat_nonneg (Fintype.card (A i)))))))
  exact ⟨Y,hY,j,hj,(block_force_error (σ j) _ g).trans (add_le_add hgroup terminal)⟩

end Hierarchy.HomogeneousFlat

end
end OAI
