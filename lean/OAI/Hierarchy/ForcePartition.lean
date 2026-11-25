import OAI.Hierarchy.DiagonalRankPrice
import OAI.Hierarchy.FlatPrices
import OAI.LinearAlgebra.SpectralBooks.SpectralDiagonal
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI
/-! # The aggregate force on the blocks of an arbitrary grouped rank decomposition -/

noncomputable section

namespace Hierarchy.HomogeneousFlat

open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators InnerProductSpace

variable {I J : Type} [Fintype I] [Fintype J] [Nonempty J] {F : Type*} [Field F] {d : ℕ}

/-- Total force of the legs sharing a block. -/
def blockForce (σ : I → J) (g : I → EuclideanSpace ℝ (Fin d)) (j : J) :
    EuclideanSpace ℝ (Fin d) := ∑ i : {i // σ i = j}, g i.1

private theorem inner_normalize {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    ⟪x, NormedSpace.normalize x⟫_ℝ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  rw [NormedSpace.normalize, real_inner_smul_right, real_inner_self_eq_norm_mul_norm,
    ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_mul]

/-- Testing the support on the normalized total force of each block gives the grouped
rank inequality, including repeated directions and force-zero blocks. -/
theorem force_partition_rank (P : HomogeneousFlat F d) (T : Raw.{0} I F)
    (g : I → EuclideanSpace ℝ (Fin d))
    (support : ∀ y, (∑ i, ⟪g i, y i⟫_ℝ) ≤ P.prices.price T y)
    (σ : I → J) (R : ℕ) (rank : (T.group σ).Restricts (Raw.diagonal J F (Fin R))) :
    ∃ y : J → EuclideanSpace ℝ (Fin d), (∀ j, ‖y j‖ ≤ 1) ∧
      ∑ j, ‖blockForce σ g j‖ ≤ P.prices.diagonal (Finset.univ.image y) * Real.logb 2 R := by
  let y (j : J) := NormedSpace.normalize (blockForce σ g j)
  have unit (j : J) : ‖y j‖ ≤ 1 := by
    by_cases h : blockForce σ g j = 0
    · simp [y,h]
    · exact (NormedSpace.norm_normalize h).le
  refine ⟨y,unit,?_⟩
  have regroup : (∑ j, ‖blockForce σ g j‖) = ∑ i, ⟪g i, y (σ i)⟫_ℝ := by
    rw [← Fintype.sum_fiberwise σ]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ⟪blockForce σ g j,y j⟫_ℝ := (inner_normalize _).symm
      _ = _ := by
        rw [blockForce, sum_inner]
        apply Finset.sum_congr rfl
        intro i _
        simp only [i.property]
  rw [regroup]
  calc
    _ ≤ P.prices.price T (y ∘ σ) := support _
    _ = P.prices.price (T.group σ) y := P.prices.group T σ y
    _ ≤ _ := by
      have diag : P.prices.price (Raw.diagonal J F (Fin 2)) y =
          P.prices.diagonal (Finset.univ.image y) := by
        convert! P.prices.price_binaryDiagonal_eq y using 1
        congr 1
        ext
        simp
      rw [← diag]
      exact price_le_diagonal_mul_log_rank P.prices (T.group σ) y R rank

omit [Nonempty J] in
/-- A concrete product expansion on the original coefficients supplies the restriction
of the grouped tensor.  The factor for a block reads exactly the legs in its fiber. -/
theorem grouped_restricts_of_cp (T : Raw.{0} I F) (σ : I → J) (R : ℕ)
    (factor : Fin R → (j : J) → ((i : {i // σ i = j}) → T.Leg i.val) → F)
    (cp : ∀ a, T.coeff a = ∑ r, ∏ j, factor r j (fun i => a i.val)) :
    (T.group σ).Restricts (Raw.diagonal J F (Fin R)) := by
  change Crossing.IsRestriction (T.group σ).coeff (Raw.diagonal J F (Fin R)).coeff
  have source : (Raw.diagonal J F (Fin R)).coeff =
      Crossing.basisTensor (F := F) (A := fun _ : J => Fin R) (fun r _ => r) := by
    funext a
    simp only [Raw.diagonal, Crossing.basisTensor];
      apply Finset.sum_congr rfl; intro r _; split_ifs <;> rfl
  rw [source]
  apply (Crossing.restriction_basisTensor_iff (fun (r : Fin R) (_ : J) => r) (T.group σ).coeff).mpr
  refine ⟨fun j x r => factor r j x, fun x => ?_⟩
  change T.coeff (fun i => x (σ i) ⟨i, rfl⟩) = _
  rw [cp]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.prod_congr rfl
  intro j _
  apply congrArg (factor r j)
  funext i
  obtain ⟨i,hi⟩ := i
  cases hi
  rfl

/-- The grouped force inequality for a CP decomposition on the original legs. -/
theorem force_partition_cp (P : HomogeneousFlat F d) (T : Raw.{0} I F)
    (g : I → EuclideanSpace ℝ (Fin d))
    (support : ∀ y, (∑ i, ⟪g i, y i⟫_ℝ) ≤ P.prices.price T y)
    (σ : I → J) (R : ℕ)
    (factor : Fin R → (j : J) → ((i : {i // σ i = j}) → T.Leg i.val) → F)
    (cp : ∀ a, T.coeff a = ∑ r, ∏ j, factor r j (fun i => a i.val)) :
    ∃ y : J → EuclideanSpace ℝ (Fin d), (∀ j, ‖y j‖ ≤ 1) ∧
      ∑ j, ‖blockForce σ g j‖ ≤ P.prices.diagonal (Finset.univ.image y) * Real.logb 2 R :=
  P.force_partition_rank T g support σ R (grouped_restricts_of_cp T σ R factor cp)

end Hierarchy.HomogeneousFlat

end
end OAI
