import OAI.Combinatorics.Sunflower.Control
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! # Character matrices for a shared-label resource

A mask diagonal with the character group as labels implements a zero-sum
constraint. Each matrix can depend on a local control and a local output index.
-/

namespace OAI
namespace Combinatorics
namespace Sunflower

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Classical

noncomputable section

variable {I : Type*} [Fintype I]

/-- Contracting matrices with a partial diagonal only sums over its shared label. -/
theorem maskDiagonal_apply {α : Type} [Fintype α] (K : Finset I)
    (M : ∀ i, MaskLeg K α i → ℂ) :
    (∑ a : ∀ i, (Raw.maskDiagonal ℂ K α).Leg i,
      (Raw.maskDiagonal ℂ K α).coeff a * ∏ i, M i (a i)) =
      ∑ t : α, ∏ i, M i (fun _ ↦ t) :=
  contract_maskDiagonal (K := ℂ) (B := fun _ ↦ Unit) K α (fun i _ ↦ M i) (fun _ ↦ ())

variable {Γ : Type} [AddCommGroup Γ] [Fintype Γ] {C B : I → Type*}

/-- The matrix at each site evaluates the shared character on its local
contribution. A designated site supplies the single normalization factor. -/
def fourierMatrix (K : Finset I) (i₀ : I) (phase : ∀ i, C i → B i → Γ)
    (i : I) (c : C i) (x : B i) (a : MaskLeg K (AddChar Γ ℂ) i) : ℂ :=
  (if i = i₀ then (Fintype.card Γ : ℂ)⁻¹ else 1) *
  if h : i ∈ K then a h (phase i c x) else 1

omit [Fintype Γ] in
private theorem char_sum {ι : Type*} (s : Finset ι) (f : ι → Γ) (χ : AddChar Γ ℂ) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]

/-- Fourier contraction implements the indicator that the sum of the local
contributions in the mask vanishes. -/
theorem fourierMatrix_apply (K : Finset I) (i₀ : I) (phase : ∀ i, C i → B i → Γ)
    (c : ∀ i, C i) (x : ∀ i, B i) :
    (∑ a : ∀ i, (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).Leg i,
      (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).coeff a *
        ∏ i, fourierMatrix K i₀ phase i (c i) (x i) (a i)) =
      if (∑ i ∈ K, phase i (c i) (x i)) = 0 then (1 : ℂ) else 0 := by
  classical
  rw [maskDiagonal_apply]
  have hterm (χ : AddChar Γ ℂ) :
      (∏ i, fourierMatrix K i₀ phase i (c i) (x i) (fun _ ↦ χ)) =
        (Fintype.card Γ : ℂ)⁻¹ * χ (∑ i ∈ K, phase i (c i) (x i)) := by
    simp only [fourierMatrix, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
      ite_true, char_sum]
    congr 1
    simp [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [hterm]
  rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite]
  split_ifs <;> simp [Fintype.card_ne_zero]

/-- The controlled-map form used for composing the zero-sum predicate with
other restrictions. -/
theorem eval_fourierMatrix (K : Finset I) (i₀ : I) (phase : ∀ i, C i → B i → Γ)
    (c : ∀ i, C i) (x : ∀ i, B i) :
    @Control.eval I C (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).Leg B _
        (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).finiteLeg
        (fourierMatrix K i₀ phase) c (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).coeff x =
      if (∑ i ∈ K, phase i (c i) (x i)) = 0 then (1 : ℂ) else 0 :=
  fourierMatrix_apply K i₀ phase c x

/-- The zero-sum predicate for fixed local controls is an ordinary tensor
restriction of the character-labeled partial diagonal. -/
theorem zeroSum_restricts (K : Finset I) (i₀ : I)
    (phase : ∀ i, C i → B i → Γ) (c : ∀ i, C i) :
    Crossing.IsRestriction
      (fun x : ∀ i, B i ↦ if (∑ i ∈ K, phase i (c i) (x i)) = 0 then (1 : ℂ) else 0)
      (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).coeff :=
  ⟨fun i ↦ fourierMatrix K i₀ phase i (c i), fun x ↦ (fourierMatrix_apply K i₀ phase c x).symm⟩

end

end Sunflower
end Combinatorics
end OAI
