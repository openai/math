import OAI.Computability.BorderVNP.CoverHeckeCorrespondence
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

/-!
# Finite rational motions from the Cesàro averages

Expand the Hecke correspondence of §5.2 into words of each length
strictly smaller than the averaging length. Distinct samples can give the
same group element. Each sample has a specified rational weight.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open Finset

variable {G I : Type*} [Group G]

/-- A word acts first by its first listed motion and last by its last listed motion. -/
def motion (step : I → G) : (n : ℕ) → (Fin n → I) → G
  | 0, _ => 1
  | n+1, w => motion step n (Fin.tail w) * step (w 0)

/-- All words remain in the subgroup containing their steps. -/
theorem motion_mem (U : Subgroup G) (step : I → G) (h : ∀ i, step i ∈ U)
    (n : ℕ) (w : Fin n → I) : motion step n w ∈ U := by
  induction n with
  | zero => exact U.one_mem
  | succ n ih => exact U.mul_mem (ih _) (h _)

variable (Γ : Subgroup G) (z : G)

/-- A representative motion for each of the Hecke branches. -/
noncomputable def step (i : Cosets (intersection Γ z)) : G := z * (i.out : G)

/-- Evaluating a branch by the motion selected for its index. -/
theorem branch_step (x : G) (i : Cosets (intersection Γ z)) :
    branch Γ z x i = coset Γ (step Γ z i * x) := by
  rw [← Quotient.out_eq i] at ⊢
  change coset Γ (z * i.out * x) = _
  rw [Quotient.out_eq]
  rfl

variable [Fintype (Cosets (intersection Γ z))]

/-- The j-fold Hecke iterate on a frame is the uniform average over all words of length j. -/
theorem iterate_words (f : Cosets Γ → ℝ) (j : ℕ) (x : G) :
    (average Γ z)^[j] f (coset Γ x) =
      ((Fintype.card (Cosets (intersection Γ z)) : ℝ)⁻¹)^j *
        ∑ w : Fin j → Cosets (intersection Γ z), f (coset Γ (motion (step Γ z) j w * x)) := by
  induction j generalizing x with
  | zero => simp [motion]
  | succ j ih =>
    let I := Cosets (intersection Γ z)
    rw [Function.iterate_succ_apply', average_coset]
    simp_rw [branch_step, ih, ← mul_sum]
    rw [← mul_assoc, pow_succ']
    congr 1
    let e := Fin.consEquiv (n := j) (fun _ => I)
    rw [← Fintype.sum_prod_type', ← e.sum_comp]
    apply sum_congr rfl
    rintro ⟨a, w⟩ _
    simp [motion, e, Fin.consEquiv, mul_assoc]

/-- The finite sample space for a Cesàro average of positive length. -/
abbrev Samples (I : Type*) (n : ℕ) := (j : Fin (n+1)) × (Fin j.val → I)

/-- Exact rational weight of one sample: choose the length uniformly and then each letter uniformly. -/
def weight (I : Type*) [Fintype I] (n : ℕ) (s : Samples I n) : ℚ :=
  ((n : ℚ) + 1)⁻¹ * ((Fintype.card I : ℚ)⁻¹)^s.1.val

/-- These rational weights are positive. -/
theorem weight_pos [Fintype I] [Nonempty I] (n : ℕ) (s : Samples I n) :
    0 < weight I n s := by unfold weight; positivity

/-- The rational sample weights sum to one. -/
theorem sum_weight [Fintype I] [Nonempty I] (n : ℕ) :
    ∑ s : Samples I n, weight I n s = 1 := by
  rw [Fintype.sum_sigma]
  have hc : (Fintype.card I : ℚ) ≠ 0 := by positivity
  simp [weight, mul_comm, inv_pow, hc, ne_of_gt (by positivity : 0 < (n : ℚ) + 1)]

/-- The rational distribution acts on all frames by the same table of group elements. -/
theorem cesaro_words (f : Cosets Γ → ℝ) (n : ℕ) (x : G) :
    ((n : ℝ)+1)⁻¹ * ∑ j : Fin (n+1), (average Γ z)^[j.val] f (coset Γ x) =
      ∑ s : Samples (Cosets (intersection Γ z)) n,
        (weight _ n s : ℝ) * f (coset Γ (motion (step Γ z) s.1.val s.2 * x)) := by
  simp_rw [iterate_words, Fintype.sum_sigma, weight, Rat.cast_mul, Rat.cast_inv, Rat.cast_add,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_one, mul_sum, mul_assoc]
  push_cast
  rfl

end Hecke

end BorderVNP
end Computability
end OAI
