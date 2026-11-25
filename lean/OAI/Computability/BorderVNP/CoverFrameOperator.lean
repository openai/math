import OAI.Computability.BorderVNP.CoverHeckeCorrespondence
import OAI.Computability.BorderVNP.CoverFrameCompactness
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The Hecke operator on bounded continuous functions

The frame space is the right coset quotient, with its quotient topology.
The Hecke branches give a positive linear contraction on this space
and commute with its right translations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open BoundedContinuousFunction Set Finset
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (Γ : Subgroup G) (z : G)

private theorem coset_open : IsOpenMap (coset Γ) := by
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  have heq : coset Γ ⁻¹' (coset Γ '' U) = ⋃ a : Γ, (fun g : G => (a:G) * g) '' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, mem_iUnion]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have ha := QuotientGroup.rightRel_apply.mp (Quotient.exact hxy)
      exact ⟨⟨x*y⁻¹, ha⟩, y, hy, by simp⟩
    · rintro ⟨a,y,hy,rfl⟩
      exact ⟨y,hy, Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp))⟩
  change IsOpen (coset Γ ⁻¹' (coset Γ '' U))
  rw [heq]
  exact isOpen_iUnion fun a => isOpenMap_mul_left _ _ hU

/-- The quotient map to the right cosets is continuous, open and surjective. -/
theorem coset_openQuotient : IsOpenQuotientMap (coset Γ) :=
  IsOpenQuotientMap.of_isOpenMap_isQuotientMap (coset_open Γ) isQuotientMap_quotient_mk'

/-- Right translations vary continuously in both the frame and the translating group element. -/
theorem rightMul_continuous :
    Continuous (Function.uncurry (fun (x : Cosets Γ) (g : G) => rightMul Γ g x)) := by
  apply ((coset_openQuotient Γ).prodMap IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr
  exact (coset_openQuotient Γ).continuous.comp continuous_mul

/-- Small right translations fill neighborhoods of each frame. -/
theorem rightMul_openOrbit (x : Cosets Γ) : IsOpenMap (fun g => rightMul Γ g x) := by
  obtain ⟨a,rfl⟩ := (coset_openQuotient Γ).surjective x
  exact (coset_open Γ).comp (isOpenMap_mul_left a)

variable [Fintype (Cosets (intersection Γ z))]

private theorem continuous_average (f : Cosets Γ →ᵇ ℝ) : Continuous (average Γ z f) := by
  apply (coset_openQuotient Γ).isQuotientMap.continuous_iff.mpr
  change Continuous (fun x : G => _ * ∑ i, f (branch Γ z x i))
  apply continuous_const.mul
  apply continuous_finsetSum
  rintro ⟨a⟩ _
  exact f.continuous.comp ((coset_openQuotient Γ).continuous.comp
    (continuous_const.mul continuous_id))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem card_pos : (0:ℝ) < Fintype.card (Cosets (intersection Γ z)) := by
  have : Nonempty (Cosets (intersection Γ z)) := ⟨coset _ 1⟩
  exact_mod_cast Fintype.card_pos

omit [IsTopologicalGroup G] in
private theorem sum_estimate (f : Cosets Γ →ᵇ ℝ) (x : G) :
    ‖average Γ z f (coset Γ x)‖ ≤ ‖f‖ := by
  have h := card_pos Γ z
  rw [average_coset, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos h]
  calc
    _ ≤ _ * (∑ _i : Cosets (intersection Γ z), ‖f‖) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i _ => f.norm_coe_le_norm _))
        (by positivity)
    _ = _ := by simp [nsmul_eq_mul, inv_mul_cancel_left₀ h.ne']

/-- The finite Hecke average as a linear contraction on bounded continuous functions. -/
noncomputable def operator [CompactSpace (Cosets Γ)] :
    (Cosets Γ →ᵇ ℝ) →L[ℝ] (Cosets Γ →ᵇ ℝ) :=
  let L : (Cosets Γ →ᵇ ℝ) →ₗ[ℝ] (Cosets Γ →ᵇ ℝ) := {
    toFun := fun f => mkOfCompact ⟨average Γ z f, continuous_average Γ z f⟩
    map_add' := by
      intro f g
      ext ⟨x⟩
      change _ * (∑ i, (f + g) (branch Γ z x i)) = _ * (∑ i, f (branch Γ z x i)) +
        _ * (∑ i, g (branch Γ z x i))
      simp only [BoundedContinuousFunction.add_apply, sum_add_distrib, mul_add]
    map_smul' := by
      intro c f
      ext ⟨x⟩
      change _ * (∑ i, (c • f) (branch Γ z x i)) = c * (_ * ∑ i, f (branch Γ z x i))
      simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, ← mul_sum]
      ring }
  L.mkContinuous 1 (by
    intro f
    rw [one_mul, BoundedContinuousFunction.norm_le (norm_nonneg _)]
    rintro ⟨x⟩
    exact sum_estimate Γ z f x)

/-- Evaluation on an actual frame. -/
theorem operator_apply [CompactSpace (Cosets Γ)] (f : Cosets Γ →ᵇ ℝ) (x : Cosets Γ) :
    operator Γ z f x = average Γ z f x := rfl

/-- The sup norm contracts. -/
theorem operator_norm_le [CompactSpace (Cosets Γ)] (f : Cosets Γ →ᵇ ℝ) :
    ‖operator Γ z f‖ ≤ ‖f‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
  rintro ⟨x⟩
  exact sum_estimate Γ z f x

/-- The branches commute with a common right translation of the frame. -/
theorem operator_translate [CompactSpace (Cosets Γ)] (g : G) (f : Cosets Γ →ᵇ ℝ) :
    operator Γ z (CoverFrameMixing.translate _ (rightMul_continuous Γ) g f) =
    CoverFrameMixing.translate _ (rightMul_continuous Γ) g (operator Γ z f) := by
  ext ⟨x⟩
  change _ * (∑ i, f (rightMul Γ g (branch Γ z x i))) = _ * (∑ i, f (branch Γ z (x*g) i))
  congr 1
  apply sum_congr rfl
  rintro ⟨a⟩ _
  change f (coset Γ (z*a*x*g)) = f (coset Γ (z*a*(x*g)))
  rw [mul_assoc]

/-- The Cesàro averages of the Hecke operator are relatively compact in the uniform norm. -/
theorem average_compact [CompactSpace (Cosets Γ)] (f : Cosets Γ →ᵇ ℝ) :
    IsCompact (closure (Set.range (CoverFrameMixing.mean (operator Γ z) f))) := by
  apply CoverFrameMixing.averages_compact _ (rightMul_continuous Γ) _ (rightMul_openOrbit Γ)
    (operator Γ z) (operator_norm_le Γ z) (operator_translate Γ z)
  rintro ⟨x⟩
  change coset Γ (x*1) = coset Γ x
  rw [mul_one]

end Hecke

end BorderVNP
end Computability
end OAI
