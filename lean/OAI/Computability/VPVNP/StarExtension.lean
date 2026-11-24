import OAI.Computability.VPVNP.StarProfile
import OAI.Computability.VPVNP.TensorExtensionMatching
import OAI.Computability.VPVNP.TensorFlatteningPoint

/-!
# Exact extension for a prescribed width profile

Theorem 2.4(2) requires the extension to match every old tensor value and
the target of one dyadic star. Products of the old generators reduce to
one old tensor, while all star occurrences combine into one power. This
identifies the finite-generator estimates with the concrete contraction
bounds on arrays.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u
namespace WireTensor.SpectralPoint

open RestrictionClass
variable {k : Type u} {J : Type} [Field k] [Fintype J] [Nonempty J]

/-- The class of the star whose width at leaf `j` is `w j`. -/
noncomputable def dyadicStarClass (w : J → ℕ) : RestrictionClass k (Option J) :=
  ofTensor (starTensor (fun j ↦ Fin (2 ^ w j)))

omit [Nonempty J] in
theorem dyadicStarClass_ne_zero (w : J → ℕ) : dyadicStarClass (k := k) w ≠ 0 := by
  rw [dyadicStarClass, ne_eq, ofTensor_eq_zero_iff]
  intro hz
  let a (j : J) : Fin (2 ^ w j) := ⟨0, Nat.pow_pos (by decide)⟩
  have h := congrFun hz (withCenter (B := starBasis (fun j ↦ Fin (2 ^ w j))) a a)
  have h₁ : (starTensor (k := k) (fun j ↦ Fin (2 ^ w j))).coeff (withCenter a a) = 1 := by
    dsimp only [starTensor, withCenter]
    exact ite_eq_left rfl
  exact one_ne_zero (h₁.symm.trans h)

variable (F : SpectralPoint k J)

/-- A monomial with a combined old factor and a star power obeys its target bound. -/
theorem contractionClassValue_old_star_le (w : J → ℕ) (x : RestrictionClass k J) (n : ℕ) :
    F.contractionClassValue (embedOldClass x * dyadicStarClass w ^ n) ≤
      ofSpectralPoint F x * ((2 : ℝ) ^ F.starRate w) ^ n := by
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  rw [F.contractionClassValue_old_product, ofSpectralPoint_ofTensor,
    dyadicStarClass, ← ofTensor_tensorPowerFin, F.contractionClassValue_ofTensor]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (F.contractionValue_starPower_le w n).trans_eq ?_
  rw [mul_comm, Real.rpow_mul_natCast (by norm_num)]

/-- The root limit of a power of one folded monomial equals its target. -/
theorem contractionClassValue_old_star_root (w : J → ℕ) (x : RestrictionClass k J) (n : ℕ) :
    Filter.Tendsto (fun m : ℕ ↦
      (F.contractionClassValue ((embedOldClass x * dyadicStarClass w ^ n) ^ m)) ^ (m : ℝ)⁻¹)
      Filter.atTop (nhds (ofSpectralPoint F x * ((2 : ℝ) ^ F.starRate w) ^ n)) := by
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  have h := F.starPower_contractionRoot T w n
  simpa only [← F.contractionClassValue_ofTensor, ofTensor_tensorProduct, ← embedOldClass_ofTensor,
    ofTensor_tensorPowerFin, map_pow, pow_mul, mul_pow, dyadicStarClass, ofSpectralPoint_ofTensor,
    mul_comm (n : ℝ), Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))] using h

/-- Theorem 2.4(2), attainment. A single new spectral point preserves every
old tensor value and realizes the profile rate as its weighted star length. -/
theorem exists_starRate_extension (w : J → ℕ) :
    ∃ H : SpectralPoint k (Option J), (∀ T, H.value (embedOld T) = F.value T) ∧
      ∑ j, (w j : ℝ) * H.wireDistance none (some j) = F.starRate w := by
  classical
  let extra (_ : Unit) := dyadicStarClass (k := k) w
  let cost (_ : Unit) := (2 : ℝ) ^ F.starRate w
  have upper (x : RestrictionClass k J) (n : Unit → ℕ) :
      F.contractionClassValue (embedOldClass x * ∏ i, extra i ^ n i) ≤
        ofSpectralPoint F x * ∏ i, cost i ^ n i := by
    simpa only [Fintype.prod_unique] using F.contractionClassValue_old_star_le w x (n ())
  have balanced (x : RestrictionClass k J) (e : ℕ) (_ : 0 < e) :
      Filter.Tendsto (fun m : ℕ ↦ F.contractionClassValue ((embedOldClass x * ∏ i, extra i ^ e) ^ m)
        ^ (m : ℝ)⁻¹) Filter.atTop (nhds (ofSpectralPoint F x * ∏ i, cost i ^ e)) := by
    simpa only [Fintype.prod_unique] using F.contractionClassValue_old_star_root w x e
  obtain ⟨H, hExtends, hStar⟩ := F.exists_extension_matching_of_rank
    (flatteningRankHom (none : Option J)) (flatteningRankHom_monotone none) extra cost
    (fun _ ↦ dyadicStarClass_ne_zero w) (fun _ ↦ Real.rpow_pos_of_pos (by norm_num) _)
    upper balanced
  refine ⟨H, hExtends, (Real.strictMono_rpow_of_base_gt_one (by norm_num : 1 < (2 : ℝ))).injective ?_⟩
  rw [← value_dyadicStar H w]
  exact hStar ()

/-- Equation (2.1). The minimum over all spectral points extending `F` is
attained, for each individual choice of the width profile. -/
theorem starRate_isLeast (w : J → ℕ) :
    IsLeast {c : ℝ | ∃ H : SpectralPoint k (Option J),
      (∀ T, H.value (embedOld T) = F.value T) ∧
        ∑ j, (w j : ℝ) * H.wireDistance none (some j) = c} (F.starRate w) := by
  refine ⟨F.exists_starRate_extension w, ?_⟩
  rintro _ ⟨H, hH, rfl⟩
  exact F.starRate_le_extension H hH w

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
