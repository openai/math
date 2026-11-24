import OAI.Computability.VPVNP.SplitWires
import OAI.Computability.VPVNP.TensorExtensionMatching
import OAI.Computability.VPVNP.TensorFlatteningPoint
import OAI.Computability.VPVNP.WireGeodesic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Prescribing both distances to a new party

For the two new generators of Theorem 2.4(1), the contraction supremum of
any monomial is at most its prescribed value. Equal exponents on the two
new generators give equality at every power.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v

namespace WireTensor.SpectralPoint

open RestrictionClass Filter
open scoped Topology

variable {k : Type u} {J : Type v} [Field k] [Fintype J] [Nonempty J]
variable (F : SpectralPoint k J)

private noncomputable def splitWireClass (a b : J) (i : Bool) : RestrictionClass k (Option J) :=
  ofTensor (wire none (some (if i then b else a)) (Fin 2))

private noncomputable def splitWireTarget (l₁ l₂ : ℝ) (i : Bool) : ℝ :=
  (2 : ℝ) ^ (if i then l₂ else l₁)

private theorem splitWireTarget_mul (l₁ l₂ : ℝ) (u v : ℕ) :
    splitWireTarget l₁ l₂ false ^ u * splitWireTarget l₁ l₂ true ^ v =
      (2 : ℝ) ^ ((u : ℝ) * l₁ + (v : ℝ) * l₂) := by
  simp only [splitWireTarget, Bool.false_eq_true, ↓reduceIte]
  rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_mul_natCast (by norm_num),
    ← Real.rpow_add (by norm_num)]
  congr 1
  ring

private theorem splitClass_upper (a b : J) {l₁ l₂ : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (hs : l₁ + l₂ = F.wireDistance a b) (x : RestrictionClass k J) (u v : ℕ) :
    F.contractionClassValue (embedOldClass x * (splitWireClass a b false ^ u *
        splitWireClass a b true ^ v)) ≤
      ofSpectralPoint F x * (splitWireTarget l₁ l₂ false ^ u * splitWireTarget l₁ l₂ true ^ v) := by
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  simp only [splitWireClass, Bool.false_eq_true, ↓reduceIte, ← ofTensor_binarySplit,
    embedOldClass_ofTensor, ← ofTensor_tensorProduct, F.contractionClassValue_ofTensor,
    ofSpectralPoint_ofTensor, splitWireTarget_mul]
  exact F.contractionValue_binarySplit_monomial_le T a b u v h₁ h₂ hs

private theorem splitClass_balanced (a b : J) {l₁ l₂ : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (hs : l₁ + l₂ = F.wireDistance a b) (x : RestrictionClass k J) (e : ℕ) :
    F.contractionClassValue (embedOldClass x * (splitWireClass a b false ^ e *
        splitWireClass a b true ^ e)) =
      ofSpectralPoint F x * (splitWireTarget l₁ l₂ false ^ e * splitWireTarget l₁ l₂ true ^ e) := by
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  simp only [splitWireClass, Bool.false_eq_true, ↓reduceIte, ← ofTensor_binarySplit,
    embedOldClass_ofTensor, ← ofTensor_tensorProduct, F.contractionClassValue_ofTensor,
    ofSpectralPoint_ofTensor, splitWireTarget_mul]
  exact F.contractionValue_binarySplit_monomial_eq T a b e h₁ h₂ hs

private theorem splitClass_power (a b : J) {l₁ l₂ : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (hs : l₁ + l₂ = F.wireDistance a b) (x : RestrictionClass k J) (e m : ℕ) :
    F.contractionClassValue ((embedOldClass x * (splitWireClass a b false ^ e *
        splitWireClass a b true ^ e)) ^ m) =
      (ofSpectralPoint F x * (splitWireTarget l₁ l₂ false ^ e * splitWireTarget l₁ l₂ true ^ e)) ^ m := by
  simpa only [mul_pow, ← pow_mul, map_pow] using
    F.splitClass_balanced a b h₁ h₂ hs (x ^ m) (e * m)

private theorem splitWireClass_ne_zero (a b : J) (i : Bool) :
    splitWireClass (k := k) a b i ≠ 0 := by
  let W := wire (k := k) none (some (if i then b else a)) (Fin 2)
  change ofTensor W ≠ 0
  intro hz
  have he := congrFun ((ofTensor_eq_zero_iff _).mp hz) (fun _ ↦ (fun _ ↦ 0, fun _ ↦ 0))
  have h : W.coeff (fun _ ↦ (fun _ ↦ 0, fun _ ↦ 0)) ≠ 0 := by simp [W, wire]
  exact h he

private theorem splitClass_upper_prod (a b : J) {l₁ l₂ : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (hs : l₁ + l₂ = F.wireDistance a b) (x : RestrictionClass k J) (n : Bool → ℕ) :
    F.contractionClassValue (embedOldClass x * ∏ i, splitWireClass a b i ^ n i) ≤
      ofSpectralPoint F x * ∏ i, splitWireTarget l₁ l₂ i ^ n i := by
  simp only [Fintype.prod_bool]
  rw [mul_comm (splitWireClass a b true ^ _), mul_comm (splitWireTarget l₁ l₂ true ^ _)]
  exact F.splitClass_upper a b h₁ h₂ hs x (n false) (n true)

private theorem splitClass_limit (a b : J) {l₁ l₂ : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (hs : l₁ + l₂ = F.wireDistance a b) (x : RestrictionClass k J) (e : ℕ) :
    Tendsto (fun m : ℕ ↦
      F.contractionClassValue ((embedOldClass x * ∏ i, splitWireClass a b i ^ e) ^ m) ^ (m : ℝ)⁻¹)
      atTop (𝓝 (ofSpectralPoint F x * ∏ i, splitWireTarget l₁ l₂ i ^ e)) := by
  simp only [Fintype.prod_bool]
  rw [mul_comm (splitWireClass a b true ^ _), mul_comm (splitWireTarget l₁ l₂ true ^ _)]
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  rw [F.splitClass_power a b h₁ h₂ hs x e m]
  symm
  apply Real.pow_rpow_inv_natCast _ hm.ne'
  have hx : 0 ≤ ofSpectralPoint F x := by
    obtain ⟨T, rfl⟩ := ofTensor_surjective x
    exact NNReal.coe_nonneg _
  exact mul_nonneg hx (mul_nonneg (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
    (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _))

/-- A spectral value prescribed as a power of two fixes the corresponding wire distance. -/
private theorem wireDistance_eq_of_target {J' : Type*} [Fintype J'] (H : SpectralPoint k J')
    (i j : J') (l : ℝ) (h : (H.value (wire i j (Fin 2)) : ℝ) = (2 : ℝ) ^ l) :
    H.wireDistance i j = l := by
  change Real.log (H.value (wire i j (Fin 2))) / Real.log 2 = l
  rw [h, Real.log_rpow (by norm_num), mul_div_cancel_right₀ _ (Real.log_pos (by norm_num)).ne']

omit [Nonempty J] in
/-- Theorem 2.4(1). An added party can realize prescribed nonnegative portions of
the old wire distance while preserving the value of every old tensor. -/
theorem exists_split_extension (a b : J) {l₁ l₂ : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (hs : l₁ + l₂ = F.wireDistance a b) :
    ∃ H : SpectralPoint k (Option J), (∀ T, H.value (embedOld T) = F.value T) ∧
      H.wireDistance (some a) none = l₁ ∧ H.wireDistance none (some b) = l₂ := by
  let : Nonempty J := ⟨a⟩
  obtain ⟨H, hold, hmatch⟩ := F.exists_extension_matching_of_rank
    (flatteningRankHom (k := k) (none : Option J)) (flatteningRankHom_monotone _)
    (splitWireClass a b) (splitWireTarget l₁ l₂) (splitWireClass_ne_zero a b)
    (fun _ ↦ Real.rpow_pos_of_pos (by norm_num) _) (F.splitClass_upper_prod a b h₁ h₂ hs)
    (fun x e _ ↦ F.splitClass_limit a b h₁ h₂ hs x e)
  refine ⟨H, hold, ?_, wireDistance_eq_of_target H _ _ _ (hmatch true)⟩
  rw [H.wireDistance_comm]
  exact wireDistance_eq_of_target H _ _ _ (hmatch false)

omit [Nonempty J] in
/-- The fractional-point form of exact extension, used when adjoining points
for the geodesic completion in Corollary 2.5. -/
theorem exists_fraction_extension (a b : J) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ∃ H : SpectralPoint k (Option J), (∀ T, H.value (embedOld T) = F.value T) ∧
      @WireGeometry.AtFraction (Option J) H.wirePseudoMetric (some a) (some b) t none := by
  have hd := F.wireDistance_nonneg a b
  obtain ⟨H, hold, hleft, hright⟩ := F.exists_split_extension a b
    (mul_nonneg ht hd) (mul_nonneg (sub_nonneg.mpr ht') hd) (by ring)
  refine ⟨H, hold, ?_⟩
  change H.wireDistance (some a) none = t * H.wireDistance (some a) (some b) ∧
    H.wireDistance none (some b) = (1 - t) * H.wireDistance (some a) (some b)
  rw [F.wireDistance_extension H hold]
  exact ⟨hleft, hright⟩

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
