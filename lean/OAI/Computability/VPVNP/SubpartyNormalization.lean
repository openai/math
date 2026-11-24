import OAI.Computability.VPVNP.SubpartyEmbedding
import OAI.Computability.VPVNP.Normalization
import OAI.Computability.VPVNP.TensorRestrictionSemiring

/-!
# Normalizing a spectral point on fewer parties

Lemma 2.3 of *VP and VNP differ over every field* embeds tensors on the used
parties by trivial legs outside them. Raising the old values to the reciprocal
of the embedded diagonal exponent makes their direct sums additive and thus
defines a spectral point on the smaller set.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v w

open scoped NNReal

namespace WireTensor.SpectralPoint

open RestrictionClass

variable {k : Type u} {I : Type v} {O : Type w} [Field k] [Fintype I] [Nonempty I]
  [Fintype O] (F : SpectralPoint k (I ⊕ O))

/-- The old value on trivial extensions descends to the restriction classes
on the smaller party set. -/
noncomputable def embeddedValue : RestrictionClass k I →*₀ ℝ where
  toFun := Quotient.lift (fun T ↦ (F.value (trivialExtension O T) : ℝ))
    (fun _ _ h ↦ congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) <| F.value_eq_of_mutual
      ⟨trivialExtension_restricts h.1, trivialExtension_restricts h.2⟩)
  map_one' := by
    change (F.value (trivialExtension O unit) : ℝ) = 1
    rw [F.value_eq_of_mutual trivialExtension_unit, F.value_unit, NNReal.coe_one]
  map_zero' := by
    change (F.value (trivialExtension O (diagonal (Fin 0))) : ℝ) = 0
    rw [F.value_zero, NNReal.coe_zero]
    funext c
    simp [trivialExtension, diagonal]
  map_mul' a b := by
    obtain ⟨T, rfl⟩ := ofTensor_surjective a
    obtain ⟨U, rfl⟩ := ofTensor_surjective b
    change (F.value (trivialExtension O (tensorProduct T U)) : ℝ) =
      (F.value (trivialExtension O T) : ℝ) * (F.value (trivialExtension O U) : ℝ)
    rw [F.value_eq_of_mutual (trivialExtension_product T U), F.value_tensorProduct, NNReal.coe_mul]

@[simp] theorem embeddedValue_ofTensor (T : Tensor.{u, v, 0} k I) :
    F.embeddedValue (ofTensor T) = F.value (trivialExtension O T) := rfl

private theorem embeddedValue_nonneg (x : RestrictionClass k I) : 0 ≤ F.embeddedValue x := by
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  exact (F.value _).coe_nonneg

private theorem embeddedValue_summand (x y : RestrictionClass k I) :
    F.embeddedValue x ≤ F.embeddedValue (x + y) := by
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  obtain ⟨U, rfl⟩ := ofTensor_surjective y
  exact F.monotone (trivialExtension_restricts (directSum_restricts_left T U))

private theorem embeddedValue_add_le (x y : RestrictionClass k I) :
    F.embeddedValue (x + y) ≤ F.embeddedValue x + F.embeddedValue y := by
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  obtain ⟨U, rfl⟩ := ofTensor_surjective y
  exact_mod_cast (F.monotone (trivialExtension_directSum T U)).trans_eq (F.value_directSum _ _)

/-- Base-two logarithm of the value of the embedded two-dimensional diagonal. -/
noncomputable def subpartyExponent : ℝ := Real.log (F.embeddedValue 2) / Real.log 2

/-- The power law for local diagonal tensors on the used parties. -/
theorem embeddedValue_natCast {q : ℕ} (hq : 0 < q) :
    F.embeddedValue q = (q : ℝ) ^ F.subpartyExponent := by
  let g := F.embeddedValue.toMonoidHom.comp (Nat.castRingHom (RestrictionClass k I)).toMonoidHom
  have hg : Monotone g := by
    intro a b hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    change F.embeddedValue a ≤ F.embeddedValue (↑(a+c))
    simpa only [Nat.cast_add] using F.embeddedValue_summand a c
  exact monotone_dimension_power_law g hg hq

/-- The smaller-party spectral point, with the local diagonal normalized to
dimension. Its evaluations include every tensor supported on the used parties. -/
noncomputable def subpartyNormalization (hpos : 0 < F.subpartyExponent) : SpectralPoint k I where
  value T := F.value (trivialExtension O T) ^ F.subpartyExponent⁻¹
  monotone h :=
    NNReal.rpow_le_rpow (F.monotone (trivialExtension_restricts h)) (inv_nonneg.mpr hpos.le)
  value_unit := by rw [F.value_eq_of_mutual trivialExtension_unit, F.value_unit, NNReal.one_rpow]
  value_zero T hT := by
    rw [F.value_zero, NNReal.zero_rpow (inv_pos.mpr hpos).ne']
    funext c
    exact congrFun hT _
  value_tensorProduct T U := by
    rw [F.value_eq_of_mutual (trivialExtension_product T U), F.value_tensorProduct, NNReal.mul_rpow]
  value_directSum T U := by
    apply NNReal.eq
    simp only [NNReal.coe_rpow, NNReal.coe_add]
    apply Spectral.normalized_multiplicative_value_add F.embeddedValue F.embeddedValue_nonneg
      F.embeddedValue_summand F.embeddedValue_add_le hpos _ (ofTensor T) (ofTensor U)
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow hpos.ne']
    · exact F.embeddedValue_natCast hn

@[simp] theorem subpartyNormalization_value (hpos : 0 < F.subpartyExponent)
    (T : Tensor.{u, v, 0} k I) :
    (F.subpartyNormalization hpos).value T =
      F.value (trivialExtension O T) ^ F.subpartyExponent⁻¹ := rfl

omit [Nonempty I] in
/-- Keeping an old wire and adding trivial legs agrees with the same wire
between the included endpoints. -/
private theorem trivialExtension_wire (a b : I) (D : Type) [Fintype D] :
    Restricts (trivialExtension O (wire (k := k) a b D)) (wire (.inl a) (.inl b) D) ∧
    Restricts (wire (.inl a) (.inl b) D) (trivialExtension O (wire (k := k) a b D)) := by
  let e (j : I ⊕ O) :
      (wire (k := k) (Sum.inl a) (Sum.inl b) D).Basis j ≃
        (trivialExtension O (wire (k := k) a b D)).Basis j :=
    match j with
    | .inl i =>
      { toFun := fun x ↦ ⟨fun h ↦ x.1 (congrArg Sum.inl h), fun h ↦ x.2 (congrArg Sum.inl h)⟩
        invFun := fun x ↦ ⟨fun h ↦ x.1 (Sum.inl.inj h), fun h ↦ x.2 (Sum.inl.inj h)⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    | .inr o =>
      { toFun := fun _ ↦ .unit
        invFun := fun _ ↦ ⟨(fun h ↦ nomatch h), (fun h ↦ nomatch h)⟩
        left_inv := fun x ↦ Prod.ext (funext fun h ↦ nomatch h) (funext fun h ↦ nomatch h)
        right_inv := fun _ ↦ rfl }
  apply restricts_of_reindex e
  intro c
  rfl

/-- Each wire on the used parties is a restriction of their local diagonal. -/
theorem wireDistance_le_subpartyExponent (a b : I) :
    F.wireDistance (.inl a) (.inl b) ≤ F.subpartyExponent := by
  have hval : F.wireDimension (.inl a) (.inl b) 2 ≤ F.embeddedValue 2 := by
    change (F.value (wire (.inl a) (.inl b) (Fin 2)) : ℝ) ≤
      F.value (trivialExtension O (diagonal (Fin 2)))
    rw [← F.value_eq_of_mutual (trivialExtension_wire a b (Fin 2))]
    exact F.monotone (trivialExtension_restricts (diagonal_restricts_wire a b (Fin 2)))
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : 1 < (2 : ℝ))).le
  exact Real.log_le_log (zero_lt_one.trans_le (F.one_le_wireDimension _ _ (by decide))) hval

/-- All wire distances are scaled by the same positive reciprocal diagonal
exponent upon passing to the smaller spectrum. -/
theorem subpartyNormalization_wireDistance (hpos : 0 < F.subpartyExponent) (a b : I) :
    (F.subpartyNormalization hpos).wireDistance a b =
      F.wireDistance (.inl a) (.inl b) / F.subpartyExponent := by
  change Real.log ((F.subpartyNormalization hpos).value (wire a b (Fin 2))) / Real.log 2 =
    (Real.log (F.value (wire (.inl a) (.inl b) (Fin 2))) / Real.log 2) / F.subpartyExponent
  rw [subpartyNormalization_value, F.value_eq_of_mutual (trivialExtension_wire a b (Fin 2)),
    NNReal.coe_rpow, Real.log_rpow]
  · ring
  · exact zero_lt_one.trans_le (F.one_le_wireDimension _ _ (by decide : 0 < 2))

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
