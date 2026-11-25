import OAI.LinearAlgebra.SpectralBooks.OldSiteEmbedding
import OAI.LinearAlgebra.SpectralBooks.ContractNonzero

/-! # The old price of an embedded tensor factor

Contracting the extra leg commutes with tensoring by a tensor supported on
the old sites. Maximizing over the contracting covector adds the old factor's
logarithmic price.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators NNReal Classical

noncomputable section

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

namespace Raw

omit [Nonempty I] in
/-- Old factors pass unchanged through contraction of the extra leg. -/
theorem contractNew_embedOld_mul (X : Raw.{v} I K) (T : Raw.{v} (Option I) K)
    (ξ : (X.embedOld.mul T).Leg none → K) :
    ofRaw ((X.embedOld.mul T).contractNew ξ) =
      ofRaw (X.mul (T.contractNew (fun b ↦ ξ (PUnit.unit, b)))) := by
  apply ofRaw_eq_iff.mpr
  apply reindex_equivalent (fun i ↦ Equiv.refl (X.Leg i × T.Leg (some i)))
  intro a
  change (∑ c : PUnit × T.Leg none, ξ c *
      (X.coeff (fun i ↦ (a i).1) * T.coeff (fun j ↦
        ((Equiv.piOptionEquivProd (β := (X.embedOld.mul T).Leg)).symm (c, a) j).2))) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  change (∑ b, ξ (PUnit.unit, b) *
      (X.coeff (fun i ↦ (a i).1) * T.coeff (fun j ↦
        ((Equiv.piOptionEquivProd (β := (X.embedOld.mul T).Leg)).symm ((PUnit.unit, b), a) j).2))) =
    X.coeff (fun i ↦ (a i).1) * ∑ b, ξ (PUnit.unit, b) *
      T.coeff (Equiv.piOptionEquivProd.symm (b, fun i ↦ (a i).2))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have eq : (fun j ↦
      ((Equiv.piOptionEquivProd (β := (X.embedOld.mul T).Leg)).symm ((PUnit.unit, b), a) j).2) =
      Equiv.piOptionEquivProd.symm (b, fun i ↦ (a i).2) := by
    funext j
    cases j <;> rfl
  rw [eq]
  ring

end Raw

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))

/-- At nonzero tensors, the contraction price is additive in an embedded old factor. -/
theorem contractionPrice_embedOld_mul (X : Raw.{v} I K) (T : Raw.{v} (Option I) K)
    (hX : X.coeff ≠ 0) (hT : T.coeff ≠ 0) :
    contractionPrice φ (X.embedOld.mul T) = rawLogPrice φ 1 X + contractionPrice φ T := by
  have hcontract (ξ : (X.embedOld.mul T).Leg none → K) :
      rawLogPrice φ 1 ((X.embedOld.mul T).contractNew ξ) =
        rawLogPrice φ 1 (X.mul (T.contractNew (fun b ↦ ξ (PUnit.unit, b)))) := by
    simp only [rawLogPrice, Raw.contractNew_embedOld_mul]
  have hlower (η : T.Leg none → K) (hn : (T.contractNew η).coeff ≠ 0) :
      rawLogPrice φ 1 X + rawLogPrice φ 1 (T.contractNew η) ≤
        contractionPrice φ (X.embedOld.mul T) := by
    have h := le_contractionPrice φ (X.embedOld.mul T) (fun c ↦ η c.2)
    rw [hcontract, rawLogPrice_mul φ 1 _ _ hX hn] at h
    exact h
  apply le_antisymm
  · apply ciSup_le
    intro ξ
    rw [hcontract]
    let U := T.contractNew (fun b ↦ ξ (PUnit.unit, b))
    change rawLogPrice φ 1 (X.mul U) ≤ _
    by_cases hu : U.coeff = 0
    · have hz : (X.mul U).coeff = 0 := by ext; simp [Raw.mul, hu]
      rw [rawLogPrice_zero φ 1 _ hz]
      exact add_nonneg (rawLogPrice_nonneg φ zero_le_one X) (contractionPrice_nonneg φ T)
    · rw [rawLogPrice_mul φ 1 _ _ hX hu]
      exact add_le_add_right (le_contractionPrice φ T _) _
  · suffices h : contractionPrice φ T ≤
        contractionPrice φ (X.embedOld.mul T) - rawLogPrice φ 1 X by linarith
    apply ciSup_le
    intro η
    by_cases hn : (T.contractNew η).coeff = 0
    · obtain ⟨ζ, hz⟩ := T.exists_contractNew_ne_zero hT
      have hp := hlower ζ hz
      have hzpos := rawLogPrice_nonneg φ zero_le_one (T.contractNew ζ)
      rw [rawLogPrice_zero φ 1 _ hn]
      linarith
    · have hp := hlower η hn
      linarith

/-- Tensoring a nonzero class by an old class adds its spectral log price. -/
theorem classContractionPrice_embedOldProduct_add (x : NonzeroProduct.{v} I K)
    (t : NonzeroProduct.{v} (Option I) K) :
    classContractionPrice φ (classOfProduct (embedOldProduct x + t)) =
      logPoint φ x + classContractionPrice φ (classOfProduct t) := by
  obtain ⟨X, hX⟩ := Quotient.exists_rep (classOfProduct x)
  obtain ⟨T, hT⟩ := Quotient.exists_rep (classOfProduct t)
  change ofRaw X = classOfProduct x at hX
  change ofRaw T = classOfProduct t at hT
  have h := contractionPrice_embedOld_mul φ X T
    (fun h ↦ x.toMul.property (hX.symm.trans ((ofRaw_eq_zero_iff _).2 h)))
    (fun h ↦ t.toMul.property (hT.symm.trans ((ofRaw_eq_zero_iff _).2 h)))
  change classContractionPrice φ (embedOldClass (classOfProduct x) * classOfProduct t) =
    Real.logb 2 (φ.val (classOfProduct x) : ℝ) + _
  rw [← hX, ← hT, embedOldClass_ofRaw, ← ofRaw_mul]
  change contractionPrice φ (X.embedOld.mul T) = _ + contractionPrice φ T
  simpa only [rawLogPrice, one_mul] using h

/-- The unit at the enlarged site set has contraction price zero. -/
@[simp] theorem classContractionPrice_one : classContractionPrice φ 1 = 0 := by
  let U := Raw.one.{v} (Option I) K
  change contractionPrice φ U = 0
  apply le_antisymm _ (contractionPrice_nonneg φ _)
  apply ciSup_le
  intro ξ
  let i₀ : I := Classical.choice inferInstance
  have h : (U.contractNew ξ).Restricts (Raw.one I K) := by
    refine ⟨fun i _ _ ↦ if i = i₀ then ξ PUnit.unit else 1, fun _ ↦ ?_⟩
    change (∑ b : PUnit, ξ b * (1 : K)) =
      ∑ _ : I → PUnit, (1 : K) * ∏ i, (if i = i₀ then ξ PUnit.unit else (1 : K))
    simp only [Fintype.sum_unique, mul_one, one_mul, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    exact Fintype.sum_unique (f := fun b : PUnit ↦ ξ b)
  simpa [rawLogPrice, φ.property.2.1] using rawLogPrice_mono φ zero_le_one h

/-- On an old class the contraction price recovers the prescribed spectral evaluation. -/
@[simp] theorem classContractionPrice_embedOldProduct (x : NonzeroProduct.{v} I K) :
    classContractionPrice φ (classOfProduct (embedOldProduct x)) = logPoint φ x := by
  simpa [show classOfProduct (0 : NonzeroProduct.{v} (Option I) K) = 1 from rfl] using
    classContractionPrice_embedOldProduct_add φ x 0

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
