import OAI.Computability.VPVNP.StarContraction
import OAI.Computability.VPVNP.WireSpectrum
import Mathlib.Order.ConditionallyCompleteLattice.Group

/-!
# Supremum of spectral values of center contractions

In the proof of Theorem 2.4 of *VP and VNP differ over every field*, the
center contraction may use any covector, including on products of several
wires. Its supremal spectral value is monotone under local restrictions.
Direct sums separate into independent blocks, and an embedded old factor
can be evaluated separately.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v
open scoped NNReal

namespace WireTensor.SpectralPoint

variable {k : Type u} {J : Type v} [Field k] [Fintype J] (F : SpectralPoint k J)

/-- Supremum over all covectors on the center, before acting at the old parties. -/
noncomputable def contractionValue (T : Tensor.{u,v,0} k (Option J)) : ℝ≥0 :=
  ⨆ ξ, F.value (contractCenter T ξ)

/-- A common bound for all contractions depends only on the dimensions at the old parties. -/
theorem contractionValues_bddAbove [Nonempty J] (T : Tensor.{u,v,0} k (Option J)) :
    BddAbove (Set.range (fun ξ ↦ F.value (contractCenter T ξ))) := by
  refine ⟨((∏ j : J, Fintype.card (T.Basis (some j)) : ℕ) : ℝ≥0), ?_⟩
  rintro _ ⟨ξ, rfl⟩
  exact F.value_le_basis_product (contractCenter T ξ)

variable [Nonempty J]

theorem value_le_contractionValue (T : Tensor.{u,v,0} k (Option J)) (ξ : T.Basis none → k) :
    F.value (contractCenter T ξ) ≤ F.contractionValue T :=
  le_ciSup (F.contractionValues_bddAbove T) ξ

theorem contractionValue_le_basis_product (T : Tensor.{u,v,0} k (Option J)) :
    F.contractionValue T ≤ (∏ j : J, Fintype.card (T.Basis (some j)) : ℕ) :=
  ciSup_le fun ξ ↦ F.value_le_basis_product (contractCenter T ξ)

/-- The real least upper bound used in the root-limit estimates. -/
theorem isLUB_contractionValue (T : Tensor.{u,v,0} k (Option J)) :
    IsLUB (Set.range (fun ξ ↦ (F.value (contractCenter T ξ) : ℝ))) (F.contractionValue T : ℝ) := by
  rw [contractionValue, NNReal.coe_iSup]
  apply isLUB_ciSup
  refine ⟨(F.contractionValue T : ℝ), ?_⟩
  rintro _ ⟨ξ, rfl⟩
  exact NNReal.coe_le_coe.mpr (F.value_le_contractionValue T ξ)

/-- A restriction can only decrease the supremal contraction value. -/
theorem contractionValue_mono {Y X : Tensor.{u,v,0} k (Option J)} (h : Restricts Y X) :
    F.contractionValue X ≤ F.contractionValue Y := by
  apply ciSup_le
  intro ξ
  obtain ⟨η, hη⟩ := contractCenter_restricts h ξ
  exact (F.monotone hη).trans (F.value_le_contractionValue Y η)

omit [Nonempty J] in
/-- Each contraction of a zero array is zero. -/
theorem contractionValue_zero (T : Tensor.{u,v,0} k (Option J)) (hT : T.coeff = 0) :
    F.contractionValue T = 0 := by
  apply le_antisymm _ bot_le
  apply ciSup_le
  intro ξ
  apply (F.value_zero _ ?_).le
  funext x
  simp [contractCenter, hT]

/-- Contracting the unit by the all-ones covector attains the dimensional upper bound. -/
theorem contractionValue_unit : F.contractionValue unit = 1 := by
  apply le_antisymm
  · refine (F.contractionValue_le_basis_product _).trans_eq ?_
    change ((∏ _ : J, Fintype.card PUnit.{1} : ℕ) : ℝ≥0) = 1
    simp
  · have hu : contractCenter (unit.{u,v,0} (k := k) (J := Option J)) (fun _ ↦ 1) = unit := by
      unfold contractCenter unit
      congr 1
      funext x
      simp
    rw [← F.value_unit, ← hu]
    exact F.value_le_contractionValue _ _

/-- A nonzero extended tensor has a center contraction of supremal value at least one. -/
theorem one_le_contractionValue (T : Tensor.{u,v,0} k (Option J)) (hT : T.coeff ≠ 0) :
    1 ≤ F.contractionValue T := by
  rw [← F.contractionValue_unit]
  exact F.contractionValue_mono (restricts_unit_of_ne_zero T hT)

/-- The two blocks of the center admit independent covectors, so the
supremum of contractions is additive on direct sums. -/
theorem contractionValue_directSum (T U : Tensor.{u,v,0} k (Option J)) :
    F.contractionValue (directSum T U) = F.contractionValue T + F.contractionValue U := by
  apply le_antisymm
  · apply ciSup_le
    intro ξ
    rw [contractCenter_directSum, F.value_directSum]
    exact add_le_add (F.value_le_contractionValue T _) (F.value_le_contractionValue U _)
  · apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_add, contractionValue, NNReal.coe_iSup]
    apply ciSup_add_ciSup_le
    intro ξ η
    have h := F.value_le_contractionValue (directSum T U) (Sum.elim ξ η)
    rw [contractCenter_directSum T U (Sum.elim ξ η), F.value_directSum] at h
    change F.value (contractCenter T ξ) + F.value (contractCenter U η) ≤ F.contractionValue _ at h
    simpa only [contractionValue, NNReal.coe_iSup, NNReal.coe_add] using (NNReal.coe_le_coe.mpr h)

omit [Nonempty J] in
/-- A spectral extension dominates every old contraction of an extended tensor. -/
theorem contractionValue_le_extension (H : SpectralPoint k (Option J))
    (hH : ∀ T, H.value (embedOld T) = F.value T) (U : Tensor.{u,v,0} k (Option J)) :
    F.contractionValue U ≤ H.value U := by
  apply ciSup_le
  intro ξ
  rw [← hH]
  exact H.monotone (restricts_embedOld_contractCenter U ξ)

/-- The unit center leg on an embedded old tensor can be contracted with coefficient one. -/
theorem contractionValue_embedOld (T : Tensor.{u,v,0} k J) :
    F.contractionValue (embedOld T) = F.value T := by
  apply le_antisymm
  · exact ciSup_le fun ξ ↦ F.monotone (restricts_contractCenter_embedOld T ξ)
  · have h := F.value_le_contractionValue (embedOld T) (fun _ ↦ 1)
    rwa [contractCenter_embedOld_one] at h

/-- Embedded old tensors multiply the contraction value by their spectral value. -/
theorem contractionValue_old_product (T : Tensor.{u,v,0} k J) (U : Tensor.{u,v,0} k (Option J)) :
    F.contractionValue (tensorProduct (embedOld T) U) = F.value T * F.contractionValue U := by
  apply le_antisymm
  · apply ciSup_le
    intro ξ
    rw [contractCenter_old_product, F.value_tensorProduct]
    exact mul_le_mul_right (F.value_le_contractionValue U _) _
  · apply NNReal.mul_iSup_le
    intro η
    have h := F.value_le_contractionValue (tensorProduct (embedOld T) U) (fun z ↦ η z.2)
    rwa [contractCenter_old_product, F.value_tensorProduct] at h

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
