import OAI.Computability.VPVNP.TensorRestrictionSemiring

/-!
# From a restriction by a direct sum to an ordinary sum of images

The base identities in Theorem 6.1 use one local linear map per party for
each summand. A restriction from the direct sum supplies these maps by
restricting the original matrices to each summand's coordinate block.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v

namespace WireTensor

open RestrictionClass

variable {k : Type u} {J : Type v} [Field k] [Fintype J] [Nonempty J]

/-- A finite direct sum dominating the demand yields an ordinary sum identity
with exactly the same indices, in the demand's given coordinate spaces. -/
theorem ordinary_sum_of_class_le_finset {ι : Type*} (s : Finset ι)
    (X : Tensor.{u,v,0} k J) (Y : ι → Tensor.{u,v,0} k J)
    (h : ofTensor X ≤ ∑ i ∈ s, ofTensor (Y i)) :
    ∃ L : ∀ i j, X.Basis j → (Y i).Basis j → k, X.coeff = ∑ i ∈ s, applyLocal (L i) (Y i).coeff := by
  classical
  induction s using Finset.induction_on generalizing X with
  | empty =>
    simp only [Finset.sum_empty] at h ⊢
    exact ⟨fun _ _ _ _ => 0, (zero_restricts_iff X).1 h⟩
  | insert a s ha ih =>
    obtain ⟨U, hU⟩ := ofTensor_surjective (∑ i ∈ s, ofTensor (Y i))
    rw [Finset.sum_insert ha, ← hU, ← ofTensor_directSum] at h
    obtain ⟨M, hM⟩ := (ofTensor_le_iff _ _).1 h
    let left := fun j c b => M j c (Sum.inl b)
    let right := fun j c b => M j c (Sum.inr b)
    let R : Tensor.{u,v,0} k J := .mk X.Basis X.finiteBasis (applyLocal right U.coeff)
    have hR : ofTensor R ≤ ∑ i ∈ s, ofTensor (Y i) := hU ▸ ⟨right, rfl⟩
    obtain ⟨N, hN⟩ := ih R hR
    let L := Function.update N a left
    refine ⟨L, ?_⟩
    calc
      X.coeff = applyLocal left (Y a).coeff + R.coeff :=
        hM.symm.trans (applyLocal_directSum (Y a) U M)
      _ = applyLocal (L a) (Y a).coeff + ∑ i ∈ s, applyLocal (L i) (Y i).coeff := by
        rw [hN]
        congr 1
        · simp [L]
        · exact Finset.sum_congr rfl fun i hi => by simp [L, ne_of_mem_of_not_mem hi ha]
      _ = _ := by rw [Finset.sum_insert ha]

/-- The direct-sum restriction in the fixed-motif comparison gives one
ordinary summand for each supply tensor. -/
theorem ordinary_sum_of_class_le {ι : Type*} [Fintype ι]
    (X : Tensor.{u,v,0} k J) (Y : ι → Tensor.{u,v,0} k J)
    (h : ofTensor X ≤ ∑ i, ofTensor (Y i)) :
    ∃ L : ∀ i j, X.Basis j → (Y i).Basis j → k, X.coeff = ∑ i, applyLocal (L i) (Y i).coeff :=
  ordinary_sum_of_class_le_finset Finset.univ X Y h

end WireTensor

end VPVNP
end Computability
end OAI
