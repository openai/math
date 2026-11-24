import OAI.Computability.VPVNP.WireTensor

/-!
# Tensor identities under mutual local restriction

Regrouping or permuting tensor factors only relabels their local bases.
The diagonal with empty bases represents zero under local restriction.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v

namespace WireTensor

variable {k : Type u} {J : Type v} [CommSemiring k] [Fintype J]

/-- The simple tensor is the multiplicative unit up to local restriction. -/
theorem tensorProduct_unit_mutual (T : Tensor.{u,v,0} k J) :
    Restricts (tensorProduct T (unit.{u,v,0})) T ∧
      Restricts T (tensorProduct T (unit.{u,v,0})) := by
  apply restricts_of_reindex (fun j ↦ (Equiv.prodPUnit (T.Basis j)).symm)
  intro x
  exact (mul_one (T.coeff x)).symm

/-- Reassociating three tensor factors preserves the local restriction class. -/
theorem tensorProduct_assoc_mutual (T U V : Tensor.{u,v,0} k J) :
    Restricts (tensorProduct (tensorProduct T U) V) (tensorProduct T (tensorProduct U V)) ∧
      Restricts (tensorProduct T (tensorProduct U V)) (tensorProduct (tensorProduct T U) V) := by
  apply restricts_of_reindex (fun j ↦ (Equiv.prodAssoc (T.Basis j) (U.Basis j) (V.Basis j)).symm)
  intro x
  exact (mul_assoc _ _ _).symm

/-- Swapping the two factors preserves the local restriction class. -/
theorem tensorProduct_comm_mutual (T U : Tensor.{u,v,0} k J) :
    Restricts (tensorProduct T U) (tensorProduct U T) ∧
      Restricts (tensorProduct U T) (tensorProduct T U) := by
  apply restricts_of_reindex (fun j ↦ Equiv.prodComm (U.Basis j) (T.Basis j))
  intro x
  exact mul_comm _ _

variable [Nonempty J]

/-- The empty diagonal is the additive unit up to local restriction. -/
theorem directSum_zero_mutual (T : Tensor.{u,v,0} k J) :
    Restricts (directSum T (diagonal (Fin 0))) T ∧
      Restricts T (directSum T (diagonal (Fin 0))) := by
  apply restricts_of_reindex (fun j ↦ (Equiv.sumEmpty (T.Basis j) (Fin 0)).symm)
  intro x
  exact (directSum_coeff_inl T (diagonal (Fin 0)) x).symm

/-- Every tensor restricts to the empty diagonal. -/
theorem restricts_zero (T : Tensor.{u,v,0} k J) : Restricts T (diagonal (Fin 0)) := by
  refine ⟨fun _ _ _ ↦ 0, ?_⟩
  funext c
  exact Fin.elim0 (c (Classical.choice ‹Nonempty J›))

/-- The empty diagonal restricts exactly to tensors with zero coefficient array. -/
theorem zero_restricts_iff (T : Tensor.{u,v,0} k J) :
    Restricts (diagonal (Fin 0)) T ↔ T.coeff = 0 := by
  constructor
  · rintro ⟨L, hL⟩
    rw [← hL]
    funext x
    simp [applyLocal, diagonal]
  · intro hT
    refine ⟨fun _ _ _ ↦ 0, ?_⟩
    rw [hT]
    funext x
    simp [applyLocal, diagonal]

/-- The tensor product with the empty diagonal has zero coefficient array. -/
theorem tensorProduct_zero_mutual (T : Tensor.{u,v,0} k J) :
    Restricts (tensorProduct T (diagonal (Fin 0))) (diagonal (Fin 0)) ∧
      Restricts (diagonal (Fin 0)) (tensorProduct T (diagonal (Fin 0))) := by
  refine ⟨restricts_zero _, (zero_restricts_iff _).2 ?_⟩
  funext x
  exact Fin.elim0 (x (Classical.choice ‹Nonempty J›)).2

end WireTensor

end VPVNP
end Computability
end OAI
