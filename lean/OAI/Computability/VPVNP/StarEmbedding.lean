import OAI.Computability.VPVNP.StarContraction
import OAI.Computability.VPVNP.TensorRestrictionSemiring

/-!
# Embedded old tensor classes

Adjoining the trivial center leg preserves parallel products and reflects
local restrictions. The old factors in a monomial of Theorem 2.4 can thus
be multiplied in the old party set, then embedded as one tensor class.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v

namespace WireTensor.RestrictionClass

variable {k : Type u} {J : Type v} [Field k] [Fintype J] [Nonempty J]

/-- Embedding an old tensor induces a multiplicative map on restriction
classes which also preserves zero. -/
noncomputable def embedOldClass : RestrictionClass k J →*₀ RestrictionClass k (Option J) where
  toFun := Quotient.map embedOld fun _ _ h ↦ ⟨embedOld_restricts h.1, embedOld_restricts h.2⟩
  map_zero' := by
    change ofTensor (embedOld (diagonal (Fin 0))) = 0
    apply (ofTensor_eq_zero_iff _).2
    funext x
    simp [embedOld, diagonal]
  map_one' := by
    change ofTensor (embedOld unit) = ofTensor unit
    apply (ofTensor_eq_iff _ _).2
    let e (j : Option J) : (unit (k := k) (J := Option J)).Basis j ≃ (embedOld (unit.{u,v,0} (k := k) (J := J))).Basis j :=
      match j with
      | none => Equiv.refl _
      | some _ => Equiv.refl _
    exact restricts_of_reindex e (fun _ ↦ rfl)
  map_mul' a b := by
    obtain ⟨T, rfl⟩ := ofTensor_surjective a
    obtain ⟨U, rfl⟩ := ofTensor_surjective b
    exact (ofTensor_eq_iff _ _).2 (embedOld_product_mutual T U)

@[simp] theorem embedOldClass_ofTensor (T : Tensor.{u,v,0} k J) :
    embedOldClass (ofTensor T) = ofTensor (embedOld T) := rfl

/-- Embedding a trivial center leg preserves and reflects restriction. To
reflect a restriction, contract the demand with the unit covector and pull
it back to the singleton center basis of the supply. -/
@[simp] theorem embedOldClass_le_iff (x y : RestrictionClass k J) :
    embedOldClass x ≤ embedOldClass y ↔ x ≤ y := by
  obtain ⟨T, rfl⟩ := ofTensor_surjective x
  obtain ⟨U, rfl⟩ := ofTensor_surjective y
  change Restricts (embedOld U) (embedOld T) ↔ Restricts U T
  refine ⟨?_, embedOld_restricts⟩
  intro h
  obtain ⟨ξ, hξ⟩ := contractCenter_restricts h (fun _ ↦ 1)
  rw [contractCenter_embedOld_one] at hξ
  exact (restricts_contractCenter_embedOld U ξ).trans hξ

/-- Adjoining a trivial leg is faithful on tensor restriction classes. -/
theorem embedOldClass_injective : Function.Injective (embedOldClass (k := k) (J := J)) := by
  intro x y h
  exact le_antisymm ((embedOldClass_le_iff _ _).1 h.le) ((embedOldClass_le_iff _ _).1 h.ge)

/-- The concrete product indexed by `Fin n` represents the `n`-th power
in the semiring of restriction classes. -/
@[simp] theorem ofTensor_tensorPowerFin (n : ℕ) (T : Tensor.{u,v,0} k J) :
    ofTensor (tensorPowerFin n T) = ofTensor T ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    change ofTensor (tensorPowerFin 0 T) = ofTensor unit
    apply (ofTensor_eq_iff _ _).2
    apply restricts_of_reindex (fun j ↦ Equiv.ofUnique PUnit (Fin 0 → T.Basis j))
    intro x
    simp [tensorPowerFin, unit]
  | succ n ih =>
    rw [pow_succ', ← ih, ← ofTensor_tensorProduct]
    apply (ofTensor_eq_iff _ _).2
    apply restricts_of_reindex (fun j ↦ Fin.consEquiv (fun _ : Fin (n + 1) ↦ T.Basis j))
    intro x
    change (j : J) → T.Basis j × (Fin n → T.Basis j) at x
    change T.coeff (fun j ↦ (x j).1) * (∏ i, T.coeff (fun j ↦ (x j).2 i)) = _
    change _ = ∏ i, T.coeff (fun j ↦ Fin.cons (α := fun _ : Fin (n + 1) ↦ T.Basis j) (x j).1 (x j).2 i)
    rw [Fin.prod_univ_succ]
    simp

end WireTensor.RestrictionClass

end VPVNP
end Computability
end OAI
