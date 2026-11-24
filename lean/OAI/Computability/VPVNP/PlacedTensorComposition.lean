import OAI.Computability.VPVNP.PlacedTensor

/-! # Composing placements of tensor legs

Regrouping factors twice gives the same tensor as placing them along the
composite map. The identity places each original leg back at its own
party, and the inclusion into `Option J` adds a singleton center leg.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

variable {k : Type*} [CommSemiring k] {R J K : Type}
  [Fintype R] [Fintype J] [Fintype K]

/-- Two successive placements induce a canonical bijection of the grouped local bases. -/
theorem placeTensor_comp_mutual (p : R → J) (q : J → K) (T : Tensor k R) :
    Restricts (placeTensor q (placeTensor p T)) (placeTensor (q ∘ p) T) ∧
    Restricts (placeTensor (q ∘ p) T) (placeTensor q (placeTensor p T)) := by
  let e (x : K) : ((r : R) → x = q (p r) → T.Basis r) ≃
      ((j : J) → x = q j → (r : R) → j = p r → T.Basis r) :=
    { toFun := fun a _ h r hr ↦ a r (h.trans (congrArg q hr))
      invFun := fun a r h ↦ a (p r) h r rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun a ↦ by
        funext j h r hr
        subst j
        rfl }
  exact restricts_of_reindex e (fun _ ↦ rfl)

/-- Placing a tensor at its original parties simply relabels its bases. -/
theorem placeTensor_id_mutual (T : Tensor k R) :
    Restricts T (placeTensor id T) ∧ Restricts (placeTensor id T) T := by
  let e (r : R) : ((s : R) → r = s → T.Basis s) ≃ T.Basis r :=
    { toFun := fun a ↦ a r rfl
      invFun := fun a s h ↦ h ▸ a
      left_inv := fun a ↦ by funext s h; subst s; rfl
      right_inv := fun _ ↦ rfl }
  exact restricts_of_reindex e (fun _ ↦ rfl)

/-- Placing the old parties by the canonical injection into `Option` is the
trivial extension of the tensor at the added party. -/
theorem placeTensor_some_mutual (T : Tensor k R) :
    Restricts (embedOld T) (placeTensor some T) ∧ Restricts (placeTensor some T) (embedOld T) := by
  let e (j : Option R) : ((r : R) → j = some r → T.Basis r) ≃ (embedOld T).Basis j :=
    match j with
    | none =>
      { toFun := fun _ ↦ PUnit.unit
        invFun := fun _ _ h ↦ nomatch h
        left_inv := fun _ ↦ by funext r h; exact nomatch h
        right_inv := fun _ ↦ rfl }
    | some s =>
      { toFun := fun a ↦ a s rfl
        invFun := fun a r h ↦ (Option.some.inj h) ▸ a
        left_inv := fun a ↦ by funext r h; obtain rfl := Option.some.inj h; rfl
        right_inv := fun _ ↦ rfl }
  exact restricts_of_reindex e (fun _ ↦ rfl)

end WireTensor

end VPVNP
end Computability
end OAI
