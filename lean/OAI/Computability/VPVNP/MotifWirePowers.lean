import OAI.Computability.VPVNP.TensorRestrictionSemiring

/-!
# Width arithmetic for binary wire networks

A wire of width `w` has `2 ^ w` index values. Concatenating two indices at
both endpoints multiplies the corresponding networks under tensor product.
This realizes repetitions of a motif as ordinary powers of its restriction
class, including for loops and repeated edges.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor.RestrictionClass

universe u v

variable {k : Type u} {J : Type v} {E : Type} [Field k] [Fintype J] [Fintype E]

/-- The restriction class of a graph with an integer bit width at each edge. -/
noncomputable def binaryNetworkClass (a b : E → J) (w : E → ℕ) : RestrictionClass k J :=
  ofTensor (wireNetwork a b (fun e ↦ Fin (2 ^ w e)))

private def joinBasis (a b : E → J) {I U R : E → Type}
    [∀ e, Fintype (I e)] [∀ e, Fintype (U e)] [∀ e, Fintype (R e)]
    (f : ∀ e, I e × U e ≃ R e) (j : J) :
    (tensorProduct (wireNetwork (k := k) a b I) (wireNetwork a b U)).Basis j ≃
      (wireNetwork (k := k) a b R).Basis j where
  toFun x := ⟨fun e h ↦ f e (x.1.1 e h, x.2.1 e h), fun e h ↦ f e (x.1.2 e h, x.2.2 e h)⟩
  invFun x :=
    (⟨fun e h ↦ ((f e).symm (x.1 e h)).1, fun e h ↦ ((f e).symm (x.2 e h)).1⟩,
     ⟨fun e h ↦ ((f e).symm (x.1 e h)).2, fun e h ↦ ((f e).symm (x.2 e h)).2⟩)
  left_inv x := by
    rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩
    simp
    rfl
  right_inv x := by
    rcases x with ⟨_, _⟩
    simp
    rfl

private theorem multiply_indicators {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R]
    (h : R ↔ P ∧ Q) :
    (if P then (1 : k) else 0) * (if Q then 1 else 0) = (if R then 1 else 0) := by
  split_ifs <;> simp_all

/-- Adding widths pointwise amounts to taking the tensor product. -/
theorem binaryNetworkClass_add (a b : E → J) (w u : E → ℕ) :
    binaryNetworkClass (k := k) a b (fun e ↦ w e + u e) =
      binaryNetworkClass a b w * binaryNetworkClass a b u := by
  classical
  let f (e : E) : Fin (2 ^ w e) × Fin (2 ^ u e) ≃ Fin (2 ^ (w e + u e)) :=
    finProdFinEquiv.trans (finCongr (pow_add 2 (w e) (u e)).symm)
  apply (ofTensor_eq_iff _ _).2
  apply restricts_of_reindex (joinBasis (k := k) a b f)
  intro x
  simp only [tensorProduct, wireNetwork, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  have h : ((joinBasis (k := k) a b f (a e)) (x (a e))).1 e rfl =
      ((joinBasis (k := k) a b f (b e)) (x (b e))).2 e rfl ↔
      (x (a e)).1.1 e rfl = (x (b e)).1.2 e rfl ∧ (x (a e)).2.1 e rfl = (x (b e)).2.2 e rfl := by
    change f e (_, _) = f e (_, _) ↔ _
    rw [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  exact @multiply_indicators k _ _ _ _ (Classical.propDecidable _) (Classical.propDecidable _)
    (Classical.propDecidable _) h

/-- Width zero gives the tensor unit. -/
theorem binaryNetworkClass_zero (a b : E → J) :
    binaryNetworkClass (k := k) a b (fun _ ↦ 0) = 1 := by
  classical
  change ofTensor (wireNetwork (k := k) a b (fun _ ↦ Fin 1)) = ofTensor unit
  apply (ofTensor_eq_iff _ _).2
  let f (j : J) : PUnit ≃ ((e : E) → j = a e → Fin 1) × ((e : E) → j = b e → Fin 1) :=
    { toFun := fun _ ↦ edgeAssignment a b (I := fun _ ↦ Fin 1) (fun _ ↦ 0) j
      invFun := fun _ ↦ PUnit.unit
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
  apply restricts_of_reindex f
  intro x
  symm
  apply Finset.prod_eq_one
  intro e _
  exact ite_eq_left (Subsingleton.elim _ _)

variable [Nonempty J]

/-- Repeating all edge widths `n` times gives the `n`th power of the class. -/
theorem binaryNetworkClass_pow (a b : E → J) (w : E → ℕ) (n : ℕ) :
    binaryNetworkClass (k := k) a b (fun e ↦ n * w e) = binaryNetworkClass a b w ^ n := by
  induction n with
  | zero => simp [binaryNetworkClass_zero]
  | succ n ih => simp only [Nat.succ_mul, binaryNetworkClass_add, ih, pow_succ]

/-- The widths accumulated by a finite family of motifs give the product
of the corresponding restriction classes. -/
theorem binaryNetworkClass_sum {ι : Type*} (a b : E → J) (S : Finset ι) (ws : ι → E → ℕ) :
    binaryNetworkClass (k := k) a b (fun e ↦ ∑ i ∈ S, ws i e) =
      ∏ i ∈ S, binaryNetworkClass a b (ws i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [binaryNetworkClass_zero]
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi, binaryNetworkClass_add, ih]

end WireTensor.RestrictionClass

end VPVNP
end Computability
end OAI
