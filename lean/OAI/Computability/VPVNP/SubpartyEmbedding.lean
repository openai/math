import OAI.Computability.VPVNP.WireSpectrum

/-!
# Trivial legs outside a subset of parties

Section 2.2 of *VP and VNP differ over every field* restricts a spectral
point to a smaller party set, with a one-dimensional leg at every remaining
party. The embedding preserves products and restrictions. The embedded
direct sum is a restriction of the full-party direct sum.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v w

namespace WireTensor

variable {k : Type u} {I : Type v} {O : Type w}

/-- Extend a tensor to the disjoint union of its parties with a new set, giving each new party
a one-dimensional leg. -/
def trivialExtension (O : Type w) (T : Tensor.{u, v, 0} k I) :
    Tensor.{u, max v w, 0} k (I ⊕ O) where
  Basis
    | .inl i => T.Basis i
    | .inr _ => PUnit
  finiteBasis
    | .inl _ => inferInstance
    | .inr _ => inferInstance
  coeff x := T.coeff (fun i ↦ x (.inl i))

private def extendTuple (T : Tensor.{u, v, 0} k I) (x : ∀ i, T.Basis i) :
    (j : I ⊕ O) → (trivialExtension O T).Basis j
  | .inl i => x i
  | .inr _ => .unit

private def tupleEquiv (T : Tensor.{u, v, 0} k I) :
    ((j : I ⊕ O) → (trivialExtension O T).Basis j) ≃ ((i : I) → T.Basis i) where
  toFun x i := x (.inl i)
  invFun := extendTuple T
  left_inv x := by
    funext j
    cases j with
    | inl i => rfl
    | inr o => exact Subsingleton.elim (α := PUnit) _ _
  right_inv _ := rfl

variable [Fintype I] [Fintype O] [Field k]

/-- Local maps supported on the old parties act on the original tensor. -/
private theorem applyLocal_trivialExtension (T : Tensor.{u, v, 0} k I) {C : I ⊕ O → Type}
    (L : ∀ j, C j → (trivialExtension O T).Basis j → k)
    (hout : ∀ (o : O) c b, L (.inr o) c b = 1) (c : ∀ j, C j) :
    applyLocal L (trivialExtension O T).coeff c =
      applyLocal (fun i ↦ L (.inl i)) T.coeff (fun i ↦ c (.inl i)) := by
  classical
  let : DecidableEq (I ⊕ O) := Classical.decEq _
  unfold applyLocal
  apply Fintype.sum_equiv (tupleEquiv T)
  intro x
  rw [Fintype.prod_sum_type]
  simp [hout, tupleEquiv, trivialExtension]
  rfl

/-- Local restrictions extend to the larger set of parties. -/
theorem trivialExtension_restricts {T U : Tensor.{u, v, 0} k I} (h : Restricts T U) :
    Restricts (trivialExtension O T) (trivialExtension O U) := by
  obtain ⟨L, hL⟩ := h
  let K : ∀ j, (trivialExtension O U).Basis j → (trivialExtension O T).Basis j → k :=
    fun j ↦ match j with
    | .inl i => L i
    | .inr _ => fun _ _ ↦ 1
  refine ⟨K, ?_⟩
  funext c
  exact (applyLocal_trivialExtension T K (fun _ _ _ ↦ rfl) c).trans (congrFun hL _)

/-- Extension commutes with the tensor product after identifying singleton factors. -/
theorem trivialExtension_product (T U : Tensor.{u, v, 0} k I) :
    Restricts (trivialExtension O (tensorProduct T U))
      (tensorProduct (trivialExtension O T) (trivialExtension O U)) ∧
    Restricts (tensorProduct (trivialExtension O T) (trivialExtension O U))
      (trivialExtension O (tensorProduct T U)) := by
  apply restricts_of_reindex (fun j ↦ match j with
    | .inl _ => Equiv.refl _
    | .inr _ => Equiv.prodPUnit PUnit)
  intro c
  rfl

theorem trivialExtension_unit :
    Restricts (trivialExtension O (unit (k := k) (J := I))) (unit.{u, max v w, 0}) ∧
    Restricts (unit.{u, max v w, 0}) (trivialExtension O (unit (k := k) (J := I))) := by
  apply restricts_of_reindex (fun j ↦ match j with
    | .inl _ => Equiv.refl _
    | .inr _ => Equiv.refl _)
  intro c
  rfl

/-- Merging the two singleton blocks at each outside party produces the
embedded direct sum on the old parties. -/
theorem trivialExtension_directSum (T U : Tensor.{u, v, 0} k I) :
    Restricts (directSum (trivialExtension O T) (trivialExtension O U))
      (trivialExtension O (directSum T U)) := by
  classical
  let L : ∀ j, (trivialExtension O (directSum T U)).Basis j →
      ((trivialExtension O T).Basis j ⊕ (trivialExtension O U).Basis j) → k :=
    fun j ↦ match j with
    | .inl _ => fun c b ↦ if c = b then 1 else 0
    | .inr _ => fun _ _ ↦ 1
  refine ⟨L, ?_⟩
  refine (applyLocal_directSum (trivialExtension O T) (trivialExtension O U) L).trans ?_
  funext c
  rw [Pi.add_apply, applyLocal_trivialExtension T _ (fun _ _ _ ↦ rfl),
    applyLocal_trivialExtension U _ (fun _ _ _ ↦ rfl)]
  simp only [L, trivialExtension, directSum, Pi.add_apply]
  congr 1 <;> congr 2 <;> funext i c b <;> split_ifs with hb <;> simp [hb]

end WireTensor

end VPVNP
end Computability
end OAI
