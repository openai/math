import OAI.Computability.VPVNP.WireSpectrum

/-! # Regrouping a restriction along an arbitrary placement of its parties -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP.WireTensor Finset
open scoped Classical BigOperators

variable {K V J : Type} [Field K] [Fintype V] [Fintype J]

noncomputable abbrev groupAt (f : V → J) (T : Tensor K V) := placedTensor f T.Basis T.coeff

private def groupBasisEquiv (f : V → J) (B : V → Type*) :
    ((j : J) → (v : V) → j = f v → B v) ≃ ((v : V) → B v) where
  toFun x v := x (f v) v rfl
  invFun x _ v _ := x v
  left_inv x := by funext j v eq; subst j; rfl
  right_inv _ := rfl

/-- Grouping factors at the same site preserves every local restriction. -/
theorem group_restricts (f : V → J) {T U : Tensor K V} (h : Restricts T U) :
    Restricts (groupAt f T) (groupAt f U) := by
  classical
  obtain ⟨L,eq⟩ := h
  let m (j : J) (c : (groupAt f U).Basis j) (b : (groupAt f T).Basis j) :=
    ∏ v, if e : j = f v then L v (c v e) (b v e) else 1
  refine ⟨m,?_⟩
  funext c
  change (∑ b, (∏ j, m j (c j) (b j))*(groupAt f T).coeff b) = _
  change _ = U.coeff (fun v => c (f v) v rfl)
  rw [← eq]
  apply Fintype.sum_equiv (groupBasisEquiv f T.Basis)
  intro b
  change (∏ j, ∏ v, if e : j = f v then L v (c j v e) (b j v e) else 1)*_ = _*_
  congr 1
  rw [prod_comm]
  apply prod_congr rfl
  intro v _
  rw [prod_eq_single (f v)]
  · simp [groupBasisEquiv]
  · intro j _ hj
    simp [hj]
  · simp

private def groupProductEquiv (f : V → J) (T U : Tensor K V) (j : J) :
    (tensorProduct (groupAt f T) (groupAt f U)).Basis j ≃ (groupAt f (tensorProduct T U)).Basis j where
  toFun p v h := (p.1 v h,p.2 v h)
  invFun p := (fun v h => (p v h).1,fun v h => (p v h).2)
  left_inv _ := rfl
  right_inv _ := rfl

private def groupFamilyEquiv {R : Type} [Fintype R] (f : V → J) (T : R → Tensor K V) (j : J) :
    (tensorFamilyProduct (fun r => groupAt f (T r))).Basis j ≃
      (groupAt f (tensorFamilyProduct T)).Basis j where
  toFun p v h r := p r v h
  invFun p r v h := p v h r
  left_inv _ := rfl
  right_inv _ := rfl

private def groupWireEquiv {E : Type} [Fintype E] (f : V → J) (a b : E → V) (B : E → Type)
    [∀ e, Fintype (B e)] (j : J) :
    (wireNetwork (k := K) (f ∘ a) (f ∘ b) B).Basis j ≃
      (groupAt f (wireNetwork (k := K) a b B)).Basis j where
  toFun p v h := (fun e hv => p.1 e (h.trans (congrArg f hv)),
    fun e hv => p.2 e (h.trans (congrArg f hv)))
  invFun p := (fun e h => (p (a e) h).1 e rfl,fun e h => (p (b e) h).2 e rfl)
  left_inv _ := rfl
  right_inv p := by
    funext v h
    apply Prod.ext <;> funext e hv <;> subst v <;> rfl

theorem value_group_product (F : SpectralPoint K J) (f : V → J) (T U : Tensor K V) :
    F.value (groupAt f (tensorProduct T U)) = F.value (groupAt f T)*F.value (groupAt f U) :=
  (F.value_eq_of_mutual (restricts_of_reindex (groupProductEquiv f T U) (fun _ => rfl))).trans
    (F.value_tensorProduct _ _)

theorem value_group_family {R : Type} [Fintype R] (F : SpectralPoint K J) (f : V → J)
    (T : R → Tensor K V) :
    F.value (groupAt f (tensorFamilyProduct T)) = ∏ r, F.value (groupAt f (T r)) :=
  (F.value_eq_of_mutual (restricts_of_reindex (groupFamilyEquiv f T) (fun _ => rfl))).trans
    (F.value_tensorFamilyProduct _)

theorem value_group_wires {E : Type} [Fintype E] (F : SpectralPoint K J) (f : V → J)
    (a b : E → V) (B : E → Type) [∀ e, Fintype (B e)] :
    F.value (groupAt f (wireNetwork a b B)) = F.value (wireNetwork (f ∘ a) (f ∘ b) B) :=
  F.value_eq_of_mutual (restricts_of_reindex (groupWireEquiv (K := K) f a b B) (fun _ => rfl))

end OAI.Computability.MultitapeWeakETH
