import OAI.Computability.VPVNP.WireSpectrum

/-!
# Relabeling the parties of a spectral point

In Lemma 2.3 of *VP and VNP differ over every field*, the parties used by a
fixed pattern of labels are identified across different realizations. A
bijection of party sets transports all local restrictions and both tensor
operations, so it gives a spectral point with the corresponding wire distances.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v v' w

namespace WireTensor

variable {k : Type u} {J : Type v} {R : Type v'}

/-- Use a bijection to rename every party of a tensor. The finite local bases
are the same bases, indexed by the new party names. -/
def relabelTensor (e : J ≃ R) (T : Tensor.{u,v',w} k R) : Tensor.{u,v,w} k J where
  Basis j := T.Basis (e j)
  finiteBasis j := T.finiteBasis (e j)
  coeff x := T.coeff (Equiv.piCongrLeft T.Basis e x)

private theorem relabelTensor_coeff (e : J ≃ R) (T : Tensor.{u,v',w} k R)
    (x : (r : R) → T.Basis r) :
    (relabelTensor e T).coeff (fun j ↦ x (e j)) = T.coeff x :=
  congrArg T.coeff ((Equiv.piCongrLeft T.Basis e).apply_symm_apply x)

section
variable [CommSemiring k] [Fintype J] [Fintype R]

/-- Local contractions agree after reindexing the sum of basis assignments and
the product of local matrix entries. -/
private theorem applyLocal_relabel (e : J ≃ R) {B C : R → Type*} [∀ r, Fintype (B r)]
    (L : ∀ r, C r → B r → k) (f : Array k B) (c : (r : R) → C r) :
    applyLocal (B := fun j ↦ B (e j)) (C := fun j ↦ C (e j))
      (fun j ↦ L (e j)) (fun b ↦ f (Equiv.piCongrLeft B e b)) (fun j ↦ c (e j)) =
      applyLocal L f c := by
  classical
  unfold applyLocal
  symm
  apply Fintype.sum_equiv (Equiv.piCongrLeft B e).symm
  intro b
  simp only [Equiv.apply_symm_apply, Equiv.piCongrLeft_symm_apply]
  exact congrArg (· * f b) (e.prod_comp (fun r ↦ L r (c r) (b r))).symm

theorem Restricts.relabelTensor {T U : Tensor.{u,v',w} k R} (h : Restricts T U) (e : J ≃ R) :
    Restricts (relabelTensor e T) (relabelTensor e U) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun j ↦ L (e j), ?_⟩
  funext x
  obtain ⟨c, rfl⟩ := (Equiv.piCongrLeft U.Basis e).symm.surjective x
  exact (applyLocal_relabel e L T.coeff c).trans ((congrFun hL c).trans (relabelTensor_coeff e U c).symm)

private theorem relabelTensor_directSum (e : J ≃ R) (T U : Tensor.{u,v',w} k R) :
    Restricts (relabelTensor e (directSum T U)) (directSum (relabelTensor e T) (relabelTensor e U)) ∧
    Restricts (directSum (relabelTensor e T) (relabelTensor e U)) (relabelTensor e (directSum T U)) := by
  classical
  apply restricts_of_reindex (T := relabelTensor e (directSum T U))
    (U := directSum (relabelTensor e T) (relabelTensor e U)) (fun _ ↦ Equiv.refl _)
  intro x
  obtain ⟨c, rfl⟩ := (Equiv.piCongrLeft (fun r ↦ T.Basis r ⊕ U.Basis r) e).symm.surjective x
  have h₁ := applyLocal_relabel e (fun r (c : T.Basis r ⊕ U.Basis r) b ↦
    if c = Sum.inl b then 1 else 0) T.coeff c
  have h₂ := applyLocal_relabel e (fun r (c : T.Basis r ⊕ U.Basis r) b ↦
    if c = Sum.inr b then 1 else 0) U.coeff c
  exact (congrArg₂ (· + ·) h₁ h₂).trans (relabelTensor_coeff e (directSum T U) c).symm

omit [Fintype R] in
private theorem relabelTensor_tensorProduct (e : J ≃ R) (T U : Tensor.{u,v',w} k R) :
    Restricts (relabelTensor e (tensorProduct T U)) (tensorProduct (relabelTensor e T) (relabelTensor e U)) ∧
    Restricts (tensorProduct (relabelTensor e T) (relabelTensor e U)) (relabelTensor e (tensorProduct T U)) := by
  apply restricts_of_reindex (T := relabelTensor e (tensorProduct T U))
    (U := tensorProduct (relabelTensor e T) (relabelTensor e U)) (fun _ ↦ Equiv.refl _)
  intro x
  obtain ⟨c, rfl⟩ := (Equiv.piCongrLeft (fun r ↦ T.Basis r × U.Basis r) e).symm.surjective x
  exact (congrArg₂ (· * ·) (relabelTensor_coeff e T (fun r ↦ (c r).1))
    (relabelTensor_coeff e U (fun r ↦ (c r).2))).trans (relabelTensor_coeff e (tensorProduct T U) c).symm

omit [Fintype R] in
private theorem relabelTensor_wire (e : J ≃ R) (a b : J) (I : Type w) [Fintype I] :
    Restricts (relabelTensor e (wire (k := k) (e a) (e b) I)) (wire a b I) ∧
    Restricts (wire (k := k) a b I) (relabelTensor e (wire (e a) (e b) I)) := by
  let q (j a : J) : (j = a → I) ≃ (e j = e a → I) :=
    { toFun := fun f h ↦ f (e.injective h)
      invFun := fun f h ↦ f (congrArg e h)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  apply restricts_of_reindex (fun j ↦ (q j a).prodCongr (q j b))
  intro x
  let B (r : R) := (r = e a → I) × (r = e b → I)
  let y (j : J) : B (e j) := (q j a (x j).1, q j b (x j).2)
  classical
  change (if (x a).1 rfl = (x b).2 rfl then (1 : k) else 0) =
    if (Equiv.piCongrLeft B e y (e a)).1 rfl = (Equiv.piCongrLeft B e y (e b)).2 rfl then 1 else 0
  rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
  rfl
end

namespace SpectralPoint
variable [Field k] [Fintype J] [Fintype R]

/-- Pull a spectral point back along a bijection of its party labels. -/
noncomputable def relabel (F : SpectralPoint k J) (e : R ≃ J) : SpectralPoint k R where
  value T := F.value (relabelTensor e.symm T)
  monotone h := F.monotone (h.relabelTensor e.symm)
  value_unit := F.value_unit
  value_zero T h := F.value_zero _ (funext fun x ↦ congrFun h (Equiv.piCongrLeft T.Basis e.symm x))
  value_directSum T U := (F.value_eq_of_mutual (relabelTensor_directSum e.symm T U)).trans
    (F.value_directSum _ _)
  value_tensorProduct T U := (F.value_eq_of_mutual (relabelTensor_tensorProduct e.symm T U)).trans
    (F.value_tensorProduct _ _)

/-- Wire distances follow the party labels under a bijection. -/
theorem wireDistance_relabel (F : SpectralPoint k J) (e : R ≃ J) (a b : R) :
    (F.relabel e).wireDistance a b = F.wireDistance (e a) (e b) := by
  have h := relabelTensor_wire (k := k) e.symm (e a) (e b) (Fin 2)
  simp only [Equiv.symm_apply_apply] at h
  exact congrArg (fun v : NNReal ↦ Real.log v / Real.log 2) (F.value_eq_of_mutual h)

end SpectralPoint
end WireTensor

end VPVNP
end Computability
end OAI
