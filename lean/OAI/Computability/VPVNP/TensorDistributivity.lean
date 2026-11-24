import OAI.Computability.VPVNP.WireTensor
import Mathlib.Logic.Equiv.Sum

/-!
# Direct sums and products up to local restriction

Relabeling local bases lets us permute and regroup direct summands, and distribute
a tensor product over a direct sum. Pure coordinate blocks carry the entries of
their summands and mixed blocks vanish.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v

namespace WireTensor

variable {k : Type u} {J : Type v}

/-- An assignment to disjoint local bases lies in one block at every party, or uses both. -/
theorem sum_assignment_cases {A : J → Type*} {B : J → Type*} (x : ∀ j, A j ⊕ B j) :
    (∃ a : ∀ j, A j, x = fun j ↦ Sum.inl (a j)) ∨
      (∃ b : ∀ j, B j, x = fun j ↦ Sum.inr (b j)) ∨
      (∃ (i j : J) (a : A i) (b : B j), x i = Sum.inl a ∧ x j = Sum.inr b) := by
  classical
  by_cases hl : ∀ j, ∃ a, x j = Sum.inl a
  · choose a ha using hl
    exact Or.inl ⟨a, funext ha⟩
  by_cases hr : ∀ j, ∃ b, x j = Sum.inr b
  · choose b hb using hr
    exact Or.inr (Or.inl ⟨b, funext hb⟩)
  push Not at hl hr
  obtain ⟨i, hi⟩ := hr
  obtain ⟨j, hj⟩ := hl
  cases hai : x i with
  | inr b => exact (hi b hai).elim
  | inl a =>
    cases hbj : x j with
    | inl b => exact (hj b hbj).elim
    | inr b => exact Or.inr (Or.inr ⟨i, j, a, b, hai, hbj⟩)

/-- Regrouping the three coordinate blocks at every party preserves the tensor. -/
theorem directSum_assoc_mutual [Fintype J] [CommSemiring k] (T U V : Tensor k J) :
    Restricts (directSum (directSum T U) V) (directSum T (directSum U V)) ∧
      Restricts (directSum T (directSum U V)) (directSum (directSum T U) V) := by
  classical
  let e (j : J) := Equiv.sumAssoc (T.Basis j) (U.Basis j) (V.Basis j)
  let M (j : J) (c b : T.Basis j ⊕ (U.Basis j ⊕ V.Basis j)) : k := if c = b then 1 else 0
  let L (j : J) (c : T.Basis j ⊕ (U.Basis j ⊕ V.Basis j))
      (b : (T.Basis j ⊕ U.Basis j) ⊕ V.Basis j) := M j c (e j b)
  have h :
      applyLocal L (directSum (directSum T U) V).coeff =
      applyLocal M (directSum T (directSum U V)).coeff := by
    erw [applyLocal_directSum (directSum T U) V L, applyLocal_directSum T (directSum U V) M,
      applyLocal_directSum T U, applyLocal_directSum U V, add_assoc]
    rfl
  have hL : L = fun j c b ↦ if (e j).symm c = b then 1 else 0 := by
    funext j c b
    simp [L, M, Equiv.symm_apply_eq]
  dsimp only [M] at h
  erw [hL, applyLocal_pullback (fun j c ↦ (e j).symm c), applyLocal_id] at h
  apply restricts_of_reindex (fun j ↦ (e j).symm)
  exact fun c ↦ (congrFun h c).symm

variable [CommSemiring k] [Fintype J] [Nonempty J]

/-- Swapping the left and right local blocks interchanges the summands. -/
theorem directSum_comm_mutual (T U : Tensor.{u,v,0} k J) :
    Restricts (directSum T U) (directSum U T) ∧ Restricts (directSum U T) (directSum T U) := by
  apply restricts_of_reindex (fun j ↦ Equiv.sumComm (U.Basis j) (T.Basis j))
  intro x
  rcases sum_assignment_cases x with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨i, j, a, b, hi, hj⟩
  · exact (directSum_coeff_inl U T a).trans (directSum_coeff_inr T U a).symm
  · exact (directSum_coeff_inr U T b).trans (directSum_coeff_inl T U b).symm
  · rw [directSum_coeff_mixed U T x hi hj]
    symm
    apply directSum_coeff_mixed T U _ (a := j) (b := i) (i := b) (l := a)
    · rw [hj]
      rfl
    · rw [hi]
      rfl

/-- Local distribution of product coordinates over a disjoint union gives
mutual restrictions for the distributive law. -/
theorem tensorProduct_directSum_mutual (T U V : Tensor.{u,v,0} k J) :
    Restricts (tensorProduct T (directSum U V))
      (directSum (tensorProduct T U) (tensorProduct T V)) ∧
    Restricts (directSum (tensorProduct T U) (tensorProduct T V))
      (tensorProduct T (directSum U V)) := by
  let e (j : J) := (Equiv.prodSumDistrib (T.Basis j) (U.Basis j) (V.Basis j)).symm
  apply restricts_of_reindex e
  intro x
  rcases sum_assignment_cases x with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨i, j, a, b, hi, hj⟩
  · rw [directSum_coeff_inl]
    change _ = T.coeff (fun j ↦ (a j).1) * (directSum U V).coeff (fun j ↦ Sum.inl (a j).2)
    rw [directSum_coeff_inl]
    rfl
  · rw [directSum_coeff_inr]
    change _ = T.coeff (fun j ↦ (b j).1) * (directSum U V).coeff (fun j ↦ Sum.inr (b j).2)
    rw [directSum_coeff_inr]
    rfl
  · rw [directSum_coeff_mixed _ _ x hi hj]
    change 0 = T.coeff _ * (directSum U V).coeff (fun l ↦ (e l (x l)).2)
    have hl : (e i (x i)).2 = Sum.inl a.2 := by rw [hi]; rfl
    have hr : (e j (x j)).2 = Sum.inr b.2 := by rw [hj]; rfl
    rw [directSum_coeff_mixed U V _ hl hr, mul_zero]

end WireTensor

end VPVNP
end Computability
end OAI
