import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Ordered pairs of subspaces

The dimensions of the two subspaces and their sum determine the orbit of an ordered pair
under the general linear group. This identifies the orbits used for Grassmannian walks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Module IsModularLattice

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Addition in a direct sum of two disjoint subspaces. -/
private noncomputable def sumEquiv {A B S : Submodule K V} (h : Disjoint A B)
    (hs : A ⊔ B = S) : (A × B) ≃ₗ[K] S :=
  let f := A.subtype.coprod B.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range, Submodule.ker_subtype,
      Submodule.ker_subtype, Submodule.prod_bot]
    simpa using h
  (LinearEquiv.ofInjective f hf).trans
    (LinearEquiv.ofEq _ _ ((Submodule.sup_eq_range _ _).symm.trans hs))

private theorem sumEquiv_coe {A B S : Submodule K V} (h : Disjoint A B) (hs : A ⊔ B = S)
    (x : A × B) : (sumEquiv h hs x : V) = x.1 + x.2 := rfl

/-- Glue two changes of coordinates on disjoint summands. -/
private theorem glue {A B S A' B' S' : Submodule K V}
    (hd : Disjoint A B) (hs : A ⊔ B = S) (hd' : Disjoint A' B') (hs' : A' ⊔ B' = S')
    (f : A ≃ₗ[K] A') (g : B ≃ₗ[K] B') :
    ∃ e : S ≃ₗ[K] S',
      (∀ (x : A) (y : S), (y : V) = x → (e y : V) = f x) ∧
      (∀ (x : B) (y : S), (y : V) = x → (e y : V) = g x) := by
  let t := sumEquiv hd hs
  let t' := sumEquiv hd' hs'
  let e := t.symm ≪≫ₗ f.prodCongr g ≪≫ₗ t'
  have he (x : A × B) : (e (t x) : V) = (f x.1 : V) + (g x.2 : V) := by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨e, ?_, ?_⟩
  · intro x y hy
    have : y = t (x, 0) := Subtype.ext (by simpa [t, sumEquiv_coe] using hy)
    rw [this, he]
    simp
  · intro x y hy
    have : y = t (0, x) := Subtype.ext (by simpa [t, sumEquiv_coe] using hy)
    rw [this, he]
    simp

private theorem complement_finrank {A B S : Submodule K V} [FiniteDimensional K V]
    (h : Disjoint A B) (hs : A ⊔ B = S) : finrank K S = finrank K A + finrank K B := by
  have hab := A.finrank_sup_add_finrank_inf_eq B
  rw [hs, h.eq_bot, finrank_bot, Nat.add_zero] at hab
  exact hab

private theorem disjoint_from_first {A B C : Submodule K V}
    (h : Disjoint (A ⊓ B) C) (hc : (A ⊓ B) ⊔ C = B) : Disjoint A C := by
  have hCB : C ≤ B := hc ▸ le_sup_right
  rw [disjoint_iff] at h ⊢
  calc
    A ⊓ C = (A ⊓ B) ⊓ C := by rw [inf_assoc, inf_eq_right.mpr hCB]
    _ = ⊥ := h

private theorem map_eq_of_agrees {A A' : Submodule K V} (e : V ≃ₗ[K] V)
    (f : A ≃ₗ[K] A') (h : ∀ x : A, e (x : V) = (f x : V)) : A.map e.toLinearMap = A' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact h ⟨x, hx⟩ ▸ (f ⟨x, hx⟩).property
  · intro hy
    obtain ⟨x, hx⟩ := f.surjective ⟨y, hy⟩
    exact ⟨x, x.property, (h x).trans (congrArg Subtype.val hx)⟩

/-- Two ordered pairs of subspaces are conjugate if the corresponding first subspaces,
second subspaces, and sums have equal dimensions. -/
theorem exists_pair_linearEquiv [FiniteDimensional K V] (A B A' B' : Submodule K V)
    (hA : finrank K A = finrank K A') (hB : finrank K B = finrank K B')
    (hS : finrank K (A ⊔ B : Submodule K V) = finrank K (A' ⊔ B' : Submodule K V)) :
    ∃ e : V ≃ₗ[K] V, A.map e.toLinearMap = A' ∧ B.map e.toLinearMap = B' := by
  let I := A ⊓ B
  let I' := A' ⊓ B'
  have hI : finrank K I = finrank K I' := by
    have h := A.finrank_sup_add_finrank_inf_eq B
    have h' := A'.finrank_sup_add_finrank_inf_eq B'
    dsimp [I, I']
    omega
  obtain ⟨D, hd, hs⟩ := exists_disjoint_and_sup_eq (show I ≤ A from inf_le_left)
  obtain ⟨D', hd', hs'⟩ := exists_disjoint_and_sup_eq (show I' ≤ A' from inf_le_left)
  obtain ⟨C, hc, ht⟩ := exists_disjoint_and_sup_eq (show I ≤ B from inf_le_right)
  obtain ⟨C', hc', ht'⟩ := exists_disjoint_and_sup_eq (show I' ≤ B' from inf_le_right)
  have hD : finrank K D = finrank K D' := by
    have := complement_finrank hd hs
    have := complement_finrank hd' hs'
    omega
  have hC : finrank K C = finrank K C' := by
    have := complement_finrank hc ht
    have := complement_finrank hc' ht'
    omega
  let fi := LinearEquiv.ofFinrankEq I I' hI
  let fc := LinearEquiv.ofFinrankEq C C' hC
  obtain ⟨fa, ha, _⟩ := glue hd hs hd' hs' fi (LinearEquiv.ofFinrankEq D D' hD)
  have hAC : A ⊔ C = A ⊔ B := by
    calc A ⊔ C = (A ⊔ I) ⊔ C := by rw [sup_eq_left.mpr (show I ≤ A from inf_le_left)]
         _ = A ⊔ B := by rw [sup_assoc, ht]
  have hAC' : A' ⊔ C' = A' ⊔ B' := by
    calc A' ⊔ C' = (A' ⊔ I') ⊔ C' := by rw [sup_eq_left.mpr (show I' ≤ A' from inf_le_left)]
         _ = A' ⊔ B' := by rw [sup_assoc, ht']
  obtain ⟨fs, hsa, hsc⟩ := glue (disjoint_from_first hc ht) hAC (disjoint_from_first hc' ht')
    hAC' fa fc
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq fs
  have hea (x : A) : e (x : V) = (fa x : V) := by
    let y : (A ⊔ B : Submodule K V) := ⟨x, (show A ≤ A ⊔ B from le_sup_left) x.property⟩
    exact (he y).symm.trans (hsa x y rfl)
  have hec (x : C) : e (x : V) = (fc x : V) := by
    let y : (A ⊔ B : Submodule K V) := ⟨x, (show C ≤ A ⊔ B from hAC ▸ le_sup_right) x.property⟩
    exact (he y).symm.trans (hsc x y rfl)
  have hei (x : I) : e (x : V) = (fi x : V) := by
    let y : A := ⟨x, x.property.1⟩
    exact (hea y).trans (ha x y rfl)
  refine ⟨e, map_eq_of_agrees e fa hea, ?_⟩
  rw [← ht, Submodule.map_sup, map_eq_of_agrees e fi hei, map_eq_of_agrees e fc hec, ht']

end Grassmann

end VPVNP
end Computability
end OAI
