import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentOpenShape
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentOpenContraction
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortPatchSubstitution
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPruneCost

/-! # The open tensor network of a trivalent tree

Slots zero, one, and two read the output, left input, and right input of the
original coefficient tensor. Interior edges share a padded alphabet. Each
external stub may have its own alphabet and supplies its index via `read`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace PlanarPatch.TrivalentTree

open PortGraph

variable {V K : Type*} {d : V → ℕ} {q : ℕ} (t : TrivalentTree K d q)
variable (h : [] ∈ t.branchAddresses) (D : ℕ) {A : t.Stub → Type}
variable (read : (s : t.Stub) → A s → ℕ)

/-- Natural indices on the three ordered slots of one actual table. -/
def localCoordinate (v : t.Role) (a : t.internalGraph.Port v → Fin D)
    (s : (e : {s : t.Stub // t.attach h s = v}) → A e.val) (i : Fin 3) : ℕ :=
  Sum.elim (fun p => (a p).val) (fun p => read p.val (s p)) ((t.openSlotEquiv h v).symm i)

/-- The original tensor zero-extended to arbitrary slot indices. -/
def slotTensor [CommSemiring K] (v : t.Role) (z : Fin 3 → ℕ) : K :=
  (t.branchAt v).paddedCoeff (z 0) (z 1) (z 2)

/-- A genuine open network with the incidence graph and local order of the tree. -/
def openNetwork [CommSemiring K] : OpenNetwork t.Stub A K where
  Vertex := t.Role
  Wire := t.InternalWire
  graph := t.internalGraph
  Index _ := Fin D
  attach := t.attach h
  table v a s := t.slotTensor v (t.localCoordinate h D read v a s)

private def globalRead (y : t.InternalWire → Fin D) (z : (s : t.Stub) → A s) : t.TreeEnd → ℕ
  | .inl (w,_) => (y w).val
  | .inr s => read s (z s)

private theorem localCoordinate_end (v : t.Role) (e : t.TreeEnd) (he : t.endOwner h e = v)
    (y : t.InternalWire → Fin D) (z : (s : t.Stub) → A s) :
    t.localCoordinate h D read v (t.internalGraph.atVertex y v) (fun p => z p.val)
      (slotOfPosition (t.endPosition h e)) = t.globalRead D read y z e := by
  let p := (t.openDartEquiv h v).symm ⟨e,he⟩
  have hp : t.openSlotEquiv h v p = slotOfPosition (t.endPosition h e) := by
    rw [openSlotEquiv_apply, Equiv.apply_symm_apply]
  rw [← hp, localCoordinate, Equiv.symm_apply_apply]
  cases e with
  | inl => rfl
  | inr => rfl

private theorem localCoordinate_eq_fixedRead (v : t.Role) (x : ∀ v, Fin (d v)) (c : Fin q)
    (y : t.InternalWire → Fin D) (z : (s : t.Stub) → A s)
    (hout : read none (z none) = c.val)
    (hleaf : ∀ p : t.Leaf, read (some p) (z (some p)) = t.leafRead x p.val)
    (pos : Option Bool) :
    t.localCoordinate h D read v (t.internalGraph.atVertex y v) (fun p => z p.val)
      (slotOfPosition pos) =
      t.fixedRead x c y (match pos with | none => v.val | some b => v.val ++ [b]) := by
  cases pos with
  | none =>
    have he := t.localCoordinate_end h D read v (t.openOutputEnd v) (t.owner_openOutputEnd h v) y z
    rw [position_openOutputEnd] at he
    rw [he]
    by_cases hv : v.val = []
    · simp [openOutputEnd, fixedRead, hv, globalRead, hout]
    · simp [openOutputEnd, fixedRead, hv, globalRead, v.property]
  | some b =>
    have he := t.localCoordinate_end h D read v (t.openChildEnd v b) (t.owner_openChildEnd h v b) y z
    rw [position_openChildEnd] at he
    rw [he]
    by_cases hv : v.val ++ [b] ∈ t.branchAddresses
    · simp [openChildEnd, fixedRead, hv, globalRead]
    · simp [openChildEnd, fixedRead, hv, globalRead, hleaf]

/-- Direct expansion of the open network as a sum of products over shared wires. -/
theorem openNetwork_expansion [CommSemiring K] (x : ∀ v, Fin (d v)) (c : Fin q)
    (z : (s : t.Stub) → A s) (hout : read none (z none) = c.val)
    (hleaf : ∀ p : t.Leaf, read (some p) (z (some p)) = t.leafRead x p.val) :
    (t.openNetwork h D read).eval z = ∑ y : t.InternalWire → Fin D, ∏ v : t.Role,
      (t.branchAt v).paddedCoeff (t.fixedRead x c y v.val)
        (t.fixedRead x c y (v.val ++ [false])) (t.fixedRead x c y (v.val ++ [true])) := by
  unfold OpenNetwork.eval
  refine Finset.sum_congr ?_ ?_
  · exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

  intro y _
  apply Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
  intro v _
  simp only [openNetwork, slotTensor]
  congr 1
  · exact t.localCoordinate_eq_fixedRead h D read v x c y z hout hleaf none
  · exact t.localCoordinate_eq_fixedRead h D read v x c y z hout hleaf (some false)
  · exact t.localCoordinate_eq_fixedRead h D read v x c y z hout hleaf (some true)

/-- Contracting the actual graph with its root and leaf stubs fixed computes the tree. -/
theorem eval_openNetwork [CommSemiring K] (hb : t.Bounded D) (x : ∀ v, Fin (d v)) (c : Fin q)
    (z : (s : t.Stub) → A s) (hout : read none (z none) = c.val)
    (hleaf : ∀ p : t.Leaf, read (some p) (z (some p)) = t.leafRead x p.val) :
    (t.openNetwork h D read).eval z = t.eval x c :=
  (t.openNetwork_expansion h D read x c z hout hleaf).trans (t.eval_eq_sum_internal hb h x c).symm

section Formula

variable {F I : Type*} [Field F]

/-- Every in-range coefficient at an internal address is an actual tree entry. -/
theorem exists_entry_at (u : TrivalentTree K d q) (v : u.Role)
    (a : Fin (u.branchAt v).q) (b : Fin (u.branchAt v).i) (c : Fin (u.branchAt v).j) :
    ∃ e : u.Entry, u.entry e = (u.branchAt v).coeff a b c := by
  induction u with
  | port => exact False.elim (Finset.notMem_empty _ v.property)
  | branch B l r hl hr =>
    obtain ⟨_ | (v | v), rfl⟩ := (branchRoleEquiv B l r).symm.surjective v
    · exact ⟨.inl (a,b,c), rfl⟩
    · obtain ⟨e,he⟩ := hl v a b c
      exact ⟨.inr (.inl e), he⟩
    · obtain ⟨e,he⟩ := hr v a b c
      exact ⟨.inr (.inr e), he⟩

/-- Every padded table entry is zero or an original tree entry. -/
theorem slotTensor_eq_zero_or_entry [CommSemiring K] (v : t.Role) (z : Fin 3 → ℕ) :
    t.slotTensor v z = 0 ∨ ∃ e : t.Entry, t.slotTensor v z = t.entry e := by
  unfold slotTensor BranchData.paddedCoeff
  split_ifs with ha hb hc
  · obtain ⟨e,he⟩ := t.exists_entry_at v ⟨_,ha⟩ ⟨_,hb⟩ ⟨_,hc⟩
    exact .inr ⟨e, he.symm⟩
  all_goals exact .inl rfl

/-- Padding at the three ports preserves the common formula bound. -/
theorem hasFormula_slotTensor (u : TrivalentTree (MvPolynomial I F) d q) {W : ℕ}
    (hW : 1 ≤ W) (hf : u.FormulaBound W) (v : u.Role) (z : Fin 3 → ℕ) :
    HasFormula W (u.slotTensor v z) := by
  obtain hz | ⟨e,he⟩ := u.slotTensor_eq_zero_or_entry v z
  · rw [hz]
    simpa using (HasFormula.const (I := I) (0 : F)).mono hW
  · exact he ▸ hf e

end Formula

end PlanarPatch.TrivalentTree

end

end SpectralBooks
end LinearAlgebra
end OAI
