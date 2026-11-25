import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Choose
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

namespace OAI
/-! # Tensor rank after grouping the factors of a formula parse by its slot partition -/

namespace Hierarchy.FormulaPartitionRank

open scoped BigOperators Classical
noncomputable section

variable {V I F : Type*} {τ : V → Type*} {B R : ℕ}

abbrev Partition (V : Type*) (B : ℕ) := {π : V → Fin B // Function.Surjective π}

abbrev Fiber (τ : V → Type*) (π : Partition V B) (j : Fin B) :=
  (v : {v // π.val v = j}) → τ v.val

def restrict (π : Partition V B) (j : Fin B) (a : (v : V) → τ v) : Fiber τ π j :=
  fun v => a v.val

def Depends (π : Partition V B) (j : Fin B) (f : ((v : V) → τ v) → F) : Prop :=
  ∀ a b, (∀ v, π.val v = j → a v = b v) → f a = f b

/-- A factor which depends only on its block descends to assignments on that block. -/
theorem factor_of_depends [Zero F] {π : Partition V B} {j : Fin B}
    {f : ((v : V) → τ v) → F} (h : Depends π j f) :
    ∃ g : Fiber τ π j → F, ∀ a, f a = g (restrict π j a) := by
  have through : Function.FactorsThrough f (restrict π j) := by
    intro a b eqn
    exact h a b (fun v hv => congrFun eqn ⟨v,hv⟩)
  exact ⟨Function.extend (restrict π j) f (fun _ => 0),fun a => (through.extend_apply _ a).symm⟩

/-- Products indexed by the actual terms can be embedded in a common rank index.
Unused indices contribute zero, including when there are no terms. -/
theorem fixed_partition [Fintype I] [CommSemiring F] [NeZero B]
    (π : Partition V B) (f : I → Fin B → ((v : V) → τ v) → F)
    (locality : ∀ i j, Depends π j (f i j)) (bound : Fintype.card I ≤ R) :
    ∃ g : Fin R → (j : Fin B) → Fiber τ π j → F, ∀ a,
      (∑ i, ∏ j, f i j a) = ∑ r, ∏ j, g r j (restrict π j a) := by
  classical
  choose factors hf using fun i j => factor_of_depends (locality i j)
  let idx : I ↪ Fin R := (Fintype.equivFin I).toEmbedding.trans (Fin.castLEEmb bound)
  let zeroRow : Fin R → (j : Fin B) → Fiber τ π j → F := fun _ _ _ => 0
  let g := Function.extend idx factors zeroRow
  refine ⟨g,fun a => ?_⟩
  let term (r : Fin R) := ∏ j, g r j (restrict π j a)
  calc
    (∑ i, ∏ j, f i j a) = ∑ i, term (idx i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [term,g,idx.injective.extend_apply]
      exact Finset.prod_congr rfl (fun j _ => hf i j a)
    _ = ∑ r ∈ Finset.univ.map idx, term r := (Finset.sum_map _ idx term).symm
    _ = ∑ r, term r := by
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro r _ miss
      have absent : ¬∃ i, idx i=r := by
        rintro ⟨i,rfl⟩
        exact miss (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      have drop : g r=zeroRow r := Function.extend_apply' _ _ _ absent
      simp [term,drop,zeroRow,NeZero.ne B]

/-- Group the parse terms by their surjective slot partitions. The rank-indexed product
decomposition at every partition holds simultaneously for every coefficient assignment. -/
theorem partition_factors [Fintype I] [Fintype V] [CommSemiring F] [NeZero B]
    (part : I → Partition V B)
    (f : I → Fin B → ((v : V) → τ v) → F)
    (locality : ∀ i j, Depends (part i) j (f i j))
    (bound : ∀ π, Fintype.card {i // part i=π} ≤ R) :
    ∃ g : (π : Partition V B) → Fin R → (j : Fin B) → Fiber τ π j → F,
      (∀ π a, (∑ i : {i // part i=π}, ∏ j, f i.val j a) =
        ∑ r, ∏ j, g π r j (restrict π j a)) ∧
      (∀ a, (∑ i, ∏ j, f i j a) =
        ∑ π ∈ Finset.univ.image part, ∑ r, ∏ j, g π r j (restrict π j a)) ∧
      (∀ a, (∑ i, ∏ j, f i j a) = ∑ π, ∑ r, ∏ j, g π r j (restrict π j a)) := by
  classical
  have local' (π : Partition V B) (i : {i // part i=π}) (j : Fin B) : Depends π j (f i.val j) := by
    obtain ⟨i,rfl⟩ := i
    exact locality i j
  choose g hg using fun π => fixed_partition π (fun (i : {i // part i=π}) => f i.val)
    (local' π) (bound π)
  have full (a : (v : V) → τ v) :
      (∑ i, ∏ j, f i j a) = ∑ π, ∑ r, ∏ j, g π r j (restrict π j a) := by
    rw [← Fintype.sum_fiberwise part (fun i => ∏ j, f i j a)]
    exact Finset.sum_congr rfl (fun π _ => hg π a)
  refine ⟨g,hg,fun a => ?_,full⟩
  rw [full]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro π _ miss
  rw [← hg]
  have zero : IsEmpty {i // part i=π} := ⟨fun i =>
    miss (Finset.mem_image.mpr ⟨i.val,Finset.mem_univ _,i.property⟩)⟩
  exact Finset.sum_eq_zero (fun i _ => (zero.false i).elim)


end
end Hierarchy.FormulaPartitionRank

end OAI
