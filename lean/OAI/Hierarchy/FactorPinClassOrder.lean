import OAI.Hierarchy.FactorOccurrences
import Mathlib.Data.List.Sort

namespace OAI
/-! # The order used by the native class-major prefix scan -/

namespace Hierarchy.FactorAllocation

private theorem atTick_sublist {α : Type} {T : ℕ} (xs : List α) (t : Fin T) :
    List.Sublist (atTick xs t) xs := by
  let part (i : Fin xs.length) := if i.val ≡ t.val [MOD T] then [xs[i]] else []
  have sub (l : List (Fin xs.length)) : List.Sublist (l.flatMap part) (l.map (fun i => xs[i])) := by
    induction l with
    | nil => simp
    | cons i l ih =>
      by_cases yes : i.val ≡ t.val [MOD T]
      · simpa [part,yes] using ih.cons_cons xs[i]
      · simpa [part,yes] using ih.cons xs[i]
  simpa [atTick,List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def,part] using
    sub (List.finRange xs.length)

variable {N T d : ℕ} (ht : 0<T) (w : ℕ) (cost : Fin N→Fin d→ℕ)

def keyItems (g : Fin ((20*(w+1)+2)^d)) :=
  group (key w cost) (List.finRange N) (finFunctionFinEquiv.symm g)

/-- Visit classes in increasing encoded order and factors in their original
physical order. Filter by tick only when writing its running prefix. -/
def classStream := (List.finRange ((20*(w+1)+2)^d)).flatMap (keyItems w cost)

private theorem group_sorted (g : Fin ((20*(w+1)+2)^d)) :
    (keyItems w cost g).Pairwise (· < ·) := (List.pairwise_lt_finRange N).filter _

private theorem groupKey {g : Fin ((20*(w+1)+2)^d)} {i : Fin N} :
    i ∈ keyItems w cost g ↔ finFunctionFinEquiv (key w cost i)=g := by
  change i ∈ (List.finRange N).filter _ ↔ _
  simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
  exact ⟨fun eqn => (congrArg finFunctionFinEquiv eqn).trans (Equiv.apply_symm_apply _ _),
    fun eqn => (Equiv.symm_apply_apply _ _).symm.trans (congrArg finFunctionFinEquiv.symm eqn)⟩

private theorem mem_by_group {i : Fin N} {t : Fin T} :
    i ∈ factors w cost (List.finRange N) t ↔ ∃ g, i ∈ atTick (keyItems w cost g) t := by
  simp [factors,keyItems,List.mem_flatten]

private theorem select_group (g : Fin ((20*(w+1)+2)^d)) (t : Fin T) :
    (keyItems w cost g).filter (fun i=>decide (owner ht w cost i=t)) =
      atTick (keyItems w cost g) t := by
  have sub := atTick_sublist (keyItems w cost g) t
  apply List.Subset.antisymm_of_pairwise ((group_sorted w cost g).filter _)
    ((group_sorted w cost g).sublist sub)
  · intro i hi
    obtain ⟨inside,atTick'⟩ := List.mem_filter.mp hi
    have atOwner : owner ht w cost i=t := of_decide_eq_true atTick'
    obtain ⟨g',hg'⟩ := (mem_by_group w cost).mp ((mem_factors_iff_owner ht w cost i t).mpr atOwner.symm)
    have inside' := (atTick_sublist (keyItems w cost g') t).subset hg'
    have same : g'=g := ((groupKey w cost).mp inside').symm.trans ((groupKey w cost).mp inside)
    exact same ▸ hg'
  · intro i hi
    refine List.mem_filter.mpr ⟨sub.subset hi,decide_eq_true ?_⟩
    exact ((mem_factors_iff_owner ht w cost i t).mp ((mem_by_group w cost).mpr ⟨g,hi⟩)).symm

theorem classStream_at (t : Fin T) : (classStream w cost).filter (fun i=>decide (owner ht w cost i=t)) =
    factors w cost (List.finRange N) t := by
  unfold classStream
  rw [List.filter_flatMap]
  simp_rw [select_group ht w cost]
  simp only [List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def,factors,keyItems]

end Hierarchy.FactorAllocation

end OAI
