import OAI.Computability.BorderVNP.PackedSewnFragmentProjection
import OAI.Computability.BorderVNP.PackedSewnFragmentSort

/-! # Recovering each site's chronological interval partition after the sparse sort

Input slots may be interleaved arbitrarily across or within sites, and may include
zero-width reservations. If their descriptors form the site's genuine partition up to a
permutation, the ordered positive output is exactly that partition with empty rows removed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

variable {n w old next k : ℕ}

private theorem starts_from (runs : List Interval) (tiles : Partition old k runs) :
    ∀ p ∈ runs, k ≤ p.oldStart := by
  induction runs generalizing k with
  | nil => simp
  | cons a rest ih =>
    obtain ⟨atStart,_,tail⟩ := tiles
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact atStart.ge
    · exact atStart.ge.trans ((Nat.le_add_right ..).trans (ih tail _ hp))

private theorem partition_order (runs : List Interval) (tiles : Partition old k runs)
    (positive : ∀ p ∈ runs, 0 < p.width) : runs.Pairwise (fun a b => a.oldStart < b.oldStart) := by
  induction runs generalizing k with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
    have tail := tiles.2.2
    apply List.pairwise_cons.mpr
    refine ⟨fun b hb => ?_, ih tail (fun p hp => positive p (List.mem_cons_of_mem a hp))⟩
    exact (Nat.lt_add_of_pos_right (positive a List.mem_cons_self)).trans_le (starts_from rest tail b hb)

private theorem positive_projection (v : ℕ) (xs : List Parsed) :
    siteRuns v (xs.filter (fun p => decide (0 < p.run.width))) =
      (siteRuns v xs).filter (fun r => decide (0 < r.width)) := by
  unfold siteRuns
  rw [List.filterMap_filter,List.filter_filterMap]
  apply congrArg (fun f => xs.filterMap f)
  funext p
  by_cases hs : p.site = v <;> by_cases hp : 0 < p.run.width <;> simp [hs,hp,Option.filter]

/-- Sorted input fragments are ordered by owner and by predecessor offset within each owner. -/
theorem Sorted.siteOrder {x y : Pin n w → Bool} (h : Sorted x y) :
    (list y).Pairwise (fun a b => a.site ≤ b.site) :=
  h.ordered.imp (by intro a b hab; unfold Parsed.before at hab; omega)

private theorem projected_order {xs : List Parsed} (h : xs.Pairwise Parsed.before) (v : ℕ) :
    (siteRuns v xs).Pairwise (fun a b => a.oldStart ≤ b.oldStart) := by
  apply List.pairwise_filterMap.mpr
  apply h.imp
  intro a b hab r hr s hs
  by_cases ha : a.site = v
  · by_cases hb : b.site = v
    · simp only [ha,hb,ite_true,Option.some.injEq] at hr hs
      subst r; subst s
      unfold Parsed.before at hab
      omega
    · simp [hb] at hs
  · simp [ha] at hr

/-- The site's sorted records reproduce its exact ordered, positive-width partition.
The supplied physical roster can contain empty descriptors anywhere. -/
theorem Sorted.siteRuns_eq {x y : Pin n w → Bool} (h : Sorted x y) (v : ℕ) (roster : List Interval)
    (rows : (siteRuns v (list x)).Perm roster) (tiles : Partition old k roster) :
    siteRuns v (list y) = roster.filter (fun r => decide (0 < r.width)) := by
  let keep := fun r : Interval => decide (0 < r.width)
  let out := roster.filter keep
  have perm : (siteRuns v (list y)).Perm out := by
    have mapped := h.perm.filterMap (fun p => if p.site = v then some p.run else none)
    change (siteRuns v (list y)).Perm (siteRuns v _) at mapped
    rw [positive_projection] at mapped
    exact mapped.trans (rows.filter keep)
  have strict : out.Pairwise (fun a b => a.oldStart < b.oldStart) :=
    partition_order out (Partition.filter_positive roster k tiles)
      (fun r hr => of_decide_eq_true (List.mem_filter.mp hr).2)
  have inject := List.inj_on_of_nodup_map (f := Interval.oldStart)
    (List.pairwise_map.mpr (strict.imp (fun a => a.ne)))
  apply perm.eq_of_pairwise _ (projected_order h.ordered v) (strict.imp (fun a => a.le))
  intro a b ha hb hab hba
  exact inject (perm.subset ha) hb (le_antisymm hab hba)

/-- The coalesced physical sort returns precisely the canonical exterior intervals of
the actual lane map. It suffices to specify each owner's sparse raw roster up to permutation. -/
theorem Sorted.coalesced_siteRuns {x y : Pin n w → Bool} (h : Sorted x y)
    (v : ℕ) (read : Fin old → Option (Fin next)) (roster : List Interval)
    (rows : (siteRuns v (list x)).Perm roster) (tiles : Partition old 0 roster)
    (good : ∀ p ∈ roster, Good read p) : siteRuns v (coalesce (list y)) = intervals read := by
  rw [project_coalesce _ _ h.siteOrder,h.siteRuns_eq v roster rows tiles]
  exact filter_localRuns_eq read roster tiles good

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
