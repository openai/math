import OAI.Computability.BorderVNP.PackedSewnFragmentSortPartition

/-! # From unique physical coverage to the ordered sewing partition

An address in the predecessor interval belongs to one raw row occurrence. This
criterion handles repeated records, interleaved owners, and empty reservations. The
sparse sort turns it into a gap-free partition in the order consumed by the scan.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open private positive_projection projected_order from OAI.Computability.BorderVNP.PackedSewnFragmentSortPartition

variable {n w old k : ℕ}

private def hit (j : ℕ) (p : Interval) : Bool := decide (p.oldStart ≤ j ∧ j < p.oldStart+p.width)

private theorem count_one {xs : List Interval} {j : ℕ}
    (one : ∃! i : Fin xs.length, (xs.get i).oldStart ≤ j ∧ j < (xs.get i).oldStart+(xs.get i).width) :
    xs.countP (hit j) = 1 := by
  obtain ⟨i,hi,only⟩ := one
  have e : hit j ∘ xs.get = fun a => decide (a = i) := by
    funext a
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,hit,decide_eq_true_eq]
    exact ⟨fun ha => only a ha, fun eq => eq ▸ hi⟩
  calc
    xs.countP (hit j) = ((List.finRange xs.length).map xs.get).countP (hit j) := by rw [List.map_get_finRange]
    _ = ((List.finRange xs.length).filter (fun a => decide (a=i))).length := by
      rw [List.countP_map,e,List.countP_eq_length_filter]
    _ = 1 := by simp [List.filter_eq]

private theorem partition_of_counts (xs : List Interval) (cap : k ≤ old)
    (bounds : ∀ p ∈ xs, k ≤ p.oldStart ∧ p.oldStart+p.width ≤ old)
    (pos : ∀ p ∈ xs, 0 < p.width) (order : xs.Pairwise (fun a b => a.oldStart ≤ b.oldStart))
    (one : ∀ j, k ≤ j → j < old → xs.countP (hit j) = 1) : Partition old k xs := by
  induction xs generalizing k with
  | nil =>
    change k = old
    by_contra! hn
    have h := one k le_rfl (lt_of_le_of_ne cap hn)
    simp at h
  | cons a xs ih =>
    have ⟨alo,ahi⟩ := bounds a List.mem_cons_self
    have aw := pos a List.mem_cons_self
    have hp (p) (mem : p ∈ xs) := pos p (List.mem_cons_of_mem _ mem)
    have hbound (p) (mem : p ∈ xs) := bounds p (List.mem_cons_of_mem _ mem)
    have minKey := (List.pairwise_cons.mp order).1
    have atStart : a.oldStart = k := by
      have hc := one k le_rfl (by omega)
      have nonempty : 0 < (a::xs).countP (hit k) := by omega
      obtain ⟨p,mem,contains⟩ := List.countP_pos_iff.mp nonempty
      have bound := (of_decide_eq_true contains : p.oldStart ≤ k ∧ k < p.oldStart+p.width).1
      rcases List.mem_cons.mp mem with rfl|mem
      · omega
      · exact le_antisymm ((minKey p mem).trans bound) alo
    refine ⟨atStart,ahi,ih ahi ?_ hp (List.pairwise_cons.mp order).2 ?_⟩
    · intro p mem
      refine ⟨?_,(hbound p mem).2⟩
      by_contra! overlaps
      have hmin := minKey p mem
      have pw := hp p mem
      have hc := one p.oldStart (hbound p mem).1 (by have := (hbound p mem).2; omega)
      have aHit : hit p.oldStart a = true := decide_eq_true ⟨hmin,overlaps⟩
      have pHit : hit p.oldStart p = true := decide_eq_true ⟨le_rfl,by omega⟩
      have ht := List.countP_pos_iff.mpr ⟨p,mem,pHit⟩
      rw [List.countP_cons_of_pos aHit] at hc
      omega
    · intro j lo hi
      have hc := one j (by omega) hi
      exact (List.countP_cons_of_neg (p := hit j) (a := a) (l := xs) (by simp [hit,not_lt_of_ge lo])).symm.trans hc

/-- An unordered sparse source covers every old lane exactly once by occurrence.
Zero-width rows have no occurrences and may be enabled before the sort. -/
def UniqueCover (old : ℕ) (xs : List Interval) : Prop :=
  ∀ j : Fin old, ∃! i : Fin xs.length,
    (xs.get i).oldStart ≤ j.val ∧ j.val < (xs.get i).oldStart+(xs.get i).width

/-- The owner's physical rows form a complete consecutive partition after sorting as soon
as the raw rows are in bounds and each old lane has one covering row occurrence. -/
theorem Sorted.sitePartition_of_cover {x y : Pin n w → Bool} (h : Sorted x y) (v old : ℕ)
    (fit : ∀ p ∈ siteRuns v (list x), p.oldStart+p.width ≤ old)
    (one : UniqueCover old (siteRuns v (list x))) : Partition old 0 (siteRuns v (list y)) := by
  let raw := siteRuns v (list x)
  let keep := fun p : Interval => decide (0<p.width)
  have perm : (siteRuns v (list y)).Perm (raw.filter keep) := by
    have m := h.perm.filterMap (fun p => if p.site=v then some p.run else none)
    change (siteRuns v (list y)).Perm (siteRuns v _) at m
    simpa only [positive_projection] using m
  apply partition_of_counts _ (Nat.zero_le _)
    (fun p mem => ⟨Nat.zero_le _,fit p (List.mem_filter.mp (perm.subset mem)).1⟩)
    (fun p mem => of_decide_eq_true (List.mem_filter.mp (perm.subset mem)).2) (projected_order h.ordered v)
  intro j _ hj
  have counts := perm.countP_eq (hit j)
  rw [List.countP_filter] at counts
  have keepHit : (fun p => hit j p && keep p) = hit j := by
    funext p
    by_cases h : p.oldStart ≤ j ∧ j < p.oldStart+p.width
    · have hw : 0 < p.width := by omega
      simp [hit,keep,h,hw]
    · simp [hit,h]
  rw [keepHit] at counts
  exact counts.trans (count_one (one ⟨j,hj⟩))

/-- At an authentically covered owner, coalescing the live sorted fragments computes
the canonical intervals of the full predecessor-to-source map. -/
theorem Sorted.coalesced_siteRuns_of_cover {x y : Pin n w → Bool} (h : Sorted x y) (v : ℕ)
    {next : ℕ} (read : Fin old → Option (Fin next)) (fit : ∀ p ∈ siteRuns v (list x), p.oldStart+p.width ≤ old)
    (one : UniqueCover old (siteRuns v (list x))) (good : ∀ p ∈ siteRuns v (list x), Good read p) :
    siteRuns v (coalesce (list y)) = intervals read := by
  have m := h.perm.filterMap (fun p => if p.site=v then some p.run else none)
  change (siteRuns v (list y)).Perm (siteRuns v _) at m
  rw [positive_projection] at m
  rw [project_coalesce _ _ h.siteOrder]
  exact localRuns_eq read _ (h.sitePartition_of_cover v old fit one)
    (fun p hp => of_decide_eq_true (List.mem_filter.mp (m.subset hp)).2)
    (fun p hp => good p (List.mem_filter.mp (m.subset hp)).1)

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
