import OAI.Optimization.LinearProgramming.Compression.ServiceGeneratorTable
import Mathlib.Data.List.InsertIdx

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

variable {α : Type*} [LinearOrder α]

/-- The first slot at or above `q` in a strictly sorted table. -/
def rank (q : α) (keys : List α) : ℕ := keys.countP (fun x => decide (x < q))

theorem rank_le_length (q : α) (keys : List α) : rank q keys ≤ keys.length := List.countP_le_length

theorem rank_snoc (q x : α) (xs : List α) : rank q (xs ++ [x]) = rank q xs + (if x<q then 1 else 0) := by
  by_cases h : x<q <;> simp [rank, List.countP_append, h]

private theorem rank_zero (q : α) {xs : List α} (h : ∀ x ∈ xs, q ≤ x) : rank q xs = 0 := by
  simpa [rank] using h

theorem rank_cons_lt {q x : α} (xs : List α) (h : x<q) : rank q (x::xs)=rank q xs+1 := by
  simp [rank,h]

/-- The index returned from the native scan matches sorted insertion, including inserting at
zero and appending after the last row. -/
theorem ranked_insert_order (q : α) {xs : List α} (hs : xs.Pairwise (· < ·)) (hf : q ∉ xs) :
    (xs.insertIdx (rank q xs) q).Pairwise (· < ·) := by
  induction xs with
  | nil => simp [rank]
  | cons x xs ih =>
    obtain ⟨hall,ht⟩ := List.pairwise_cons.mp hs
    have hnx : x≠q := fun he => hf (he ▸ List.mem_cons_self)
    have hq : q∉xs := fun h => hf (List.mem_cons_of_mem _ h)
    by_cases hx : x<q
    · rw [rank_cons_lt xs hx, List.insertIdx_succ_cons, List.pairwise_cons]
      exact ⟨fun z hz => (List.eq_or_mem_of_mem_insertIdx hz).elim (fun he => he ▸ hx) (hall z), ih ht hq⟩
    · have hqx : q<x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hnx)
      have hz := rank_zero q (xs := x::xs) (fun z hz => by
        rcases List.mem_cons.mp hz with rfl | hmem
        · exact hqx.le
        · exact hqx.le.trans (hall z hmem).le)
      rw [hz,List.insertIdx_zero,List.pairwise_cons]
      exact ⟨fun z hz => (List.mem_cons.mp hz).elim (fun he => he ▸ hqx) (fun hm => hqx.trans (hall z hm)),hs⟩

theorem membership_rank {q : α} {xs : List α} (hs : xs.Pairwise (· < ·)) (hq : q ∈ xs) :
    ∃ h : rank q xs < xs.length, xs[rank q xs] = q := by
  induction xs with
  | nil => simp at hq
  | cons x xs ih =>
    obtain ⟨hall,ht⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp hq with rfl | hq'
    · have hz := rank_zero q (xs := q::xs) (fun z hz =>
        (List.mem_cons.mp hz).elim (fun he => he ▸ le_rfl) (fun hm => (hall z hm).le))
      simp [hz]
    · have hx := hall q hq'
      obtain ⟨hr,he⟩ := ih ht hq'
      rw [rank_cons_lt xs hx]
      exact ⟨by simpa using Nat.succ_lt_succ hr, by simpa using he⟩

/-- The stored list and the canonical order on the mathematical generator set identify
the same coordinate, which is needed when reading commitment coefficients by position. -/
theorem get_sorted_eq_orderIso (J : Finset α) (i : Fin J.card) :
    J.sort[i.val]'(by simp) = ((J.orderIsoOfFin rfl i : J) : α) := by
  rw [Finset.coe_orderIsoOfFin_apply,Finset.orderEmbOfFin_apply,Fin.getElem_fin]

theorem toFinset_ranked_insert {q : α} {xs : List α} :
    (xs.insertIdx (rank q xs) q).toFinset = insert q xs.toFinset := by
  ext a
  simp [List.mem_insertIdx (rank_le_length q xs)]

/-- Thus native insertion produces the same ordered generator vector used in the proof. -/
theorem finset_sort_insert (J : Finset α) (q : α) (hq : q ∉ J) :
    (insert q J).sort = J.sort.insertIdx (rank q J.sort) q := by
  let ys := J.sort.insertIdx (rank q J.sort) q
  have hs : ys.Pairwise (· < ·) := ranked_insert_order q J.sortedLT_sort.pairwise (by simpa using hq)
  have hy : ys.toFinset=insert q J := by rw [toFinset_ranked_insert,Finset.sort_toFinset]
  rw [← hy]
  exact (List.toFinset_sort (· ≤ ·) hs.sortedLT.nodup).mpr (hs.imp fun h => le_of_lt h)

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
