import OAI.Computability.BorderVNP.FiniteCellPower

/-! # Exact cell factors from the sparse directory

A finite-field table entry is named by its position in a fixed field table.
The cell validates every proposed multiplicity, including that of a zero scalar.
The independently checked count bits then give the product of precisely the
selected entries, without expanding a shared table description in the advice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldPowers

open CellSparse
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]

/-- Look up a finite scalar position. Unallocated positions have value zero. -/
def entry {k : ℕ} (v : Fin k → F) (i : ℕ) : F :=
  if hi : i < k then v ⟨i,hi⟩ else 0

omit [Fintype F] in
private theorem prod_counted {k : ℕ} (v : Fin k → F) (ids : List ℕ) (h : ∀ j ∈ ids, j < k) :
    (ids.map (entry v)).prod = ∏ i, v i ^ ids.count i.val := by
  induction ids with
  | nil => simp
  | cons j ids ih =>
    have hj : j < k := h j (by simp)
    let p : Fin k := ⟨j,hj⟩
    have hi := ih (fun z hz => h z (by simp [hz]))
    have factors (i : Fin k) : v i ^ (j::ids).count i.val =
        (if i = p then v i else 1) * v i ^ ids.count i.val := by
      by_cases he : i = p
      · subst i; simp [p, pow_succ, mul_comm]
      · have hn : j ≠ i.val := fun hh => he (Fin.ext hh.symm)
        simp [hn, he]
    simp only [List.map_cons, List.prod_cons, hi, factors, Finset.prod_mul_distrib,
      Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    simp [p, entry, hj]

/-- The sparse checker validates every exponent used by the actual finite-state
power scanner. The result equals the direct product of all observed table positions. -/
theorem checked_count_product (D : Directory) (bank : ℕ → Bool)
    (v : Fin D.reportedCounts.length → F) (obs : List (Bool × Option ℕ))
    (h : countsValid bank D.reportedCounts obs) :
    let counts := fun i : Fin D.reportedCounts.length => D.reportedCounts[i].map bank
    FieldStack.productPaths (program v) factor (fun _ => 1)
      (1 + ∑ i, (2*(counts i).length+2)) (.visit (Fin.last _)) counts =
      ((obs.filterMap Prod.snd).map (entry v)).prod := by
  intro counts
  rw [evaluate, prod_counted v _ h.1]
  apply Finset.prod_congr rfl
  intro i _
  rw [show digits (counts i) = (obs.filterMap Prod.snd).count i.val from
    (digits_map bank D.reportedCounts[i]).trans (h.2 i).symm]

/-- The cell's signed flags times the scanner output reproduce the full field product.
A missing row or invalid declaration contributes zero. -/
theorem cell_weight (D : Directory) (bank : ℕ → Bool) (v : Fin D.reportedCounts.length → F) :
    let counts := fun i : Fin D.reportedCounts.length => D.reportedCounts[i].map bank
    (D.weight bank : F) * FieldStack.productPaths (program v) factor (fun _ => 1)
      (1 + ∑ i, (2*(counts i).length+2)) (.visit (Fin.last _)) counts =
    (D.observations bank).elim 0 (fun obs =>
      if (∀ r ∈ D.records, r.Valid D.boxes bank) ∧ countsValid bank D.reportedCounts obs then
        (if (obs.map Prod.fst).foldl Bool.xor false then -1 else 1) * ((obs.filterMap Prod.snd).map (entry v)).prod
      else 0) := by
  intro counts
  unfold Directory.weight
  cases he : D.observations bank with
  | none => simp
  | some obs =>
    by_cases hv : (∀ r ∈ D.records, r.Valid D.boxes bank) ∧ countsValid bank D.reportedCounts obs
    · have h := checked_count_product D bank v obs hv.2
      change FieldStack.productPaths _ _ _ _ _ counts = _ at h
      rw [h]
      cases hs : (obs.map Prod.fst).foldl Bool.xor false <;> simp [hv.2, hs]
    · simp [hv]

end FieldPowers

end BorderVNP
end Computability
end OAI
