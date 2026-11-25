import OAI.Hierarchy.DescentPhysicalOrder
import OAI.Hierarchy.TraceIntervalScanner

namespace OAI
/-! # First occurrence of each occupied cell in the physical site directory -/

namespace Hierarchy.DescentFirstOccurrence
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {U C : Type*} [Fintype C] {n cells : ℕ}
    (row : U ≃ Fin n) (group : U → C) (covered : Function.Surjective group)

def rank := DescentPhysicalOrder.first (row.toEmbedding.trans Fin.valEmbedding) group covered

def dest (cell : C ↪ Fin cells) (i : Fin n) := cell (group (row.symm i))

def earlier (t : ℕ) : Finset C := Finset.univ.filter (fun c => rank row group covered c < t)

theorem count_at (c : C) :
    (earlier row group covered (rank row group covered c)).card =
      (DescentPhysicalOrder.physical (rank row group covered) c).val :=
  (DescentPhysicalOrder.physical_val ..).symm

omit [Fintype C] in
theorem rank_le (i : Fin n) : rank row group covered (group (row.symm i)) ≤ i.val := by
  simpa [rank] using DescentPhysicalOrder.first_le (row.toEmbedding.trans Fin.valEmbedding) group covered (row.symm i)

omit [Fintype C] in
theorem rank_at (c : C) : ∃ i : Fin n, group (row.symm i) = c ∧ i.val = rank row group covered c := by
  obtain ⟨u,a,b⟩ := DescentPhysicalOrder.first_at (row.toEmbedding.trans Fin.valEmbedding) group covered c
  exact ⟨row u,by simpa using a,b⟩

theorem count_zero : (earlier row group covered 0).card = 0 := by simp [earlier]

theorem count_step (i : Fin n) : (earlier row group covered (i.val+1)).card =
    (earlier row group covered i.val).card + (if rank row group covered (group (row.symm i)) = i.val then 1 else 0) := by
  let c := group (row.symm i)
  have same (d : C) (h : rank row group covered d = i.val) : d=c := by
    obtain ⟨j,hj,eqn⟩ := rank_at row group covered d
    have hj' : j=i := Fin.ext (eqn.trans h)
    subst j
    exact hj.symm
  by_cases seen : rank row group covered c = i.val
  · have union_ : earlier row group covered (i.val+1) = insert c (earlier row group covered i.val) := by
      ext d
      simp only [earlier,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
      constructor
      · intro before
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp before) with lt | eqn
        · exact Or.inr lt
        · exact Or.inl (same d eqn)
      · rintro (rfl | lt)
        · omega
        · omega
    have fresh : c ∉ earlier row group covered i.val := by simp [earlier,seen]
    rw [union_,Finset.card_insert_of_notMem fresh,ite_eq_left seen]
  · have identical : earlier row group covered (i.val+1) = earlier row group covered i.val := by
      ext d
      simp only [earlier,Finset.mem_filter,Finset.mem_univ,true_and]
      have ne : rank row group covered d ≠ i.val := fun eqn => seen ((same d eqn) ▸ eqn)
      omega
    rw [identical,ite_eq_right seen,Nat.add_zero]

omit [Fintype C] in
/-- The genuine reverse scatter stores the earliest row plus one at each occupied cell. -/
theorem head {w H N : ℕ} (cell : C ↪ Fin cells) {m o : Memory w}
    (ran : TraceIntervalScanner.Output H N (dest row group cell) m o) (c : C) :
    (o (H+(cell c).val)).val = rank row group covered c + 1 := by
  let xs := (List.finRange n).filter (fun j => decide (dest row group cell j=cell c))
  have member (i : Fin n) : i∈xs ↔ group (row.symm i)=c := by simp [xs,dest]
  obtain ⟨i,hi,iRank⟩ := rank_at row group covered c
  have hi' := (member i).mpr hi
  have chain : TraceIntervalScanner.Chain N o (o (H+(cell c).val)).val xs := ran.chain (cell c)
  have order : xs.Pairwise (· < ·) := (List.pairwise_lt_finRange n).filter _
  cases split_ : xs with
  | nil => simp [split_] at hi'
  | cons j js =>
    have hj := (member j).mp (by rw [split_]; exact .head _)
    have le : rank row group covered c ≤ j.val := hj ▸ rank_le row group covered j
    have le' : j.val ≤ i.val := by
      rw [split_] at hi' order
      rcases List.mem_cons.mp hi' with eqn|tail
      · exact eqn ▸ le_rfl
      · exact ((List.pairwise_cons.mp order).1 _ tail).le
    rw [split_] at chain
    exact chain.1.trans (by omega)

end
end Hierarchy.DescentFirstOccurrence

end OAI
