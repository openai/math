import OAI.Hierarchy.DescentColoredHost
import OAI.Hierarchy.DescentMatchedPublication

namespace OAI
/-! # Scalar accepted-row counts along the complete padded public source roster -/
namespace Hierarchy.DescentPacking.MatchedStageRAM
open PairRAM Computability.BorderVNP.Crossing
open DescentSixParty.StarKeys (NativePair)
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {C : Type} [Fintype C] (id : C↪ℕ) (rows : C→ℕ)

/-- Exclusive accepted mass at a physical source number, including every
empty numerical slot before the next occupied colony. -/
def countAt (q : ℕ) := ∑c∈Finset.univ.filter (fun c=>id c < q),rows c

theorem countAt_start : countAt id rows 0=0 := by simp [countAt]

theorem countAt_live (c : C) {q : ℕ} (live : id c=q) : countAt id rows (q+1)=countAt id rows q+rows c := by
  classical
  have add : (Finset.univ.filter (fun d : C=>id d < q+1))=insert c (Finset.univ.filter fun d=>id d < q) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · intro h
      by_cases same : id d=q
      · exact Or.inl (id.injective (same.trans live.symm))
      · exact Or.inr (by omega)
    · rintro (rfl|h) <;> omega
  unfold countAt
  rw [add,Finset.sum_insert (by simp [live]),Nat.add_comm]

theorem countAt_empty {q : ℕ} (empty : ∀c,id c≠q) : countAt id rows (q+1)=countAt id rows q := by
  unfold countAt
  congr 1
  ext c
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have ne:=empty c
  omega

theorem countAt_mono : Monotone (countAt id rows) := by
  intro a b h
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _=>Nat.zero_le _)
  intro c hc
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hc).2.trans_le h⟩

theorem countAt_end {G : ℕ} (bounds : ∀c,id c < G) : countAt id rows G=∑c,rows c := by
  have all : (Finset.univ.filter fun c=>id c < G)=Finset.univ := by ext c;simp [bounds]
  simp only [countAt,all]

/-- Reading the compiled loop's prior word before a real source gives its
exclusive prefix, even with arbitrarily many zero-item or absent groups. -/
theorem countAt_loop {G : ℕ} (acc : Fin (G+1)→ℕ) (initial : acc 0=0)
    (live : ∀q : Fin G,∀c,id c=q.val→acc q.succ=acc q.castSucc+rows c)
    (empty : ∀q : Fin G,(∀c,id c≠q.val)→acc q.succ=acc q.castSucc) (q : Fin (G+1)) :
    acc q=countAt id rows q.val := by
  induction q using Fin.induction with
  | zero=>exact initial.trans (countAt_start id rows).symm
  | succ q ih=>
    by_cases h : ∃c,id c=q.val
    · obtain ⟨c,eqn⟩:=h
      exact (live q c eqn).trans ((congrArg (·+rows c) ih).trans (countAt_live id rows c eqn).symm)
    · have none : ∀c,id c≠q.val := fun c eqn=>h ⟨c,eqn⟩
      exact (empty q none).trans (ih.trans (countAt_empty id rows none).symm)

/-- The native offset may remain a word throughout the loop. Converting to
a natural is needed only once at the boundary read by the profile validator. -/
theorem countAt_loop_word {G w : ℕ} (acc : Fin (G+1) → Computability.VPVNP.BurstRAM.Word w)
    (initial : acc 0=0)
    (live : ∀q : Fin G,∀c,id c=q.val → acc q.succ=acc q.castSucc+(rows c:Computability.VPVNP.BurstRAM.Word w))
    (empty : ∀q : Fin G,(∀c,id c≠q.val)→acc q.succ=acc q.castSucc) (q : Fin (G+1)) :
    acc q=(countAt id rows q.val:Computability.VPVNP.BurstRAM.Word w) := by
  induction q using Fin.induction with
  | zero=>simpa only [Fin.val_zero,countAt_start,Nat.cast_zero] using initial
  | succ q ih=>
    simp only [Fin.val_castSucc] at ih
    by_cases h : ∃c,id c=q.val
    · obtain ⟨c,eqn⟩:=h
      rw [live q c eqn,ih,Fin.val_succ,countAt_live id rows c eqn,Nat.cast_add]
    · have none : ∀c,id c≠q.val := fun c eqn=>h ⟨c,eqn⟩
      rw [empty q none,ih,Fin.val_succ,countAt_empty id rows none]

variable {D : ℕ} {P : Type*} {bits : P→ℕ} (N : Network D P bits) [DecidableEq C]
variable (core : Finset N.Edge) (home : N.Site→C) (color : N.Site→Bool) (B : ℕ)
local notation "T" => nativeTraffic N core home
local notation "row" => fun c=>Fintype.card (Matched T B (thinList home color c) (thickList home color c))

theorem countAt_groupStart (c : C) : countAt id row (id c)=groupStartBy N core home color B id c := rfl

theorem countAt_all {G : ℕ} (bounds : ∀c,id c < G) :
    countAt id row G=Fintype.card (NativePair N core home color B) := by
  rw [countAt_end _ _ bounds]
  exact (Fintype.card_sigma).symm

theorem countAt_le_card (t : ℕ) : countAt id row t ≤ Fintype.card (NativePair N core home color B) := by
  change (∑c∈Finset.univ.filter (fun c=>id c<t),row c) ≤ Fintype.card (Σc,Matched T B (thinList home color c) (thickList home color c))
  rw [Fintype.card_sigma]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)

theorem row_lt_countAt (e : NativePair N core home color B) {t : ℕ} (past : id e.1 < t) :
    (globalNumberBy N core home color B id e).val < countAt id row t := by
  rcases e with ⟨c,e⟩
  calc
    (globalNumberBy N core home color B id ⟨c,e⟩).val
        = countAt id row (id c)+(pairNumber _ _ e).val := group_order_by N core home color B id c e
    _ < countAt id row (id c)+row c := Nat.add_lt_add_left (pairNumber _ _ e).isLt _
    _ = countAt id row (id c+1) := (countAt_live id row c rfl).symm
    _ ≤ countAt id row t := countAt_mono id row (Nat.succ_le_of_lt past)

theorem countAt_original {G : ℕ} (room : Fintype.card C≤G) :
    countAt (originalId C) row G=Fintype.card (NativePair N core home color B) :=
  countAt_all (originalId C) N core home color B (fun c=>(Fintype.equivFin C c).isLt.trans_le room)


end
end Hierarchy.DescentPacking.MatchedStageRAM

end OAI
