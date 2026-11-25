import OAI.Computability.BorderVNP.FragmentBucketOrder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace OAI
/-! # Dense prefix addresses for the bit units of ordered occurrence records -/

noncomputable section
namespace Hierarchy.ProtocolRAMPortRanks
open scoped Classical BigOperators

variable {I : Type*} [Fintype I] (width rank : I → ℕ)

/-- Start of a row in the ordering determined by its scalar rank. -/
def «prefix» (i : I) := ∑ j ∈ Finset.univ.filter (fun j => rank j<rank i), width j

private theorem prefix_le (i : I) (s : Finset I) (more : insert i
    (Finset.univ.filter fun j => rank j<rank i) ⊆ s) :
    «prefix» width rank i+width i ≤ ∑ j ∈ s, width j := by
  classical
  rw [Nat.add_comm]
  unfold «prefix»
  rw [←Finset.sum_insert (show i ∉ Finset.univ.filter (fun j=>rank j<rank i) by simp)]
  exact Finset.sum_le_sum_of_subset_of_nonneg more (by intros; omega)

theorem prefix_disjoint {i j : I} (lt : rank i<rank j) :
    «prefix» width rank i+width i≤«prefix» width rank j := by
  apply prefix_le
  intro t ht
  rcases Finset.mem_insert.mp ht with eqn|before
  · simpa only [eqn,Finset.mem_filter,Finset.mem_univ,true_and] using lt
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp before).2.trans lt⟩

theorem prefix_end (i : I) : «prefix» width rank i+width i≤∑ j,width j :=
  prefix_le width rank i _ (Finset.subset_univ _)

abbrev Units (width : I → ℕ) := (i:I) × Fin (width i)

/-- A unit is the concatenation offset in its real row. Zero-width
rows reserve no positions. -/
def address (u : Units width) : Fin (∑ j, width j) :=
  ⟨«prefix» width rank u.1+u.2.val,
    (Nat.add_lt_add_left u.2.isLt _).trans_le (prefix_end width rank u.1)⟩

theorem injective (distinct : Function.Injective rank) : Function.Injective (address width rank) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have same := congrArg Fin.val h
  change «prefix» width rank i+a.val=«prefix» width rank j+b.val at same
  by_cases eqn : i=j
  · subst j
    exact congrArg (Sigma.mk i) (Fin.ext (by omega))
  have different := distinct.ne eqn
  rcases Nat.lt_or_gt_of_ne different with hij|hji
  · have := prefix_disjoint width rank hij
    have := a.isLt
    omega
  · have := prefix_disjoint width rank hji
    have := b.isLt
    omega

def enumerate (distinct : Function.Injective rank) : Units width ≃ Fin (∑ j, width j) :=
  Equiv.ofBijective (address width rank) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨injective width rank distinct,by simp [Units,Fintype.card_sigma]⟩)

/-- Ordering by physical endpoint and then original row index makes each
endpoint's pieces contiguous in the bank. -/
def bySite {n : ℕ} (site : Fin n → ℕ) (i : Fin n) := site i*n+i.val

/-- The native sorter may compare two separate words. It need never
materialize the mathematical product of the site and row count. -/
theorem bySite_lt_iff {n : ℕ} (site : Fin n → ℕ) (i j : Fin n) :
    bySite site i < bySite site j ↔ site i<site j ∨ (site i=site j ∧ i.val<j.val) := by
  have hi := i.isLt
  have hj := j.isLt
  unfold bySite
  rcases lt_trichotomy (site i) (site j) with lt|eq|gt
  · have h := Nat.mul_le_mul_right n lt
    rw [Nat.succ_mul] at h
    omega
  · rw [eq]
    omega
  · have h := Nat.mul_le_mul_right n gt
    rw [Nat.succ_mul] at h
    omega

theorem bySite_injective {n : ℕ} (site : Fin n → ℕ) : Function.Injective (bySite site) := by
  intro i j h
  apply Fin.ext
  have eqn := congrArg (· % n) h
  simpa [bySite,Nat.add_mod,i.isLt,j.isLt,Nat.mod_eq_of_lt] using eqn

open Computability.BorderVNP.FragmentBucket

private theorem start_mono {n cells : ℕ} (site : Fin n → Fin cells) :
    Monotone (start site) := by
  intro i j le
  unfold start
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono le) (by intros; omega)

private theorem prior_mono {n cells : ℕ} (site : Fin n → Fin cells) (c : Fin cells) :
    Monotone fun i => prior site i c := by
  intro i j h
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,lt_of_lt_of_le (Finset.mem_filter.mp hx).2 h⟩

private theorem dest_lt_of_key {n cells : ℕ} (site : Fin n → Fin cells) {i j : Fin n}
    (h : bySite (fun k=>(site k).val) i < bySite (fun k=>(site k).val) j) :
    (dest site i).val<(dest site j).val := by
  rw [dest_val,dest_val]
  rcases (bySite_lt_iff _ _ _).mp h with different|⟨same,before⟩
  · have next := start_mono site (show (site i).val+1≤(site j).val from different)
    rw [start_step] at next
    have bound := prior_mono site (site i) (show i.val+1≤n from i.isLt)
    dsimp only at bound
    rw [prior_step,prior_end,ite_eq_left rfl] at bound
    omega
  · have eqn : site i=site j := Fin.ext same
    have next := prior_mono site (site j) (show i.val+1≤j.val from before)
    dsimp only at next
    rw [prior_step,ite_eq_left eqn] at next
    rw [eqn]
    omega

/-- The old verified stable counting-sort permutation yields exactly
the endpoint/occurrence order used by the side-address prefix. -/
theorem dest_lt_iff {n cells : ℕ} (site : Fin n → Fin cells) (i j : Fin n) :
    (dest site i).val<(dest site j).val ↔
      bySite (fun k=>(site k).val) i < bySite (fun k=>(site k).val) j := by
  refine ⟨fun order=>?_,dest_lt_of_key site⟩
  rcases lt_trichotomy (bySite (fun k=>(site k).val) i) (bySite (fun k=>(site k).val) j) with h|h|h
  · exact h
  · have same := bySite_injective _ h
    subst j
    exact (Nat.lt_irrefl _ order).elim
  · have backwards := dest_lt_of_key site h
    omega

end Hierarchy.ProtocolRAMPortRanks

end
end OAI
