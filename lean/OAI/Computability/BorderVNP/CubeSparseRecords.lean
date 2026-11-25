import OAI.Computability.BorderVNP.CubeConditioning

/-!
# Endpoint indexing for conditional-expectation records

In Section 8.1 the public computation processes compressed cable descriptors with
widths. Each covariance record concerns two descriptors sharing a cell and is
indexed at the at most three cells in their union. Fixing a different cell has
no effect on that record. Counting visits to these indices bounds the total work
over the traversal, without expanding the cable widths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Balancing

open Finset
open scoped BigOperators

variable {C L E : Type*} [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L]
  [Nonempty L] [Fintype E] [DecidableEq E]

/-- The list of descriptors touching a cell, before any labels have been fixed. -/
def incident (sites : E → Finset C) (c : C) := univ.filter fun i ↦ c ∈ sites i

/-- Ordered covariance records. A descriptor also has its own self-pair record. -/
def overlapRecords (sites : E → Finset C) : Finset (E × E) :=
  univ.filter fun p ↦ ¬ Disjoint (sites p.1) (sites p.2)

/-- Listing pairs in each incidence list gives a quadratic bound in the maximum
number of descriptors at a single cell. -/
theorem overlapRecords_card (sites : E → Finset C) {M : ℕ}
    (hM : ∀ c, (incident sites c).card ≤ M) :
    (overlapRecords sites).card ≤ Fintype.card C * M^2 := by
  let lists (c : C) := (incident sites c) ×ˢ (incident sites c)
  have cover : overlapRecords sites = univ.biUnion lists := by
    ext p; simp [overlapRecords,lists,incident,Finset.not_disjoint_iff]
  rw [cover]
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _c : C, M^2 := Finset.sum_le_sum fun c _ ↦ by
      simp only [lists,Finset.card_product,sq]; exact Nat.mul_le_mul (hM c) (hM c)
    _ = _ := by simp

/-- Total indexed covariance visits over the entire traversal. This counts a
record once for each of its endpoint cells, even when the same pair shares two. -/
theorem overlapRecord_visits (sites : E → Finset C) {M : ℕ}
    (hM : ∀ c, (incident sites c).card ≤ M) (hr : ∀ i, (sites i).card ≤ 2) :
    (∑ c : C, ((overlapRecords sites).filter fun p ↦ c ∈ sites p.1 ∪ sites p.2).card) ≤
      3 * Fintype.card C * M^2 := by
  have support (p : E × E) (hp : p ∈ overlapRecords sites) : (sites p.1 ∪ sites p.2).card ≤ 3 := by
    have hinter : (sites p.1 ∩ sites p.2).Nonempty := by
      obtain ⟨c,hc,hc'⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hp).2
      exact ⟨c,mem_inter.mpr ⟨hc,hc'⟩⟩
    have hc := Finset.card_union_add_card_inter (sites p.1) (sites p.2)
    have := hinter.card_pos
    have := hr p.1
    have := hr p.2
    omega
  calc
    _ = ∑ p ∈ overlapRecords sites, (sites p.1 ∪ sites p.2).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Fintype.sum_ite_mem,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
    _ ≤ ∑ _p ∈ overlapRecords sites, 3 := Finset.sum_le_sum support
    _ ≤ _ := by
      rw [Finset.sum_const,smul_eq_mul]
      calc
        _ ≤ (Fintype.card C * M^2) * 3 := Nat.mul_le_mul_right _ (overlapRecords_card _ hM)
        _ = _ := by ring

omit [Nonempty L] in
/-- An unaffected descriptor keeps its exact pinned chance during a trial assignment. -/
theorem pinnedChance_unchanged (p : Pattern C L) (s : Finset C) (x : C → L)
    (c : C) (hc : c ∉ p.sites) (v : L) :
    pinnedChance p (insert c s) (Function.update x c v) = pinnedChance p s x := by
  have hsites : p.sites ∩ insert c s = p.sites ∩ s := by ext; simp; grind
  have condition : (∀ i ∈ p.sites ∩ s, Function.update x c v i = p.value i) ↔
      ∀ i ∈ p.sites ∩ s, x i = p.value i := by
    have eq (i : C) (hi : i ∈ p.sites ∩ s) : Function.update x c v i = x i :=
      Function.update_of_ne (show i ≠ c from fun h ↦ hc (h ▸ (mem_inter.mp hi).1)) _ _
    exact ⟨fun h i hi ↦ (eq i hi).symm.trans (h i hi), fun h i hi ↦ (eq i hi).trans (h i hi)⟩
  simp only [pinnedChance,hsites,condition,Finset.sdiff_insert_of_notMem hc]

omit [Nonempty L] in
/-- A covariance is unchanged at every cell outside the union of its two supports. -/
theorem covariance_unchanged (p q : Pattern C L) (s : Finset C) (x : C → L)
    (c : C) (hc : c ∉ p.sites ∪ q.sites) (v : L) :
    jointChance p q (insert c s) (Function.update x c v) -
      pinnedChance p (insert c s) (Function.update x c v) *
      pinnedChance q (insert c s) (Function.update x c v) =
    jointChance p q s x - pinnedChance p s x * pinnedChance q s x := by
  rw [pinnedChance_unchanged p s x c (fun h ↦ hc (mem_union_left _ h)) v,
    pinnedChance_unchanged q s x c (fun h ↦ hc (mem_union_right _ h)) v]
  unfold jointChance
  split
  · rw [pinnedChance_unchanged _ s x c hc v]
  · rfl

end Cube.Balancing

end BorderVNP
end Computability
end OAI
