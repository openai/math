import OAI.Computability.BorderVNP.CubeLabels

/-!
# Conditional scores of cable and data counts

Fixing labels one cell at a time uses conditional means and covariances. A
pattern's mean reads only its own endpoint labels. A pair covariance vanishes
unless the two supports overlap, even after conditioning. Thus the conditional
score for a count has exactly the local records described in Section 8.1.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Balancing

open Finset
open scoped BigOperators

variable {C L : Type*} [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Nonempty L]

/-- Keep the labels of the fixed cells and assign the free cells using `y`. -/
def fill (s : Finset C) (x y : C → L) (c : C) : L := if c ∈ s then x c else y c

/-- Conditional probability of a bit-pattern given labels on a fixed set. -/
noncomputable def pinnedChance (p : Pattern C L) (s : Finset C) (x : C → L) : ℝ :=
  if ∀ c ∈ p.sites ∩ s, x c = p.value c then
    (Fintype.card L : ℝ)⁻¹ ^ (p.sites \ s).card else 0

private def freePart (p : Pattern C L) (s : Finset C) : Pattern C L :=
  ⟨p.sites \ s, p.value⟩

omit [Fintype L] [Nonempty L] in
private theorem split_hit (p : Pattern C L) (s : Finset C) (x y : C → L) :
    hit p (fill s x y) =
      if ∀ c ∈ p.sites ∩ s, x c = p.value c then hit (freePart p s) y else 0 := by
  have iff : (∀ c ∈ p.sites, fill s x y c = p.value c) ↔
      (∀ c ∈ p.sites ∩ s, x c = p.value c) ∧ (∀ c ∈ p.sites \ s, y c = p.value c) := by
    constructor
    · intro h
      exact ⟨fun c hc ↦ by simpa [fill,(mem_inter.mp hc).2] using h c (mem_inter.mp hc).1,
        fun c hc ↦ by simpa [fill,(mem_sdiff.mp hc).2] using h c (mem_sdiff.mp hc).1⟩
    · rintro ⟨h₁,h₂⟩ c hc
      by_cases hs : c ∈ s
      · simpa [fill,hs] using h₁ c (mem_inter.mpr ⟨hc,hs⟩)
      · simpa [fill,hs] using h₂ c (mem_sdiff.mpr ⟨hc,hs⟩)
  simp only [hit, freePart, iff]; split_ifs <;> simp_all

/-- The conditional mean uses only the pattern's own cell labels and the
number of them still unfixed. -/
theorem expect_pinned_hit (p : Pattern C L) (s : Finset C) (x : C → L) :
    (𝔼 y, hit p (fill s x y)) = pinnedChance p s x := by
  simp_rw [split_hit]
  by_cases h : ∀ c ∈ p.sites ∩ s, x c = p.value c
  · simp only [pinnedChance,ite_eq_left h,expect_hit,chance,freePart]
  · simp only [pinnedChance,ite_eq_right h,Fintype.expect_const]

private def combine (p q : Pattern C L) : Pattern C L :=
  ⟨p.sites ∪ q.sites, fun c ↦ if c ∈ p.sites then p.value c else q.value c⟩

/-- Conditional joint probability for a pair of bit-patterns. -/
noncomputable def jointChance (p q : Pattern C L) (s : Finset C) (x : C → L) : ℝ :=
  if ∀ c ∈ p.sites ∩ q.sites, p.value c = q.value c then pinnedChance (combine p q) s x else 0

omit [Fintype L] [Nonempty L] in
private theorem combined_hit (p q : Pattern C L) (y : C → L) :
    hit p y * hit q y =
      if ∀ c ∈ p.sites ∩ q.sites, p.value c = q.value c then hit (combine p q) y else 0 := by
  by_cases hc : ∀ c ∈ p.sites ∩ q.sites, p.value c = q.value c
  · have iff : (∀ c ∈ (combine p q).sites, y c = (combine p q).value c) ↔
        (∀ c ∈ p.sites, y c = p.value c) ∧ (∀ c ∈ q.sites, y c = q.value c) := by
      constructor
      · intro h
        refine ⟨fun c hcp ↦ by simpa [combine,hcp] using h c (mem_union_left _ hcp), ?_⟩
        intro c hcq
        by_cases hcp : c ∈ p.sites
        · simpa [combine,hcp,hc c (mem_inter.mpr ⟨hcp,hcq⟩)] using h c (mem_union_right _ hcq)
        · simpa [combine,hcp] using h c (mem_union_right _ hcq)
      · rintro ⟨hp,hq⟩ c h
        by_cases hcp : c ∈ p.sites
        · simpa [combine,hcp] using hp c hcp
        · simpa [combine,hcp] using hq c ((mem_union.mp h).resolve_left hcp)
    simp only [hit, iff]; split_ifs <;> simp_all
  · simp only [hc, ↓reduceIte, hit]
    split_ifs with hp hq
    · exact (hc (fun c h ↦ (hp c (mem_inter.mp h).1).symm.trans (hq c (mem_inter.mp h).2))).elim
    all_goals simp

/-- The joint conditional mean reads only the union of the two endpoint sets. -/
theorem expect_pinned_product (p q : Pattern C L) (s : Finset C) (x : C → L) :
    (𝔼 y, hit p (fill s x y) * hit q (fill s x y)) = jointChance p q s x := by
  simp_rw [combined_hit]
  by_cases hc : ∀ c ∈ p.sites ∩ q.sites, p.value c = q.value c
  · simp only [jointChance,ite_eq_left hc,expect_pinned_hit]
  · simp only [jointChance,ite_eq_right hc,Fintype.expect_const]

/-- After conditioning on fixed cell labels, patterns with disjoint endpoint sets
still have zero covariance. -/
theorem pinned_independent (p q : Pattern C L) (s : Finset C) (x : C → L)
    (hd : Disjoint p.sites q.sites) :
    jointChance p q s x = pinnedChance p s x * pinnedChance q s x := by
  rw [← expect_pinned_product]
  simp_rw [split_hit]
  have hfree : Disjoint (freePart p s).sites (freePart q s).sites :=
    hd.mono sdiff_subset sdiff_subset
  by_cases hp : ∀ c ∈ p.sites ∩ s, x c = p.value c <;>
    by_cases hq : ∀ c ∈ q.sites ∩ s, x c = q.value c <;>
      unfold pinnedChance
  · simp only [ite_eq_left hp,ite_eq_left hq]
    exact expect_hit_mul _ _ hfree
  · simp only [ite_eq_right hq,mul_zero,Fintype.expect_const]
  · simp only [ite_eq_right hp,zero_mul,Fintype.expect_const]
  · simp only [ite_eq_right hp,zero_mul,Fintype.expect_const]

variable {E : Type*} [Fintype E]

/-- The conditional squared deviation uses the squared mean shift and one covariance
per ordered pair of descriptors sharing a cell. The widths are the multiplicities
of cable or data bits represented by each descriptor. -/
theorem sparse_conditional_score (p : E → Pattern C L) (w : E → ℝ) (m : ℝ)
    (s : Finset C) (x : C → L) :
    (𝔼 y, ((∑ i, w i * hit (p i) (fill s x y)) - m)^2) =
      ((∑ i, w i * pinnedChance (p i) s x) - m)^2 +
      ∑ i, ∑ j with ¬ Disjoint (p i).sites (p j).sites,
        w i * w j * (jointChance (p i) (p j) s x - pinnedChance (p i) s x * pinnedChance (p j) s x) := by
  let X (i : E) (y : C → L) := w i * hit (p i) (fill s x y)
  let M (i : E) := w i * pinnedChance (p i) s x
  have hx (i : E) : (𝔼 y, X i y) = M i := by
    dsimp [X,M]; rw [← Finset.mul_expect, expect_pinned_hit]
  have hp (i j : E) : (𝔼 y, X i y * X j y) = w i * w j * jointChance (p i) (p j) s x := by
    simp only [X, mul_mul_mul_comm (w i) _ (w j)]
    rw [← Finset.mul_expect, expect_pinned_product]
  have hm : (𝔼 y, ∑ i, X i y) = ∑ i, M i := by rw [Finset.expect_sum_comm]; simp only [hx]
  have hsq : (𝔼 y, (∑ i, X i y)^2) = ∑ i, ∑ j, w i*w j*jointChance (p i) (p j) s x := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.expect_sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.expect_sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ by simpa only [mul_comm (X i _) (X j _)] using hp i j
  have localRow (i : E) :
      (∑ j with ¬ Disjoint (p i).sites (p j).sites, w i*w j *
        (jointChance (p i) (p j) s x - pinnedChance (p i) s x * pinnedChance (p j) s x)) =
      (∑ j, w i*w j * jointChance (p i) (p j) s x) - M i * ∑ j, M j := by
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    by_cases h : Disjoint (p i).sites (p j).sites
    · simp [h,M,pinned_independent _ _ _ _ h]; ring
    · simp [h,M]; ring
  change (𝔼 y, ((∑ i, X i y)-m)^2) = ((∑ i, M i)-m)^2 + _
  simp_rw [localRow]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp_rw [sub_sq]
  rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, Fintype.expect_const,
    ← Finset.expect_mul, ← Finset.mul_expect, hm, hsq]
  ring

end Cube.Balancing

end BorderVNP
end Computability
end OAI
