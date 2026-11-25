import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Independent cell labels and cable-count variance

For Lemma 8.2, a bit contributes to a specified count when the labels on its
incident cells take specified values. Cable bits have two distinct incident cells
and incoming data bits have one. Indicators on disjoint sets of cells are independent.
This gives a second-moment bound using only the number of bits incident at a cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Balancing

open scoped BigOperators
open Finset

variable {C L : Type*} [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Nonempty L]

/-- The required labels at a finite set of cells. Values off that set are ignored. -/
structure Pattern (C L : Type*) where
  /-- Cells whose labels are prescribed. -/
  sites : Finset C
  /-- The prescribed label at each participating cell. -/
  value : C → L

/-- A bit's zero-or-one contribution at a given full labeling. -/
def hit (p : Pattern C L) (x : C → L) : ℝ := if ∀ c ∈ p.sites, x c = p.value c then 1 else 0

/-- Probability of hitting the specified labels under uniform independent sampling. -/
noncomputable def chance (p : Pattern C L) : ℝ := (Fintype.card L : ℝ)⁻¹ ^ p.sites.card

omit [Fintype L] [Nonempty L] in
private theorem hit_bounds (p : Pattern C L) (x : C → L) : 0 ≤ hit p x ∧ hit p x ≤ 1 := by
  unfold hit; split <;> norm_num

/-- A finite product with `k` prescribed labels has density `|L|^(-k)`. -/
theorem expect_hit (p : Pattern C L) : (𝔼 x, hit p x) = chance p := by
  classical
  let fibers (c : C) := if c ∈ p.sites then {p.value c} else (univ : Finset L)
  have mem (x : C → L) : x ∈ Fintype.piFinset fibers ↔ ∀ c ∈ p.sites, x c = p.value c := by
    rw [Fintype.mem_piFinset]
    constructor
    · intro h c hc; simpa [fibers,hc] using h c
    · intro h c; by_cases hc : c ∈ p.sites <;> simp [fibers,hc,h]
  have hcard : (Fintype.piFinset fibers).card = Fintype.card L ^ p.sitesᶜ.card := by
    rw [Fintype.card_piFinset]
    calc
      _ = ∏ c : C, (if c ∈ p.sitesᶜ then Fintype.card L else 1) := by
        apply prod_congr rfl
        intro c _; by_cases h : c ∈ p.sites <;> simp [fibers, h]
      _ = _ := by rw [Fintype.prod_ite_mem]; simp
  have htot : p.sitesᶜ.card + p.sites.card = Fintype.card C := by
    simp
  have hpos : (Fintype.card L : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.expect_eq_sum_div_card]
  simp only [hit, ← mem, Fintype.sum_ite_mem, sum_const, nsmul_eq_mul, mul_one, hcard,
    Fintype.card_fun, Nat.cast_pow, chance, ← htot, pow_add, inv_pow]
  field_simp
  push_cast
  rfl

/-- Independence of two bit indicators with disjoint endpoint sets. -/
theorem expect_hit_mul (p q : Pattern C L) (hd : Disjoint p.sites q.sites) :
    (𝔼 x, hit p x * hit q x) = chance p * chance q := by
  classical
  let r : Pattern C L := ⟨p.sites ∪ q.sites, fun c ↦ if c ∈ p.sites then p.value c else q.value c⟩
  have eqh (x : C → L) : hit p x * hit q x = hit r x := by
    have hr : (∀ c ∈ r.sites, x c = r.value c) ↔
        (∀ c ∈ p.sites, x c = p.value c) ∧ (∀ c ∈ q.sites, x c = q.value c) := by
      constructor
      · intro h
        exact ⟨fun c hc ↦ by simpa [r,hc] using h c (mem_union_left _ hc),
          fun c hc ↦ by simpa [r,Finset.disjoint_right.mp hd hc] using h c (mem_union_right _ hc)⟩
      · rintro ⟨hp,hq⟩ c hc
        rcases mem_union.mp hc with h | h
        · simpa [r,h] using hp c h
        · simpa [r,Finset.disjoint_right.mp hd h] using hq c h
    simp only [hit, hr]
    split_ifs <;> simp_all
  simp_rw [eqh, expect_hit]
  simp [chance, r, Finset.card_union_of_disjoint hd, pow_add]

private theorem covariance (p q : Pattern C L) :
    (𝔼 x, (hit p x - chance p) * (hit q x - chance q)) =
      (𝔼 x, hit p x * hit q x) - chance p * chance q := by
  simp_rw [sub_mul, mul_sub]
  rw [Finset.expect_sub_distrib, Finset.expect_sub_distrib, Finset.expect_sub_distrib,
    ← Finset.expect_mul, ← Finset.mul_expect, Fintype.expect_const, expect_hit, expect_hit]
  ring

variable {E : Type*} [Fintype E]

/-- Total number of bits whose prescribed cell labels match. -/
def load (p : E → Pattern C L) (x : C → L) : ℝ := ∑ i, hit (p i) x

/-- Cable or data count variance is bounded by the number of ordered pairs of bits
that have an endpoint in common. -/
theorem variance_le_overlaps (p : E → Pattern C L) :
    (𝔼 x, (load p x - ∑ i, chance (p i)) ^ 2) ≤
      ∑ i : E, ∑ j : E, if Disjoint (p i).sites (p j).sites then (0 : ℝ) else 1 := by
  classical
  have cov (i j : E) :
      (𝔼 x, (hit (p i) x - chance (p i)) * (hit (p j) x - chance (p j))) ≤
        if Disjoint (p i).sites (p j).sites then (0 : ℝ) else 1 := by
    rw [covariance]
    by_cases hd : Disjoint (p i).sites (p j).sites
    · simp [hd, expect_hit_mul _ _ hd]
    · rw [ite_eq_right_iff.mpr fun h ↦ (hd h).elim]
      have h : (𝔼 x, hit (p i) x * hit (p j) x) ≤ 1 :=
        Finset.expect_le univ_nonempty fun x _ ↦
          (mul_le_of_le_one_left (hit_bounds _ _).1 (hit_bounds _ _).2).trans (hit_bounds _ _).2
      have hp : 0 ≤ chance (p i) * chance (p j) := by unfold chance; positivity
      linarith
  have expand (x : C → L) : (load p x - ∑ i, chance (p i)) ^ 2 =
      ∑ i, ∑ j, (hit (p i) x - chance (p i)) * (hit (p j) x - chance (p j)) := by
    rw [load, ← Finset.sum_sub_distrib, sq, Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp_rw [expand]
  rw [Finset.expect_sum_comm]
  apply sum_le_sum fun i _ ↦ ?_
  rw [Finset.expect_sum_comm]
  exact sum_le_sum fun j _ ↦ cov i j

/-- A bit with at most `r` incident cells overlaps at most `r*M` bits if at
most `M` bits meet each cell. -/
theorem variance_le_incidence (p : E → Pattern C L) (r M : ℕ)
    (hr : ∀ i, (p i).sites.card ≤ r)
    (hM : ∀ c, (univ.filter (fun i ↦ c ∈ (p i).sites)).card ≤ M) :
    (𝔼 x, (load p x - ∑ i, chance (p i))^2) ≤ Fintype.card E * (r * M : ℕ) := by
  classical
  let inc (c : C) := univ.filter (fun j ↦ c ∈ (p j).sites)
  have bound (i : E) : ∑ j : E, (if Disjoint (p i).sites (p j).sites then (0:ℝ) else 1) ≤
      (r*M : ℕ) := by
    let s := (p i).sites.biUnion inc
    have eq (j : E) : (if Disjoint (p i).sites (p j).sites then (0:ℝ) else 1) =
        if j ∈ s then 1 else 0 := by
      have h : j ∈ s ↔ ¬ Disjoint (p i).sites (p j).sites := by
        simp [s,inc, Finset.not_disjoint_iff]
      by_cases h' : Disjoint (p i).sites (p j).sites <;> simp [h,h']
    simp_rw [eq, Fintype.sum_ite_mem, sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast (Finset.card_biUnion_le_card_mul (p i).sites inc M
      (fun c _ ↦ hM c)).trans (Nat.mul_le_mul_right M (hr i))
  exact (variance_le_overlaps p).trans ((sum_le_sum fun i _ ↦ bound i).trans_eq (by simp))

end Cube.Balancing

end BorderVNP
end Computability
end OAI
