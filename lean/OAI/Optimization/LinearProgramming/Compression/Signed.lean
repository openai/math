import OAI.Optimization.LinearProgramming.Compression.SeparationBasic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

variable {ι : Type*}

/-- Separate the positive and negative parts of a ternary integer form. -/
private theorem signed_sum_eq_sub (J : Finset ι) (l : ι → ℝ) (ε : ι → ℤ)
    (hε : ∀ i ∈ J, ε i = -1 ∨ ε i = 0 ∨ ε i = 1) :
    ∑ i ∈ J, (ε i : ℝ) * l i =
      (∑ i ∈ J.filter (fun i => ε i = 1), l i) -
       ∑ i ∈ J.filter (fun i => ε i = -1), l i := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hε i hi with h | h | h <;> simp [h]

private noncomputable def subsetDiff (A B : Finset ι) (i : ι) : ℤ := by
  classical exact (if i ∈ A then 1 else 0) - (if i ∈ B then 1 else 0)

private theorem subsetDiff_ternary (A B : Finset ι) (i : ι) :
    subsetDiff A B i = -1 ∨ subsetDiff A B i = 0 ∨ subsetDiff A B i = 1 := by
  classical
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [subsetDiff, ha, hb]

private theorem sum_subsetDiff (J : Finset ι) (l : ι → ℝ) (A B : Finset ι)
    (hA : A ⊆ J) (hB : B ⊆ J) :
    (∑ i ∈ J, (subsetDiff A B i : ℝ) * l i) = (∑ i ∈ A, l i) - ∑ i ∈ B, l i := by
  classical
  have hsum (S : Finset ι) (hS : S ⊆ J) :
      (∑ i ∈ J, if i ∈ S then l i else 0) = ∑ i ∈ S, l i := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    exact Finset.mem_filter.trans ⟨And.right, fun hi => ⟨hS hi, hi⟩⟩
  rw [← hsum A hA, ← hsum B hB, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [subsetDiff, ha, hb]

/-- Dissociation in terms of the nonzero ternary forms in Section 3. -/
theorem isDissociated_iff_signed (l : ι → ℝ) (J : Finset ι) :
    IsDissociated l J ↔
      ∀ ε : ι → ℤ, (∀ i ∈ J, ε i = -1 ∨ ε i = 0 ∨ ε i = 1) →
        (∃ i ∈ J, ε i ≠ 0) → 2 < |∑ i ∈ J, (ε i : ℝ) * l i| := by
  classical
  constructor
  · intro h ε hε hn
    rw [signed_sum_eq_sub J l ε hε]
    apply h _ (Finset.filter_subset _ _) _ (Finset.filter_subset _ _)
    obtain ⟨i, hi, hn⟩ := hn
    intro heq
    have hmem := Finset.ext_iff.mp heq i
    simp only [Finset.mem_filter, hi, true_and] at hmem
    rcases hε i hi with hc | hc | hc
    · have hpos := hmem.mpr hc
      omega
    · exact hn hc
    · have hneg := hmem.mp hc
      omega
  · intro h A hA B hB hAB
    let ε := subsetDiff A B
    have hn : ∃ i ∈ J, ε i ≠ 0 := by
      by_contra! hz
      apply hAB
      ext i
      constructor
      · intro hi
        by_contra hni
        simpa [ε, subsetDiff, hi, hni] using hz i (hA hi)
      · intro hi
        by_contra hni
        simpa [ε, subsetDiff, hi, hni] using hz i (hB hi)
    have hform := h ε (fun i _ => subsetDiff_ternary A B i) hn
    rwa [sum_subsetDiff J l A B hA hB] at hform

/-- A small signed form for a rejected insertion must involve the new index. -/
theorem exists_signed_of_not_isDissociated_insert [DecidableEq ι]
    (l : ι → ℝ) (J : Finset ι) (u : ι) (hu : u ∉ J)
    (hJ : IsDissociated l J) (hJu : ¬ IsDissociated l (insert u J)) :
    ∃ ε : ι → ℤ, (∀ i ∈ insert u J, ε i = -1 ∨ ε i = 0 ∨ ε i = 1) ∧
      ε u ≠ 0 ∧ |∑ i ∈ insert u J, (ε i : ℝ) * l i| ≤ 2 := by
  classical
  rw [isDissociated_iff_signed] at hJ hJu
  push Not at hJu
  obtain ⟨ε, hε, ⟨i, hi, hne⟩, hsmall⟩ := hJu
  refine ⟨ε, hε, ?_, hsmall⟩
  intro hz
  have hi' : i ∈ J := by
    rcases Finset.mem_insert.mp hi with rfl | hj
    · exact (hne hz).elim
    · exact hj
  have hlarge := hJ ε (fun j hj => hε j (Finset.mem_insert_of_mem hj)) ⟨i, hi', hne⟩
  simp [Finset.sum_insert hu, hz] at hsmall
  exact (not_lt_of_ge hsmall) hlarge

/-- If adjoining an index destroys dissociation, its value is within two of
one signed subset sum of the old indices. -/
theorem exists_subsets_approx_of_not_isDissociated_insert [DecidableEq ι]
    (l : ι → ℝ) (J : Finset ι) (u : ι) (hu : u ∉ J)
    (hJ : IsDissociated l J) (hJu : ¬ IsDissociated l (insert u J)) :
    ∃ A ⊆ J, ∃ B ⊆ J, |l u - ((∑ i ∈ A, l i) - ∑ i ∈ B, l i)| ≤ 2 := by
  classical
  obtain ⟨ε, hε, hn, hsmall⟩ :=
    exists_signed_of_not_isDissociated_insert l J u hu hJ hJu
  have hrest := fun j (hj : j ∈ J) => hε j (Finset.mem_insert_of_mem hj)
  rw [Finset.sum_insert hu, signed_sum_eq_sub J l ε hrest] at hsmall
  rcases hε u (Finset.mem_insert_self _ _) with hm | hz | hp
  · refine ⟨J.filter (fun i => ε i = 1), Finset.filter_subset _ _,
           J.filter (fun i => ε i = -1), Finset.filter_subset _ _, ?_⟩
    rw [hm] at hsmall
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at hsmall
    rw [← abs_neg]
    convert hsmall using 2
    ring
  · exact (hn hz).elim
  · refine ⟨J.filter (fun i => ε i = -1), Finset.filter_subset _ _,
           J.filter (fun i => ε i = 1), Finset.filter_subset _ _, ?_⟩
    rw [hp] at hsmall
    simp only [Int.cast_one, one_mul] at hsmall
    convert hsmall using 2
    ring


/-- Extend a dissociated family to an inclusion-maximal one in a finite universe. -/
theorem exists_maximal_dissociated [DecidableEq ι] (l : ι → ℝ) (U J : Finset ι) (hJU : J ⊆ U)
    (hJ : IsDissociated l J) :
    ∃ I, J ⊆ I ∧ I ⊆ U ∧ IsDissociated l I ∧
      ∀ u ∈ U, u ∉ I → ¬ IsDissociated l (insert u I) := by
  classical
  let family := U.powerset.filter (fun I => J ⊆ I ∧ IsDissociated l I)
  have mem_family (I : Finset ι) : I ∈ family ↔ I ⊆ U ∧ J ⊆ I ∧ IsDissociated l I := by
    simp [family]
  have hj : J ∈ family := (mem_family J).mpr ⟨hJU, fun _ h => h, hJ⟩
  obtain ⟨I, hI, hmax⟩ := family.exists_max_image Finset.card ⟨J, hj⟩
  obtain ⟨hiu, hji, hd⟩ := (mem_family I).mp hI
  refine ⟨I, hji, hiu, hd, ?_⟩
  intro u hu hnu hins
  have hmem : insert u I ∈ family := (mem_family _).mpr
    ⟨Finset.insert_subset hu hiu, fun i hi => Finset.mem_insert_of_mem (hji hi), hins⟩
  have hcard := hmax _ hmem
  rw [Finset.card_insert_of_notMem hnu] at hcard
  omega

/-- Each point in a finite universe admits a ternary linear combination on the
same maximal family. On that family the combination is its coordinate function. -/
theorem exists_simultaneous_ternary_approx [DecidableEq ι] (l : ι → ℝ)
    (U J : Finset ι) (hJU : J ⊆ U) (hJ : IsDissociated l J) :
    ∃ I, J ⊆ I ∧ I ⊆ U ∧ IsDissociated l I ∧
      ∃ c : U → ι → ℤ,
        ∀ u, (∀ i, c u i = -1 ∨ c u i = 0 ∨ c u i = 1) ∧
          (∀ i ∉ I, c u i = 0) ∧
          (u.val ∈ I → ∀ i, c u i = if i = u.val then 1 else 0) ∧
          |l u - ∑ i ∈ I, (c u i : ℝ) * l i| ≤ 2 := by
  classical
  obtain ⟨I, hji, hiu, hd, hmax⟩ := exists_maximal_dissociated l U J hJU hJ
  have hrow (u : U) : ∃ row : ι → ℤ,
      (∀ i, row i = -1 ∨ row i = 0 ∨ row i = 1) ∧
      (∀ i ∉ I, row i = 0) ∧
      (u.val ∈ I → ∀ i, row i = if i = u.val then 1 else 0) ∧
      |l u - ∑ i ∈ I, (row i : ℝ) * l i| ≤ 2 := by
    by_cases hu : u.val ∈ I
    · refine ⟨(fun i => if i = u.val then 1 else 0), ?_, ?_, fun _ _ => rfl, ?_⟩
      · intro i
        by_cases hi : i = u.val <;> simp [hi]
      · intro i hi
        have hne : i ≠ u.val := fun h => hi (h.symm ▸ hu)
        simp [hne]
      · simp [Int.cast_ite, ite_mul, hu]
    · obtain ⟨A, hA, B, hB, herr⟩ :=
        exists_subsets_approx_of_not_isDissociated_insert l I u hu hd (hmax u u.property hu)
      refine ⟨subsetDiff A B, subsetDiff_ternary A B, ?_, fun h => (hu h).elim, ?_⟩
      · intro i hi
        have hna : i ∉ A := fun ha => hi (hA ha)
        have hnb : i ∉ B := fun hb => hi (hB hb)
        simp [subsetDiff, hna, hnb]
      · rwa [sum_subsetDiff I l A B hA hB]
  choose c hc using hrow
  exact ⟨I, hji, hiu, hd, c, hc⟩

/-- Round a residual in [-2,2] down to the grid with positive denominator D.
The numerator also satisfies the uniform bound 2D. -/
private theorem floor_grid {r : ℝ} (hr : |r| ≤ 2) (D : ℕ) (hD : 0 < D) :
    |⌊(D : ℝ) * r⌋| ≤ 2 * (D : ℤ) ∧
    |r - (⌊(D : ℝ) * r⌋ : ℤ) / (D : ℝ)| < 1 / (D : ℝ) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨hr₁, hr₂⟩ := abs_le.mp hr
  have h₁ := Int.floor_le ((D : ℝ) * r)
  have h₂ := Int.lt_floor_add_one ((D : ℝ) * r)
  constructor
  · apply abs_le.mpr
    constructor
    · apply Int.le_floor.mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hr₁ hd.le]
    · apply Int.floor_le_iff.mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hr₂ hd.le]
  · rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hd).mpr (by linarith))) ,
      sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hd]
    linarith

/-- The common set of generators admits simultaneous affine approximations on
any grid of mesh 1/D. All coefficients are ternary and the absolute value of
each residual numerator is at most 2D. -/
theorem exists_simultaneous_affine_grid [DecidableEq ι] (l : ι → ℝ)
    (U J : Finset ι) (hJU : J ⊆ U) (hJ : IsDissociated l J) (D : ℕ) (hD : 0 < D) :
    ∃ I, J ⊆ I ∧ I ⊆ U ∧ IsDissociated l I ∧
      ∃ (c : U → ι → ℤ) (k : U → ℤ),
        ∀ u, (∀ i, c u i = -1 ∨ c u i = 0 ∨ c u i = 1) ∧
          (∀ i ∉ I, c u i = 0) ∧
          (u.val ∈ I → k u = 0 ∧ ∀ i, c u i = if i = u.val then 1 else 0) ∧
          |k u| ≤ 2 * (D : ℤ) ∧
          |l u - ((∑ i ∈ I, (c u i : ℝ) * l i) + (k u : ℝ) / D)| < 1 / (D : ℝ) := by
  classical
  obtain ⟨I, hji, hiu, hd, c, hc⟩ :=
    exists_simultaneous_ternary_approx l U J hJU hJ
  let r (u : U) := l u - ∑ i ∈ I, (c u i : ℝ) * l i
  refine ⟨I, hji, hiu, hd, c, fun u => ⌊(D : ℝ) * r u⌋, ?_⟩
  intro u
  obtain ⟨hcoeff, hsupp, hcoordinate, hres⟩ := hc u
  obtain ⟨hnum, herr⟩ := floor_grid hres D hD
  refine ⟨hcoeff, hsupp, ?_, hnum, ?_⟩
  · intro hu
    refine ⟨?_, hcoordinate hu⟩
    simp [r, hcoordinate hu, Int.cast_ite, ite_mul, hu]
  · rw [← sub_sub]
    exact herr

end Compression
end LinearProgramming
end Optimization
end OAI
