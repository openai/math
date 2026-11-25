import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

/-! # Partition of the axes of a geometric grid

With `c = 1/24` the two thresholds have integer forms `N ≤ B^24` and
`B^12 ≤ N`. A full group satisfies both. At most one group falls short
of the first threshold.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {ι : Type*}

/-- Number of register settings on a list of axes. -/
def axisVolume (a : ι → ℕ) (xs : List ι) : ℕ := (xs.map a).prod

@[simp] lemma axisVolume_nil (a : ι → ℕ) : axisVolume a [] = 1 := rfl

@[simp] lemma axisVolume_cons (a : ι → ℕ) (x : ι) (xs : List ι) :
    axisVolume a (x :: xs) = a x * axisVolume a xs := rfl

@[simp] lemma axisVolume_append (a : ι → ℕ) (xs ys : List ι) :
    axisVolume a (xs ++ ys) = axisVolume a xs * axisVolume a ys := by
  simp [axisVolume]

@[simp] lemma axisVolume_flatten (a : ι → ℕ) (gs : List (List ι)) :
    axisVolume a gs.flatten = (gs.map (axisVolume a)).prod := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [ih]

/-- Large axes, full groups of small axes, and the final possibly empty small group. -/
structure GridPartition (a : ι → ℕ) (N : ℕ) (xs : List ι) where
  large : List ι
  full : List (List ι)
  rest : List ι
  covers : (large ++ (rest ++ full.flatten)).Perm xs
  large_spec : ∀ i ∈ large, N < a i ^ 24
  small_spec : ∀ i ∈ rest ++ full.flatten, a i ^ 24 ≤ N
  full_lower : ∀ g ∈ full, N ≤ axisVolume a g ^ 24
  full_upper : ∀ g ∈ full, axisVolume a g ^ 12 ≤ N
  rest_lt : axisVolume a rest ^ 24 < N

/-- Greedily add a small axis to the current group and close it as soon as it
reaches `N^(1/24)`. -/
theorem exists_gridPartition (a : ι → ℕ) {N : ℕ} (hN : 1 < N) (xs : List ι) :
    Nonempty (GridPartition a N xs) := by
  induction xs with
  | nil =>
    exact ⟨⟨[], [], [], by simp, by simp, by simp, by simp, by simp, by simpa using hN⟩⟩
  | cons x xs ih =>
    obtain ⟨w⟩ := ih
    by_cases hx : N < a x ^ 24
    · exact ⟨⟨x :: w.large, w.full, w.rest, w.covers.cons x, by
        simpa using And.intro hx w.large_spec, w.small_spec, w.full_lower, w.full_upper, w.rest_lt⟩⟩
    have hperm := (List.perm_middle (a := x) (l₁ := w.large)
      (l₂ := w.rest ++ w.full.flatten)).trans (w.covers.cons x)
    have hsmall (i) (hi : i ∈ x :: w.rest ++ w.full.flatten) : a i ^ 24 ≤ N := by
      rcases List.mem_cons.mp hi with rfl | hi
      · exact le_of_not_gt hx
      · exact w.small_spec i hi
    by_cases hfull : N ≤ axisVolume a (x :: w.rest) ^ 24
    · have hupper : axisVolume a (x :: w.rest) ^ 12 ≤ N := by
        apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
        rw [← pow_mul, axisVolume_cons, mul_pow]
        simpa only [show 12 * 2 = 24 by decide, pow_two] using
          Nat.mul_le_mul (le_of_not_gt hx) w.rest_lt.le
      refine ⟨⟨w.large, (x :: w.rest) :: w.full, [], ?_, w.large_spec, ?_, ?_, ?_, by simpa using hN⟩⟩
      · simpa using hperm
      · simpa using hsmall
      · simpa using And.intro hfull w.full_lower
      · simpa using And.intro hupper w.full_upper
    · exact ⟨⟨w.large, w.full, x :: w.rest, hperm, w.large_spec, hsmall, w.full_lower,
        w.full_upper, lt_of_not_ge hfull⟩⟩

namespace GridPartition

variable {a : ι → ℕ} {N : ℕ} {xs : List ι} (w : GridPartition a N xs)

/-- The incomplete group's volume also fits the extension-capacity bound. -/
theorem rest_upper : axisVolume a w.rest ^ 12 ≤ N := by
  apply le_trans _ w.rest_lt.le
  rw [show 24 = 12 * 2 by decide, pow_mul]
  exact Nat.le_pow (by decide : 0 < 2)

private theorem pow_length_le_prod {l : List ℕ} (h : ∀ b ∈ l, N ≤ b ^ 24) :
    N ^ l.length ≤ l.prod ^ 24 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.length_cons, List.prod_cons, mul_pow]
    rw [pow_succ' N l.length]
    exact Nat.mul_le_mul (h b (.head _)) (ih (fun x hx ↦ h x (.tail _ hx)))

/-- Counting the full groups and the large axes together gives at most 24.
Adding the (possibly empty) final group gives at most 25 calls. -/
theorem length_le (hN : 1 < N) (hvol : axisVolume a xs = N) :
    w.large.length + w.full.length ≤ 24 := by
  let sizes := w.large.map a ++ w.full.map (axisVolume a)
  have hs (b : ℕ) (hb : b ∈ sizes) : N ≤ b ^ 24 := by
    rcases List.mem_append.mp hb with hl | hf
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
      exact (w.large_spec i hi).le
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact w.full_lower g hg
  have hv : sizes.prod * axisVolume a w.rest = N := by
    have hp := (w.covers.map a).prod_eq
    change axisVolume a _ = axisVolume a xs at hp
    rw [hvol, axisVolume_append, axisVolume_append, axisVolume_flatten] at hp
    simpa [sizes, axisVolume, mul_assoc, mul_left_comm, mul_comm] using hp
  have hle : sizes.prod ≤ N := Nat.le_of_dvd (by omega) ⟨_, hv.symm⟩
  have hh := (Nat.pow_le_pow_iff_right hN).mp <|
    (pow_length_le_prod hs).trans (Nat.pow_le_pow_left hle 24)
  simpa [sizes] using hh

/-- If each large-axis call and each group call costs at most `C` gates, their
total cost is at most `25*C`, independent of the number of axes. -/
theorem sum_cost_le (hN : 1 < N) (hvol : axisVolume a xs = N) {C : ℕ}
    (largeCost : ι → ℕ) (groupCost : List ι → ℕ)
    (hlarge : ∀ i ∈ w.large, largeCost i ≤ C)
    (hfull : ∀ g ∈ w.full, groupCost g ≤ C) (hrest : groupCost w.rest ≤ C) :
    (w.large.map largeCost).sum + (w.full.map groupCost).sum + groupCost w.rest ≤ 25 * C := by
  have h₁ := List.sum_le_sum hlarge
  have h₂ := List.sum_le_sum hfull
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul] at h₁ h₂
  calc
    _ ≤ w.large.length * C + w.full.length * C + C :=
      Nat.add_le_add (Nat.add_le_add h₁ h₂) hrest
    _ = (w.large.length + w.full.length + 1) * C := by ring
    _ ≤ _ := Nat.mul_le_mul_right C (by have := w.length_le hN hvol; omega)

end GridPartition

end FiniteFourier
end LinearAlgebra
end OAI
