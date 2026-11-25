import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Matching direction bins in a shortening epoch

In Lemma 6.1, page 19, the permutations of bin addresses preserve segment length.
At seed `b` we use the smallest width among the bins `A j b`. Integer pooling
divides each count by the number of directions, then groups the resulting pool
into blocks of the given width. The estimates here include both losses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Finset

variable {ι β : Type*} [Fintype ι] [Nonempty ι] [Fintype β]

/-- The smallest count among the directions of one seed bin. -/
noncomputable def leastCount {R : Type*} [LinearOrder R] (f : ι → R) : R :=
  (univ.image f).min' (univ_nonempty.image f)

private theorem leastCount_le {R : Type*} [LinearOrder R] (f : ι → R) (i : ι) :
    leastCount f ≤ f i :=
  min'_le _ _ (mem_image_of_mem _ (mem_univ i))

private theorem leastCount_attained {R : Type*} [LinearOrder R] (f : ι → R) :
    ∃ i, f i = leastCount f := by
  classical
  obtain ⟨i, _, hi⟩ := mem_image.mp (min'_mem _ (univ_nonempty.image f))
  exact ⟨i, hi⟩

private theorem leastCount_comp {R S : Type*} [LinearOrder R] [LinearOrder S]
    (f : ι → R) {g : R → S} (hg : Monotone g) :
    leastCount (g ∘ f) = g (leastCount f) := by
  obtain ⟨i, hi⟩ := leastCount_attained f
  obtain ⟨j, hj⟩ := leastCount_attained (g ∘ f)
  apply le_antisymm
  · simpa [Function.comp_apply, hi] using leastCount_le (g ∘ f) i
  · rw [← hj]
    exact hg (leastCount_le f j)

private theorem leastCount_sub_le (x y : ι → ℝ) :
    leastCount x - leastCount y ≤ ∑ i, |x i - y i| := by
  obtain ⟨j, hj⟩ := leastCount_attained y
  calc
    leastCount x - leastCount y ≤ x j - y j := by rw [← hj]; gcongr; exact leastCount_le _ _
    _ ≤ |x j - y j| := le_abs_self _
    _ ≤ ∑ i, |x i - y i| := single_le_sum (fun i _ => abs_nonneg (x i - y i)) (mem_univ j)

/-- The matched length before rounding. Dividing every bin into pools cancels
the number of matched directions at each seed. -/
noncomputable def matchedLength (A : ι → Equiv.Perm β) (length x : β → ℝ) : ℝ :=
  ∑ b, length b * leastCount (fun j => x (A j b))

/-- Dividing the combined counts by the number of packs divides the matched length
by the same factor. -/
theorem matchedLength_div (A : ι → Equiv.Perm β) (length x : β → ℝ) {K : ℝ} (hK : 0 ≤ K) :
    matchedLength A length (fun b => x b / K) = matchedLength A length x / K := by
  unfold matchedLength
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro b _
  rw [mul_div_assoc]
  congr 1
  exact leastCount_comp (fun j => x (A j b)) (g := fun r => r / K)
    (fun _ _ h => div_le_div_of_nonneg_right h hK)

/-- For invariant ideal counts the whole mean length is matched. -/
theorem matchedLength_invariant (A : ι → Equiv.Perm β) (length x : β → ℝ)
    (hx : ∀ j b, x (A j b) = x b) :
    matchedLength A length x = ∑ b, length b * x b := by
  apply sum_congr rfl
  intro b _
  obtain ⟨j, hj⟩ := leastCount_attained (fun j => x (A j b))
  rw [← hj, hx]

/-- The weighted Lipschitz estimate used to pass from ideal to actual motions. -/
theorem matchedLength_lipschitz (A : ι → Equiv.Perm β) (length x y : β → ℝ)
    (hpos : ∀ b, 0 ≤ length b) (hpres : ∀ j b, length (A j b) = length b) :
    |matchedLength A length x - matchedLength A length y| ≤
      Fintype.card ι * ∑ b, length b * |x b - y b| := by
  classical
  have hmin (b : β) :
      |leastCount (fun j => x (A j b)) - leastCount (fun j => y (A j b))| ≤
        ∑ j, |x (A j b) - y (A j b)| := by
    rw [abs_le]
    constructor
    · have h := leastCount_sub_le (fun j => y (A j b)) (fun j => x (A j b))
      simp_rw [abs_sub_comm (y _) (x _)] at h
      linarith
    · exact leastCount_sub_le _ _
  unfold matchedLength
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ b, |length b * leastCount (fun j => x (A j b)) -
        length b * leastCount (fun j => y (A j b))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, length b * ∑ j, |x (A j b) - y (A j b)| := by
      apply sum_le_sum
      intro b _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hpos b)]
      exact mul_le_mul_of_nonneg_left (hmin b) (hpos b)
    _ = ∑ j, ∑ b, length (A j b) * |x (A j b) - y (A j b)| := by
      simp_rw [mul_sum, hpres]
      rw [sum_comm]
    _ = _ := by
      simp_rw [Equiv.sum_comp (A _) (fun b => length b * |x b - y b|)]
      simp

/-- A half-length lower bound for an actual mean near the invariant ideal mean. -/
theorem half_length_le_matchedLength (A : ι → Equiv.Perm β) (length actual ideal : β → ℝ)
    (hpos : ∀ b, 0 ≤ length b) (hpres : ∀ j b, length (A j b) = length b)
    (hinv : ∀ j b, ideal (A j b) = ideal b)
    (herr : Fintype.card ι * ∑ b, length b * |actual b - ideal b| ≤
      (∑ b, length b * ideal b) / 2) :
    (∑ b, length b * ideal b) / 2 ≤ matchedLength A length actual := by
  have h := matchedLength_lipschitz A length actual ideal hpos hpres
  rw [matchedLength_invariant A length ideal hinv, abs_le] at h
  linarith [h.1]

/-- Matched bits at a seed after forming the direction pools and rounding the
common pool down to a whole number of width-`m` blocks. -/
noncomputable def pooledBits (m : ℕ) (x : ι → ℕ) : ℕ :=
  Fintype.card ι * (m * (leastCount (fun j => x j / Fintype.card ι) / m))

/-- The exact loss from pooling and block rounding is a single remainder. -/
theorem pooledBits_add_mod (m : ℕ) (x : ι → ℕ) :
    pooledBits m x + leastCount x % (Fintype.card ι * m) = leastCount x := by
  let d := Fintype.card ι
  have hdiv : leastCount (fun j => x j / d) = leastCount x / d :=
    leastCount_comp x (g := fun n => n / d) (fun _ _ h => Nat.div_le_div_right h)
  change d * (m * (leastCount (fun j => x j / d) / m)) + _ = _
  rw [hdiv, Nat.div_div_eq_div_mul, ← Nat.mul_assoc, Nat.mul_comm, Nat.div_add_mod']

/-- The total weighted loss is at most one `D * m` block per seed address. -/
theorem pooledLength_loss_le (A : ι → Equiv.Perm β) (length : β → ℝ)
    (counts : β → ℕ) {m : ℕ} (hm : 0 < m) (hpos : ∀ b, 0 ≤ length b) :
    matchedLength A length (fun b => counts b) -
        ∑ b, length b * pooledBits m (fun j => counts (A j b)) ≤
      ∑ b, length b * (Fintype.card ι * m : ℕ) := by
  unfold matchedLength
  rw [← sum_sub_distrib]
  apply sum_le_sum
  intro b _
  rw [← mul_sub]
  apply mul_le_mul_of_nonneg_left _ (hpos b)
  let x : ι → ℕ := fun j => counts (A j b)
  have hmin : leastCount (fun j => (x j : ℝ)) = ((leastCount x : ℕ) : ℝ) :=
    leastCount_comp x (g := fun n => (n : ℝ)) (fun _ _ h => Nat.cast_le.mpr h)
  change leastCount (fun j => (x j : ℝ)) - (pooledBits m x : ℝ) ≤ _
  rw [hmin, sub_le_iff_le_add]
  have h := pooledBits_add_mod m x
  have hr := Nat.mod_lt (leastCount x) (Nat.mul_pos (Fintype.card_pos (α := ι)) hm)
  exact_mod_cast (show leastCount x ≤ Fintype.card ι * m + pooledBits m x by omega)

end Epoch

end BorderVNP
end Computability
end OAI
