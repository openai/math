import OAI.Computability.IntegerMultiplication.Fourier.Nearest
import OAI.Computability.IntegerMultiplication.Fourier.Bounds
import OAI.Computability.IntegerMultiplication.Fourier.Residual

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open Finset Real

variable {s t : ℕ} [NeZero s] [NeZero t]

def nextSample (k : Spot t) (l : ℤ) : Spot s :=
  wrap s ((floorSample s t k : ℤ)+l)

noncomputable def win (D : ℕ) (k : Spot t) (j : Spot s) : ℂ :=
  (window D (s*t) ((t : ℤ)*rep j-(s:ℤ)*rep k) : ℂ)

noncomputable def sample (s t : ℕ) [NeZero s] (D L : ℕ) (f : Arr s ℂ) (k : Spot t) : ℂ :=
  ∑ l ∈ rad L, win D k (nextSample k l : Spot s)*f (nextSample k l)
-- fix typo

omit [NeZero s] [NeZero t] in
@[simp]
theorem win_bound (D : ℕ) (k : Spot t) (j : Spot s) :
    ‖win D k j‖ ≤ 1 := by simpa [win] using window_abs_le D (s*t) ((t : ℤ)*rep j-(s:ℤ)*rep k)

omit [NeZero t] in
theorem gather {D L : ℕ} (h : 2*L<s) (f : Arr s ℂ) (k : Spot t) :
    sample s t D L f k =
    ∑ j ∈ around s L (floorSample s t k), win D k j * f j := by
  rw [around, sum_image (inj_near s _ h)]
  rfl

omit [NeZero s] [NeZero t] in
theorem grow_bound {B : ℝ} (D : ℕ) {f : Arr s ℂ} (h : Bound f B) (e : 0≤B) :
    Bound (grow s t D f) (s*B) := by
  intro k
  apply Bound.weight h e (s := (@univ (Spot s) _)) (w := win D k) (B:=B) (C:=s) _ id
  convert sum_le_sum (fun j (_ : j∈ (@univ (Spot s) _)) => win_bound D k j) using 1
  · simp [Spot]

omit [NeZero t] in
theorem sample_bound {B : ℝ} (D L : ℕ) {f : Arr s ℂ} (h : Bound f B) (e : 0≤B) :
    Bound (sample s t D L f) ((2*L+1:ℝ)*B) := by
  intro k
  apply Bound.weight h e (s := rad L) (w := fun i => win D k (nextSample k i : Spot s))
    (B:=B) (C:=2*L+1) _ _
  convert sum_le_sum (fun j (_ : j∈rad L) => win_bound D k (nextSample k j : Spot s)) using 1
  · simp [rad_card]

theorem sample_gap_grow (D L : ℕ) (hsize : 2*L<s) {f : Arr s ℂ}
    {B : ℝ} (h : Bound f B) (e : 0≤B) :
    Gap (sample s t D L f) (grow s t D f) ((s:ℝ)*Real.exp (-(4:ℝ)*D*(L:ℕ)^2/(s:ℕ)^2)*B) := by
  apply Gap.symm
  intro k
  let y : ℤ := floorSample s t k
  let R₀ := around s L y
  let S := (@univ (Spot s) _) \ R₀
  have hh := sum_sdiff (subset_univ R₀) (f := fun j : Spot s => win D k j * f j)
  rw [gather hsize]
  change ‖(∑ j : Spot s, win D k j*f j)-(∑ j ∈ R₀, win D k j * f j)‖ ≤ _
  rw [← hh,add_sub_cancel_right]
  apply Bound.weight (s := S) (w := win D k) (j := id) h e
  -- tails small: center floor
  obtain ⟨δ,hy,hδ⟩ := floor_spec s t k
  let X := Real.exp (-(4:ℝ)*D*(L:ℕ)^2/(s:ℕ)^2)
  have h := sum_le_sum (g := fun _ => X) fun j (hj : j∈S) =>
    show ‖win D k (j:Spot s)‖≤X from by
      simpa [win,X] using extreme D L j k y δ hy hδ (Finset.mem_sdiff.mp hj).2
  simp only [sum_const, nsmul_eq_mul] at h
  have b : S.card ≤ s := by
    calc
      _ ≤ Fintype.card (Spot s) := card_le_univ _
      _ = _ := Fintype.card_fin s
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast b) (Real.exp_pos _).le)

omit [NeZero t] in
theorem sample_gap {B : ℝ} (D L : ℕ) {f g : Arr s ℂ} (h : Gap f g B) (e : 0≤B) :
    Gap (sample s t D L f) (sample s t D L g) ((2*L+1:ℝ)*B) := by
  intro k
  simp only [sample,← sum_sub_distrib, ← mul_sub]
  exact sample_bound (t:=t) D L (f := fun x => f x-g x) h e k

end Fourier

end IntegerMultiplication
end Computability
end OAI
