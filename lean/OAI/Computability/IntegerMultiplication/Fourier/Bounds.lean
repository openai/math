import OAI.Computability.IntegerMultiplication.Fourier.Line

/-! Pointwise ("max") norms, often without the need to pack together maxima. -/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open Finset
def Bound {X : Type*} (f : X → ℂ) (B : ℝ) : Prop :=
  ∀ i, ‖f i‖ ≤ B

def Gap {X : Type*} (f g : X → ℂ) (E : ℝ) : Prop :=
  ∀ i, ‖f i - g i‖ ≤ E

section Bound
variable {X Y : Type*} {f g u v : X → ℂ} {B C : ℝ}

theorem Bound.diff (hf : Bound f B) (hh : Bound g C) : Gap f g (B+C) :=
  fun i => (norm_sub_le ..).trans (add_le_add (hf i) (hh i))

theorem Bound.add (hf : Bound f B) (hg : Bound g C) : Bound (f+g) (B+C) :=
  fun i => (norm_add_le ..).trans (add_le_add (hf i) (hg i))

theorem Bound.of_gap (hg : Bound g C) (e : Gap f g B) : Bound f (B+C) := by
  intro i
  rw [show f i=f i-g i+g i by ring]
  exact (norm_add_le ..).trans (add_le_add (e i) (hg i))

theorem Gap.mono (h : Gap f g B) (e : B ≤ C) : Gap f g C := fun i => (h i).trans e
theorem Bound.mono (h : Bound f B) (e : B ≤ C) : Bound f C := fun i => (h i).trans e
theorem Gap.symm (h : Gap f g B) : Gap g f B := fun i => by rw [norm_sub_rev]; exact h i
theorem Gap.refl (f : X → ℂ) : Gap f f 0 := by simp [Gap]
theorem Gap.trans (h : Gap f g B) (e : Gap g u C) : Gap f u (B+C) := by
  intro i
  rw [show f i-u i=(f i-g i)+(g i-u i) by ring]
  exact (norm_add_le ..).trans (add_le_add (h i) (e i))
theorem Gap.add (h : Gap f g B) (e : Gap u v C) : Gap (f+u) (g+v) (B+C) := by
  intro i
  rw [Pi.add_apply,Pi.add_apply,show f i+u i-(g i+v i)=f i-g i+(u i-v i) by ring]
  exact (norm_add_le ..).trans (add_le_add (h i) (e i))

-- summing weighted applications (not necessarily injective index map)
theorem Bound.weight {w : Y → ℂ} {s : Finset Y} (e : Bound f B) (hb : 0 ≤ B)
    (h : ∑ i ∈ s, ‖w i‖ ≤ C) (j : Y → X) :
    ‖∑ i ∈ s, w i * f (j i)‖ ≤ C * B :=
  (norm_sum_le_of_le s (f := fun i => w i*f (j i)) (n := fun i => ‖w i‖*B) (fun i _ => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (e _) (norm_nonneg _))).trans <|
    (by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right h hb)

theorem Gap.of_weight {w : Y → ℂ} {s : Finset Y} (e : Gap f g B) (hb : 0 ≤ B)
    (h : ∑ i ∈ s, ‖w i‖ ≤ C) (j : Y → X) :
    ‖(∑ i ∈ s, w i*f (j i))-(∑ i ∈ s, w i*g (j i))‖≤ C*B := by
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  exact Bound.weight (f := fun x => f x - g x) e hb h j

end Bound

variable {n : ℕ} {B : ℝ} {f g : Arr n ℂ}

theorem dft_bound (q : ℤ) (h : Bound f B) :
    Bound (dft n q f) (n*B) := by
  intro i
  unfold dft
  calc
    _ ≤ ∑ _j : Spot n, B := norm_sum_le_of_le _ (fun j _ => by simp [h j])
    _ = _ := by simp

theorem dft_gap (q : ℤ) (h : Gap f g B) :
    Gap (dft n q f) (dft n q g) (n*B) := by
  have e := dft_bound q (f := fun x => f x-g x) h
  intro i
  unfold dft
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  exact e i

end Fourier

end IntegerMultiplication
end Computability
end OAI
