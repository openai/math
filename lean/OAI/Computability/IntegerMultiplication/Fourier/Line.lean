import OAI.Computability.IntegerMultiplication.Fourier.Window
import Mathlib.Tactic

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open scoped BigOperators
open Finset

/- We use *unnormalized*, negative-sign transforms, but allow an integer frequency factor
q, so the opposite transform is available too. -/
noncomputable def dft (n : ℕ) (q : ℤ) (f : Arr n ℂ) (x : Spot n) : ℂ :=
  ∑ j : Spot n, phase n (-q*rep x*rep j) * f j

/-- expansion, with a full finite window. -/
noncomputable def grow (s t : ℕ) (D : ℕ) (f : Arr s ℂ) (k : Spot t) : ℂ :=
  ∑ j : Spot s, (window D (s*t) ((t : ℤ)*rep j-(s:ℤ)*rep k) : ℂ)*f j

variable {s t : ℕ} [NeZero s] [NeZero t]

private theorem phase_pull (b : ℤ) (j : Spot s) (k : Spot t) :
    phase (s*t) (b*((t:ℤ)*rep j-(s:ℤ)*rep k)) =
      phase s (b*rep j)*phase t (-(b*rep k)) := by
  have hs : (s:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne s)
  have ht : (t:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  unfold phase
  rw [← cis_add]
  congr 1
  push_cast
  field_simp; ring

-- Compute the inner sum over target k when extracting one frequency.
private theorem k_sum (b : ℤ) (x : Spot t) (j : Spot s) :
    ∑ k : Spot t, (phase t ((s:ℤ)*rep x*rep k) * phase (s*t) (b*((t:ℤ)*rep j-(s:ℤ)*rep k))) =
      if (t:ℤ) ∣ (s:ℤ)*rep x-b
      then (t:ℂ)*phase s (b*rep j) else 0 := by
  have e (k : Spot t) : phase t ((s:ℤ)*rep x*rep k) *
      phase (s*t) (b*((t:ℤ)*rep j-(s:ℤ)*rep k)) =
        phase s (b*rep j) * phase t (((s:ℤ)*rep x-b)*rep k) := by
    rw [phase_pull b j k,sub_mul,sub_eq_add_neg,phase_add]
    ring
  simp_rw [e, ← mul_sum]
  change _ * (∑ k : Fin t, phase t (_ * (k.val : ℕ))) = _
  rw [sum_phase]
  split <;> ring

omit [NeZero t] in
/-- Coefficient switches at wrap. Uses no coprimality yet. -/
private theorem j_sum {b z : ℤ} {x : Spot t} (e : b=(s:ℤ)*rep x-(t:ℤ)*z)
    (f : Arr s ℂ) :
    (∑ j : Spot s, phase s (b*rep j) * f j) = dft s t f (wrap s z) := by
  unfold dft
  apply sum_congr rfl
  intro j _
  rw [e, sub_mul, sub_eq_add_neg, phase_add]
  have eh : phase s ((s:ℤ) * rep x * rep j)=1 := by
    rw [phase_eq_one,mul_assoc]
    exact dvd_mul_right _ _
  rw [eh,one_mul]
  congr 1
  apply phase_congr
  have hh := wrap_mul s z (-((t:ℤ)*rep j))
  rw [show -(↑t * z * rep j) = z * -(↑t * rep j) by ring,
      show -(t:ℤ) * rep (wrap s z) * rep j = rep (wrap s z) * -(↑t * rep j) by ring,
      hh]

/-- Direct identity indexed by binomial offsets b. No sign-chirps or synthetic-ring
normalizations are hidden in it. -/
theorem grow_dft (D : ℕ) (f : Arr s ℂ) (x : Spot t) :
    dft t (-(s:ℤ)) (grow s t D f) x =
      ∑ b ∈ (rad D).filter (fun b => (t:ℤ)∣(s:ℤ)*rep x-b),
        (t:ℂ) * (coef D b : ℂ) * dft s t f (wrap s (((s:ℤ)*rep x-b)/t)) := by
  unfold dft grow
  simp_rw [neg_neg, mul_sum, window_phase, sum_mul, mul_sum]
  -- shape of circulations
  rw [sum_comm]
  -- lhs order j,k,r; want r,j,k
  simp_rw [sum_comm (s := (@univ (Spot t) _)) (t := rad D)]
  rw [sum_comm (s := (@univ (Spot s) _)) (t := rad D)]
  rw [sum_filter]
  apply sum_congr rfl
  intro b _
  conv_lhs =>
    arg 2; ext j; arg 2; ext k
    rw [show phase t ((s:ℤ)*rep x*rep k)
      * ((coef D b : ℂ)*phase (s*t) (b*((t:ℤ)*rep j-(s:ℤ)*rep k))*f j) =
      ((phase t ((s:ℤ)*rep x*rep k)*phase (s*t) (b*((t:ℤ)*rep j-(s:ℤ)*rep k)))
         * ((coef D b : ℂ)*f j)) by ring]
  simp_rw [← sum_mul, k_sum]
  split
  · next h =>
--    simp only [h, ↓reduceIte]
    let z := ((s:ℤ)*rep x-b)/t
    have he := Int.ediv_mul_cancel h
    have e : b=(s:ℤ)*rep x - (t:ℤ)*z := by unfold z; rw [mul_comm (t:ℤ), he]; ring
    rw [← mul_sum]
    change (∑ j : Spot s, _) =
      (t:ℂ)*_ * dft s t f (wrap s z)
    rw [← j_sum e, mul_sum]
    apply sum_congr rfl
    intros
    ring
  · next h => simp

/-- The selected-line form: when a row y is supplied with any k near t*y/s
(within D/s, here), its mixing is a short finite matrix indexed by shifts off y.
D/s is generally large; quantitative estimates will ask for the nearer threshold. -/
theorem selected_grow_dft (D : ℕ) (f : Arr s ℂ) (x : Spot t) (y : Spot s) (δ : ℤ)
    (hx : (s:ℤ)*rep x=(t:ℤ)*rep y+δ)
    (hb : δ∈rad D) :
    dft t (-(s:ℤ)) (grow s t D f) x =
      ∑ l ∈ rad (2*D),
        (t:ℂ) * (coef D (δ - (t:ℤ)*l) : ℂ) * dft s t f (wrap s (rep y+l)) := by
  let U := (rad (2*D)).filter (fun l => δ-(t:ℤ)*l ∈ rad D)
  let V := (rad D).filter (fun b => (t:ℤ) ∣ (s:ℤ)*rep x-b)
  let wp (b : ℤ) (z : Spot s) := (t:ℂ) * (coef D b : ℂ) * dft s t f z
  rw [grow_dft]
  have he : (∑ l ∈ U, wp (δ-(t:ℤ)*l) (wrap s (rep y+l))) =
      ∑ l ∈ rad (2*D), wp (δ-(t:ℤ)*l) (wrap s (rep y+l)) := by
    simp only [U,sum_filter]
    apply sum_congr rfl
    intro l _
    split
    · rfl
    · next h => simp only [wp,coef,ite_eq_right h,Complex.ofReal_zero,mul_zero,zero_mul]
  change (∑ b ∈ V, wp b _) = (∑ l ∈ rad (2*D), wp _ _)
  rw [← he]
  symm
  have ht : (0:ℤ)<t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  apply sum_bij (fun l _ => δ-(t:ℤ)*l)
  · intro l hl
    simp only [U, mem_filter] at hl
    have eq : (s:ℤ)*rep x-(δ-(t:ℤ)*l)=(t:ℤ)*(rep y+l) := by rw [hx]; ring
    simp [V, -mem_rad, hl.2,eq]
  · intro l _ j _ h
    apply mul_left_cancel₀ ht.ne'
    linarith
  · intro b hb'
    simp only [V, mem_filter] at hb'
    have h : (t:ℤ) ∣ δ-b := by
      obtain ⟨z,hz⟩ := hb'.2
      use z-rep y
      rw [mul_sub,← hz,hx]
      ring
    obtain ⟨l,hl⟩ := h
    have bq : δ-(t:ℤ)*l=b := by linarith
    have hm : l ∈ rad (2*D) := by
      have e := mem_rad.mp hb'.1
      have g := mem_rad.mp hb
      rw [mem_rad]
      push_cast
      constructor <;> nlinarith
    exact ⟨l,mem_filter.mpr ⟨hm,bq.symm ▸ hb'.1⟩,bq⟩
  · intro l _
    dsimp only [wp]
    rw [hx, show (t:ℤ)*rep y+δ-(δ- (t:ℤ)*l) = (t:ℤ)*(rep y+l) by ring,
      Int.mul_ediv_cancel_left _ ht.ne']

end Fourier

end IntegerMultiplication
end Computability
end OAI
