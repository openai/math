import OAI.Computability.NearSquareRoot.ChirpIncrement
import OAI.Computability.NearSquareRoot.ChirpPartition
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Cancellation on a nonstationary run of a quadratic chirp

After scaling the phase by one full turn, the reciprocals of successive
phase differences lie on one vertical line. Their imaginary parts increase
along each run, so summation by parts costs just four endpoint moduli.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Chirp

open Finset

private theorem weightedDiff (u w : ℕ → ℂ) (n : ℕ) :
    ∑ i ∈ range (n + 1), (u i - u (i + 1)) * w i =
      u 0 * w 0 - u (n + 1) * w n +
      ∑ i ∈ range n, u (i + 1) * (w (i + 1) - w i) := by
  induction n with
  | zero => simp [sub_mul]
  | succ n ih =>
    rw [sum_range_succ _ (n+1), ih, sum_range_succ _ n]
    ring

/-- The bounded-variation estimate used on each closed arc avoiding phase one.
The difference equation is required up to the last term, so the estimate
charges both boundary terms of the finite sum. -/
theorem norm_sum_run_le {u w : ℕ → ℂ} {n : ℕ} {B : ℝ}
    (hu : ∀ i ≤ n+1, ‖u i‖ = 1)
    (hdiff : ∀ i ≤ n, u i = (u i - u (i+1)) * w i)
    (hre : ∀ i < n, (w (i+1)).re = (w i).re)
    (him : ∀ i < n, (w i).im ≤ (w (i+1)).im)
    (h₀ : ‖w 0‖ ≤ B) (hn : ‖w n‖ ≤ B) :
    ‖∑ i ∈ range (n+1), u i‖ ≤ 4 * B := by
  have sum_eq : (∑ i ∈ range (n+1), u i) =
      ∑ i ∈ range (n+1), (u i - u (i+1)) * w i :=
    sum_congr rfl fun i hi => hdiff i (by simpa using hi)
  have variation : ∀ i ∈ range n,
      ‖u (i+1) * (w (i+1) - w i)‖ = (w (i+1)).im - (w i).im := by
    intro i hi
    have hi' := mem_range.mp hi
    rw [norm_mul, hu _ (by omega), one_mul,
      ← Complex.abs_im_eq_norm.mpr (by simp [hre _ hi'] : (w (i+1) - w i).re = 0),
      Complex.sub_im, abs_of_nonneg (sub_nonneg.mpr (him i hi'))]
  have he : (w n).im ≤ B := (Complex.im_le_norm _).trans hn
  have hs : -(w 0).im ≤ B := (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans h₀)
  rw [sum_eq, weightedDiff]
  calc
    _ ≤ ‖u 0 * w 0 - u (n+1) * w n‖ + ‖∑ i ∈ range n, u (i+1) * (w (i+1) - w i)‖ := norm_add_le ..
    _ ≤ (‖u 0 * w 0‖ + ‖u (n+1) * w n‖) + ∑ i ∈ range n, ‖u (i+1) * (w (i+1) - w i)‖ :=
      add_le_add (norm_sub_le ..) (norm_sum_le ..)
    _ = ‖w 0‖ + ‖w n‖ + ((w n).im - (w 0).im) := by
      rw [norm_mul, norm_mul, hu _ (by omega), hu _ (by omega), one_mul, one_mul,
        sum_congr rfl variation, sum_range_sub (fun i => (w i).im)]
    _ ≤ _ := by linarith

/-- A good frequency arc contributes at most `1/δ`, independently of its length. -/
theorem norm_sum_on_arc {a : ℕ} (ha : 0 < a) {β δ : ℝ} (hδ : 0 < δ)
    (u : ℕ → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (hsucc : ∀ i, u (i+1) = u i * phase (β - (i : ℝ)/a))
    (j : ℤ) (l r : ℕ)
    (harc : ∀ i ∈ Ico l r, (j : ℝ)+δ ≤ β - (i : ℝ)/a ∧ β - (i : ℝ)/a ≤ j+1-δ) :
    ‖∑ i ∈ Ico l r, u i‖ ≤ 1/δ := by
  let t (i : ℕ) : ℝ := β - ((l+i : ℕ) : ℝ) / a - j
  rw [sum_Ico_eq_sum_range]
  generalize hn : r - l = m
  cases m with
  | zero => simp [one_div, hδ.le]
  | succ n =>
    have ht (i : ℕ) (hi : i ≤ n) : t i ∈ Set.Icc δ (1 - δ) := by
      obtain ⟨hli, hri⟩ := harc (l+i) (mem_Ico.mpr ⟨by omega, by omega⟩)
      dsimp [t]
      constructor <;> linarith
    have ht' (i : ℕ) (hi : i ≤ n) : t i ∈ Set.Ioo (0 : ℝ) 1 := by
      obtain ⟨hli,hri⟩ := ht i hi
      exact ⟨by linarith, by linarith⟩
    have hstep (i : ℕ) : u (l+(i+1)) = u (l+i) * phase (t i) := by
      rw [← Nat.add_assoc, hsucc]
      have hp := phase_periodic.sub_int_mul_eq (x := β - ((l+i : ℕ) : ℝ)/a) j
      rw [mul_one] at hp
      rw [hp]
    have hB := norm_sum_run_le (n := n) (u := fun i => u (l+i)) (w := fun i => weight (t i))
      (B := 1/(4*δ)) (fun i _ => hu _) (fun i hi => by
        rw [hstep, ← mul_one_sub, weight]
        field_simp [sub_ne_zero.mpr (phase_ne_one (ht' i hi)).symm])
      (fun i hi => by
        rw [weight_re (ht' _ (by omega)), weight_re (ht' _ (by omega))])
      (fun i hi => by
        apply weight_im_antitone (ht' _ (by omega)) (ht' _ (by omega))
        dsimp [t]
        push_cast
        have ha' : (0 : ℝ) < a := by exact_mod_cast ha
        have h := div_le_div_of_nonneg_right (show (l : ℝ) + i ≤ l + (i+1 : ℝ) by linarith) ha'.le
        linarith)
      (norm_weight_le hδ (ht 0 (by omega))) (norm_weight_le hδ (ht n le_rfl))
    exact hB.trans (by field_simp; rfl)

/-- Sample `exp(2πi(-h²/(2a)+b h))` at consecutive points `h = s+i`. -/
noncomputable def quadraticSamples (a : ℕ) (b s : ℝ) (i : ℕ) : ℂ :=
  phase (-((s+i)^2)/(2*a) + b*(s+i))

theorem quadraticSamples_succ (a : ℕ) (ha : 0 < a) (b s : ℝ) (i : ℕ) :
    quadraticSamples a b s (i+1) = quadraticSamples a b s i *
      phase ((b-(s+1/2)/a) - (i : ℝ)/a) := by
  unfold quadraticSamples
  rw [← phase_add]
  congr 1
  push_cast
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp
  ring

/-- Uniform incomplete quadratic exponential-sum estimate, for arbitrary real
linear frequency and any interval of at most `2a` consecutive samples. -/
theorem quadraticSamples_bound {a m : ℕ} (ha : 0 < a) (hm : m ≤ 2*a) (b s : ℝ) :
    ‖∑ i ∈ range m, quadraticSamples a b s i‖ ≤ 40 * Real.sqrt a := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  let δ := 1/(4 * Real.sqrt a)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hu (i : ℕ) : ‖quadraticSamples a b s i‖ = 1 := phase_norm _
  have H := partition_sum_bound a m ha hm (b-(s+1/2)/a) δ (1/δ) hδ.le
    (by positivity) (quadraticSamples a b s) (fun i _ => (hu i).le)
    (fun j l r _ => norm_sum_on_arc ha hδ _ hu (quadraticSamples_succ a ha b s) j l r)
  have hs : 1 ≤ Real.sqrt a := (Real.one_le_sqrt.mpr ha')
  have hs' : Real.sqrt a ≠ 0 := by linarith
  have he : (a : ℝ) = Real.sqrt a * Real.sqrt a := (Real.mul_self_sqrt (by positivity)).symm
  apply H.trans
  dsimp [δ]
  calc
    _ = 3 * (Real.sqrt a / 2 + 1 + 4 * Real.sqrt a) := by
      field_simp [hs']
      nlinarith [he]
    _ ≤ _ := by linarith

/-- The normalized Bluestein multiplier of the zero-extended chirp, evaluated
at a real frequency in turns per grid point. The paper uses `b = ξ/r`. -/
noncomputable def bluesteinMultiplier (a : ℕ) (b : ℝ) : ℂ :=
  (Real.sqrt a : ℂ)⁻¹ * ∑ h ∈ Ioo (-(a : ℤ)) (a : ℤ),
    phase (-((h : ℝ)^2)/(2*a) + b*h)

/-- All frequencies of the zero-extended chirp are uniformly bounded, including
the nonintegral frequencies of a larger padded Fourier transform. -/
theorem bluesteinMultiplier_bound {a : ℕ} (ha : 0 < a) (b : ℝ) :
    ‖bluesteinMultiplier a b‖ ≤ 40 := by
  have hsum : (∑ i ∈ range (2*a-1), quadraticSamples a b (1-(a : ℝ)) i) =
      ∑ h ∈ Ioo (-(a : ℤ)) (a : ℤ), phase (-((h : ℝ)^2)/(2*a) + b*h) := by
    refine sum_bij (fun i _ => (i : ℤ) + 1 - a) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [mem_range] at hi
      simp only [mem_Ioo]
      omega
    · intro i _ j _ hij
      omega
    · intro h hh
      simp only [mem_Ioo] at hh
      refine ⟨(h + a - 1).toNat, mem_range.mpr (by omega), by omega⟩
    · intro i _
      unfold quadraticSamples
      push_cast
      ring_nf
  have H := quadraticSamples_bound ha (show 2 * a - 1 ≤ 2*a by omega) b (1 - (a : ℝ))
  have hs : 0 < Real.sqrt a := by positivity
  rw [bluesteinMultiplier, ← hsum, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs, inv_mul_eq_div, div_le_iff₀ hs]
  exact H

/-- With `64` amplification rounds, all scalar dilations in the restored
transform lie in the disk of radius `1/2`. -/
theorem scaledMultiplier_lt_half {a : ℕ} (ha : 0 < a) (b : ℝ) :
    ‖bluesteinMultiplier a b * (Real.sin (Real.pi / (4*64+2)) : ℂ)‖ < 1/2 := by
  let θ : ℝ := Real.pi / (4*64+2)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ (by
    dsimp [θ]; linarith [Real.pi_pos])
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  calc
    _ ≤ 40 * θ := mul_le_mul (bluesteinMultiplier_bound ha b) (Real.sin_le hθ) hs (by norm_num)
    _ < _ := by dsimp [θ]; linarith [Real.pi_lt_d2]

end Chirp

end NearSquareRoot
end Computability
end OAI
