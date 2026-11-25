import OAI.LinearAlgebra.FiniteFourier.Cyclic
import OAI.LinearAlgebra.FiniteFourier.InverseComplexity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The logarithmic overhead exponent

Uniform estimates at every positive slack imply the exponent one half along
every sequence of orders tending to infinity. All logarithms here have base
two, including the inner logarithm of the double logarithm.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter
open scoped Topology

/-- The logarithmic overhead of a size bound at order N, as in the
Fourier complexity theorem. -/
noncomputable def logOverhead (N S : ℝ) : ℝ :=
  Real.logb 2 (S / N) / Real.logb 2 (Real.logb 2 N)

/-- Transfer the uniform lower and upper estimates to a limit of the overhead
exponent. The field, group, and circuit cost may all vary along the filter. -/
theorem tendsto_logOverhead_of_bounds {ι : Type*} {l : Filter ι} {N S : ι → ℝ}
    (hN : Tendsto N l atTop)
    (hlower : ∃ c > 0, ∀ᶠ i in l, c * N i * Real.sqrt (Real.logb 2 (N i)) ≤ S i)
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ C > 0, ∀ᶠ i in l,
      S i ≤ C * N i * (1 + Real.logb 2 (N i)) ^ ((1 : ℝ) / 2 + ε)) :
    Tendsto (fun i => logOverhead (N i) (S i)) l (𝓝 ((1 : ℝ) / 2)) := by
  let X (i : ι) := Real.logb 2 (N i)
  let Y (i : ι) := Real.logb 2 (X i)
  have hX : Tendsto X l atTop := (Real.tendsto_logb_atTop (by norm_num)).comp hN
  have hY : Tendsto Y l atTop := (Real.tendsto_logb_atTop (by norm_num)).comp hX
  obtain ⟨c, hc, hlow⟩ := hlower
  have hposN := hN.eventually_gt_atTop 0
  have hposX := hX.eventually_gt_atTop 1
  have hposY := hY.eventually_gt_atTop 0
  have hposS : ∀ᶠ i in l, 0 < S i / N i := by
    filter_upwards [hlow, hposN, hposX] with i hi hn hx
    exact div_pos ((mul_pos (mul_pos hc hn) (Real.sqrt_pos.mpr (by linarith : 0 < X i))).trans_le hi) hn
  have hL : ∀ᶠ i in l, Real.logb 2 c / Y i + (1 : ℝ) / 2 ≤ logOverhead (N i) (S i) := by
    filter_upwards [hlow, hposN, hposX, hposY] with i hi hn hx hy
    have hx' : 0 < X i := by linarith
    have hlo : c * Real.sqrt (X i) ≤ S i / N i := by
      apply (le_div_iff₀ hn).mpr
      linarith only [hi]
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (mul_pos hc (Real.sqrt_pos.mpr hx')) hlo
    rw [Real.logb_mul hc.ne' (Real.sqrt_pos.mpr hx').ne', Real.sqrt_eq_rpow,
      Real.logb_rpow_eq_mul_logb_of_pos hx'] at hlog
    change _ ≤ Real.logb 2 (S i / N i) / Y i
    apply (le_div_iff₀ hy).mpr
    rw [add_mul, div_mul_cancel₀ _ hy.ne']
    exact hlog
  refine tendsto_order.mpr ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hl : Tendsto (fun i => Real.logb 2 c / Y i + 1 / 2) l (𝓝 ((1 : ℝ) / 2)) := by
      simpa using (hY.const_div_atTop (Real.logb 2 c)).add_const ((1 : ℝ) / 2)
    filter_upwards [hl.eventually_const_lt ha, hL] with i h₁ h₂ using h₁.trans_le h₂
  · obtain ⟨p, hp, hpb⟩ := exists_between hb
    obtain ⟨C, hC, hhi⟩ := hupper (p - 1 / 2) (sub_pos.mpr hp)
    have hp₀ : 0 ≤ p := by linarith
    let A := C * (2 : ℝ) ^ p
    have hA : 0 < A := mul_pos hC (by positivity)
    have hu : Tendsto (fun i => Real.logb 2 A / Y i + p) l (𝓝 p) := by
      simpa using (hY.const_div_atTop (Real.logb 2 A)).add_const p
    filter_upwards [hhi, hposN, hposX, hposY, hposS, hu.eventually_lt_const hpb]
      with i hi hn hx hy hs hε
    apply lt_of_le_of_lt _ hε
    have hx' : 0 < X i := by linarith
    have hpow := Real.rpow_le_rpow (show 0 ≤ 1 + X i by linarith)
      (show 1 + X i ≤ 2 * X i by linarith) hp₀
    rw [Real.mul_rpow (by norm_num) hx'.le] at hpow
    have hi' : S i ≤ C * N i * (1 + X i) ^ p := by
      simpa only [show (1 : ℝ) / 2 + (p - 1 / 2) = p by ring] using hi
    have hratio : S i / N i ≤ A * (X i) ^ p := by
      apply (div_le_iff₀ hn).mpr
      change _ ≤ C * 2 ^ p * X i ^ p * N i
      nlinarith only [hi', mul_le_mul_of_nonneg_left hpow (mul_pos hC hn).le]
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hs hratio
    rw [Real.logb_mul hA.ne' (Real.rpow_pos_of_pos hx' p).ne',
      Real.logb_rpow_eq_mul_logb_of_pos hx'] at hlog
    change Real.logb 2 (S i / N i) / Y i ≤ _
    apply (div_le_iff₀ hy).mpr
    rw [add_mul, div_mul_cancel₀ _ hy.ne']
    exact hlog

/-- The uniform square-root lower bound and all positive-slack upper bounds
for a family of finite problems. The constants are independent of the index. -/
structure FiniteCostBounds {ι : Type*} (order cost : ι → ℕ) : Prop where
  lower : ∃ c > (0 : ℝ), ∀ i, 2 ≤ order i →
    c * order i * Real.sqrt (Real.logb 2 (order i)) ≤ cost i
  upper : ∀ ε : ℝ, 0 < ε → ∃ C > (0 : ℝ), ∀ i, 2 ≤ order i →
    (cost i : ℝ) ≤ C * order i * (1 + Real.logb 2 (order i)) ^ ((1 : ℝ) / 2 + ε)

theorem FiniteCostBounds.tendsto_logOverhead {ι : Type*} {order cost : ι → ℕ} {l : Filter ι}
    (h : FiniteCostBounds order cost) (hN : Tendsto order l atTop) :
    Tendsto (fun i => logOverhead (order i) (cost i)) l (𝓝 ((1 : ℝ) / 2)) := by
  apply tendsto_logOverhead_of_bounds (tendsto_natCast_atTop_atTop.comp hN)
  · obtain ⟨c, hc, hlo⟩ := h.lower
    exact ⟨c, hc, (hN.eventually_ge_atTop 2).mono fun i hi => hlo i hi⟩
  · intro ε hε
    obtain ⟨C, hC, hup⟩ := h.upper ε hε
    exact ⟨C, hC, (hN.eventually_ge_atTop 2).mono fun i hi => hup i hi⟩

/-- The Fourier complexity theorem's finite estimates imply its logarithmic
overhead limit for the actual unrestricted binary linear circuit size.
The groups and fields can both vary along the sequence. -/
theorem fourier_logOverhead_tendsto {ι : Type*} (G K : ι → Type*) [∀ i, AddCommGroup (G i)]
    [∀ i, Fintype (G i)] [∀ i, Field (K i)] {l : Filter ι}
    (hN : Tendsto (fun i => Fintype.card (G i)) l atTop)
    (h : FiniteCostBounds (fun i => Fintype.card (G i))
      (fun i => complexity (fourierMatrix (G i) (K i)))) :
    Tendsto (fun i => logOverhead (Fintype.card (G i))
      (complexity (fourierMatrix (G i) (K i)))) l (𝓝 ((1 : ℝ) / 2)) :=
  h.tendsto_logOverhead hN

/-- The same finite forward estimates give the inverse limit, using the
equality of the two circuit sizes over an admissible splitting field. -/
theorem inverseFourier_logOverhead_tendsto {ι : Type*} (G K : ι → Type*) [∀ i, AddCommGroup (G i)]
    [∀ i, Fintype (G i)] [∀ i, Field (K i)] {l : Filter ι}
    (hadm : ∀ i, Admissible (G i) (K i))
    (hN : Tendsto (fun i => Fintype.card (G i)) l atTop)
    (h : FiniteCostBounds (fun i => Fintype.card (G i))
      (fun i => complexity (fourierMatrix (G i) (K i)))) :
    Tendsto (fun i => logOverhead (Fintype.card (G i))
      (complexity (inverseFourierMatrix (G i) (K i)))) l (𝓝 ((1 : ℝ) / 2)) := by
  simpa only [fun i => complexity_inverseFourierMatrix (G i) (K i) (hadm i)] using
    fourier_logOverhead_tendsto G K hN h

/-- The cyclic DFT and its inverse both have logarithmic overhead exponent
one half under the finite estimates. The primitive root, field, and length
can all vary with the index. -/
theorem dft_logOverhead_tendsto {ι : Type*} (K : ι → Type*) [∀ i, Field (K i)]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (ζ : ∀ i, K i) (hζ : ∀ i, IsPrimitiveRoot (ζ i) (n i))
    {l : Filter ι} (hn : Tendsto n l atTop)
    (h : FiniteCostBounds n (fun i => complexity (fourierMatrix (ZMod (n i)) (K i)))) :
    Tendsto (fun i => logOverhead (n i) (complexity (dftMatrix (n i) (ζ i)))) l (𝓝 ((1 : ℝ) / 2)) ∧
    Tendsto (fun i => logOverhead (n i) (complexity (inverseDftMatrix (n i) (ζ i)))) l
      (𝓝 ((1 : ℝ) / 2)) := by
  have hf := h.tendsto_logOverhead hn
  constructor
  · simpa only [fun i => complexity_dftMatrix (hζ i)] using hf
  · simpa only [fun i => complexity_inverseDftMatrix (hζ i),
      fun i => complexity_inverseFourierMatrix (ZMod (n i)) (K i) (admissible_zmod (hζ i))] using hf

end FiniteFourier
end LinearAlgebra
end OAI
