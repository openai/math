import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The word-step exponent for parsimonious RAM transcripts

The site loop can charge a linear scan of the private-write log at each
instruction. The sorting term pays for every offset at every comparator
layer. Since the word width and the stage counts are polylogarithmic, their
constants and powers fit the slack in the exponent of Lemma 10.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open Filter

/-- A fixed polynomial in the logarithm fits within the input length,
with a threshold independent of every private computation or message. -/
theorem eventually_polylog_le (A k : ℕ) : ∀ᶠ n : ℕ in atTop, A * (n.log2 + 1)^k ≤ n := by
  have hk := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k
    (r := 2) (by norm_num)).def (c := ((A+1 : ℕ) : ℝ)⁻¹ / 2^k) (by positivity)
  obtain ⟨L, hL⟩ := eventually_atTop.mp hk
  filter_upwards [eventually_ge_atTop (2^(max L 1))] with n hn
  have hn0 : 0 < n := (Nat.two_pow_pos _).trans_le hn
  have hlarge : max L 1 ≤ n.log2 := (Nat.le_log2 hn0.ne').mpr hn
  have hpos : 1 ≤ n.log2 := (le_max_right _ _).trans hlarge
  have hh := hL n.log2 ((le_max_left ..).trans hlarge)
  simp only [Real.norm_eq_abs, abs_pow, abs_of_nonneg (show 0 ≤ (n.log2 : ℝ) by positivity), abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))] at hh
  have hreal : ((A+1 : ℕ) : ℝ) * 2^k * (n.log2 : ℝ)^k ≤ (2:ℝ)^n.log2 := by
    have hp : 0 < ((A+1 : ℕ) : ℝ) := by positivity
    have htwo : 0 < (2:ℝ)^k := by positivity
    calc
      _ ≤ ((A+1 : ℕ) : ℝ) * 2^k * (((A+1 : ℕ) : ℝ)⁻¹ / 2^k * (2:ℝ)^n.log2) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (2:ℝ)^n.log2 := by field_simp
  have hnat : (A+1) * 2^k * n.log2^k ≤ 2^n.log2 := by exact_mod_cast hreal
  calc
    A * (n.log2 + 1)^k ≤ (A+1) * (2*n.log2)^k := by gcongr <;> omega
    _ = (A+1) * 2^k * n.log2^k := by rw [mul_pow, Nat.mul_assoc]
    _ ≤ 2^n.log2 := hnat
    _ ≤ n := (Nat.le_log2 hn0.ne').mp le_rfl

/-- The logarithmic number of address bits and the prescribed quartic word
width simultaneously fit the bounds used below. `r ≤ B(log₂ n+1)` includes
the rounded address format of the live and virtual RAMs. -/
theorem eventually_word_stage_le (B D : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ r t : ℕ,
    r ≤ B * (n.log2 + 1) → t ≤ D * (n.log2 + 1) →
    (r + 10)^4 ≤ n ∧ t ≤ n := by
  filter_upwards [eventually_polylog_le ((B+10)^4) 4, eventually_polylog_le D 1] with n hw ht
  intro r t hr hts
  constructor
  · have h : r+10 ≤ (B+10)*(n.log2+1) := by
      rw [Nat.add_mul]; omega
    exact (Nat.pow_le_pow_left h 4).trans (by simpa [mul_pow] using hw)
  · simpa using hts.trans (by simpa using ht)

/-- An upper envelope in primitive word steps. Here `stages` is the number
of bitonic phases, `H` the bucket capacity, and `k` a fixed program constant.
Each of the `4H` slots is visited at each sorting layer. -/
def transcriptWorkBound (k w H stages fuel : ℕ) : ℕ :=
  2048 * (w + 1) + 2048 * (H + 1) * (fuel + 1) * (fuel + 1) * (w + k + 2) +
    (stages + 1).choose 2 * (4 * H * (1024 * (w + 1)) + 9)

set_option maxRecDepth 8192 in
/-- The envelope with private fuel `n^u` is within the paper's site clock.
The threshold on the fixed program constant and the polylogarithmic
parameters can be taken before choosing the messages. -/
theorem transcriptWorkBound_le_clock {n u k w H stages : ℕ} (hn : 2048 ≤ n)
    (hk : k+2 ≤ n) (hw : w ≤ n) (hH : H ≤ 2*n) (hstage : stages+1 ≤ n) :
    transcriptWorkBound k w H stages (n^u) ≤ n^(10*u+30) := by
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hs : 2*n ≤ n^2 := by rw [pow_two]; exact Nat.mul_le_mul_right n hn2
  have hw' : w+1 ≤ n^2 := (by omega : w+1 ≤ 2*n).trans hs
  have hk' : w+k+2 ≤ n^2 := (by omega : w+k+2 ≤ 2*n).trans hs
  have hH' : H+1 ≤ n^2 := by
    rw [pow_two]
    exact (by omega : H+1 ≤ 3*n).trans (Nat.mul_le_mul_right n (by omega))
  have hf : n^u + 1 ≤ n^(u+1) := by
    rw [pow_succ]
    have h := Nat.pow_pos (by omega : 0 < n) (n := u)
    exact (by omega : n^u+1 ≤ n^u*2).trans (Nat.mul_le_mul_left _ hn2)
  have hb : 4*H ≤ n^2 := by
    rw [pow_two]
    exact (by omega : 4*H ≤ 8*n).trans (Nat.mul_le_mul_right n (by omega))
  have hc : (stages+1).choose 2 ≤ n^2 := by
    rw [Nat.choose_two_right, pow_two]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul hstage (by omega))
  have a : 2048*(w+1) ≤ n^3 := by
    calc _ ≤ n*n^2 := Nat.mul_le_mul hn hw'
         _ = _ := by ring
  have b : 2048*(H+1)*(n^u+1)*(n^u+1)*(w+k+2) ≤ n^(2*u+7) := by
    calc _ ≤ n*n^2*n^(u+1)*n^(u+1)*n^2 := by gcongr
         _ = _ := by rw [show 2*u+7 = 1+2+(u+1)+(u+1)+2 by omega]; simp only [pow_add, pow_one]
  have c : 4*H*(1024*(w+1)) ≤ n^5 := by
    calc _ ≤ n^2*(n*n^2) := by gcongr; omega
         _ = _ := by ring
  have cc : (stages+1).choose 2 * (4*H*(1024*(w+1))+9) ≤ n^8 := by
    calc _ ≤ n^2 * n^6 := by
           apply Nat.mul_le_mul hc
           rw [show n^6=n^5*n by ring]
           have hp : 9 ≤ n^5 := (by omega : 9 ≤ n).trans (Nat.le_self_pow (by decide) n)
           exact (by omega : 4*H*(1024*(w+1))+9 ≤ n^5*2).trans (Nat.mul_le_mul_left _ hn2)
         _ = _ := by ring
  have ha := a.trans (Nat.pow_le_pow_right hn1 (show 3 ≤ 2*u+8 by omega))
  have hbb := b.trans (Nat.pow_le_pow_right hn1 (show 2*u+7 ≤ 2*u+8 by omega))
  have hcc := cc.trans (Nat.pow_le_pow_right hn1 (show 8 ≤ 2*u+8 by omega))
  calc
    transcriptWorkBound k w H stages (n^u) ≤ n^(2*u+8)*3 := by unfold transcriptWorkBound; omega
    _ ≤ n^(2*u+8)*n := Nat.mul_le_mul_left _ (by omega)
    _ = n^(2*u+9) := (pow_succ n (2*u+8)).symm
    _ ≤ n^(10*u+30) := Nat.pow_le_pow_right hn1 (by omega)

/-- With `S=2^d`, `H=2^e`, a logarithmic site identifier and
`H ≤ 2n`, the site-clock estimate holds eventually and uniformly over all
permitted choices of the parameters. -/
theorem eventually_transcriptWorkBound_le_clock (B D k u : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ r d e : ℕ, r ≤ B * (n.log2 + 1) → d ≤ D * (n.log2 + 1) →
      2^e ≤ 2*n →
      transcriptWorkBound k ((r+10)^4) (2^e) (2+e+d) (n^u) ≤ n^(10*u+30) := by
  filter_upwards [eventually_ge_atTop 2048, eventually_ge_atTop (k+2),
    eventually_word_stage_le B (D+4)] with n hn hk hparams
  intro r d e hr hd hH
  have hn0 : n ≠ 0 := by omega
  have he := (Nat.le_log2 (by omega : 2*n ≠ 0)).mpr hH
  rw [Nat.log2_two_mul hn0] at he
  have ht : 2+e+d+1 ≤ (D+4)*(n.log2+1) := by rw [Nat.add_mul]; omega
  obtain ⟨hw, hstage⟩ := hparams r _ hr ht
  exact transcriptWorkBound_le_clock hn hk hw hH hstage

end BurstRAM

end VPVNP
end Computability
end OAI
