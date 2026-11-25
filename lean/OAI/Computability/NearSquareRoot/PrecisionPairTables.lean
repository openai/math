import OAI.Computability.NearSquareRoot.PrecisionRotatedPair
import OAI.Computability.NearSquareRoot.SynchronizedPair
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! # Local phase tables of the synchronized two-coordinate factors -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open ComplexConjugate

/-- Exact coefficients of the three local phase diagonals evaluated on rational
approximations to the matrix entries. Square roots in the normalization are
rounded at `p` fractional bits. -/
def rationalTable (p : ℕ) (a b : ℚ × ℚ) : Fin 6 → ℚ × ℚ :=
  let u := unitPhase p a
  let v := unitPhase p b
  let r := modulus p a
  let s := modulus p b
  ![u, (v.2, v.1), (r,s), (r,-s), (1,0),
    (u.1 * v.2 - u.2 * v.1, -(u.1 * v.1 + u.2 * v.2))]

private theorem norm_mul_error {x y x' y' : ℂ} {E : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h₁ : ‖x' - x‖ ≤ E) (h₂ : ‖y' - y‖ ≤ E) (hE : E ≤ 1) :
    ‖x' * y' - x * y‖ ≤ 3 * E := by
  have h : ‖y'‖ ≤ 2 := by
    have h := norm_add_le (y' - y) y
    rw [sub_add_cancel, hy] at h
    linarith
  calc
    _ = ‖(x' - x) * y' + x * (y' - y)‖ := by congr 1; ring
    _ ≤ ‖(x' - x) * y'‖ + ‖x * (y' - y)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_mul, hx, one_mul]
      linarith [mul_le_mul_of_nonneg_left h (norm_nonneg (x' - x))]

private theorem table_values (p : ℕ) (a b : ℚ × ℚ) (i : Fin 6) :
    let u := toComplex (unitPhase p a)
    let v := toComplex (unitPhase p b)
    let r : ℂ := (modulus p a : ℝ)
    let s : ℂ := (modulus p b : ℝ)
    toComplex (rationalTable p a b i) =
      ![u, Complex.I * conj v, r + Complex.I * s, r - Complex.I * s, 1,
        -Complex.I * conj u * v] i := by
  fin_cases i <;> apply Complex.ext <;>
    simp [rationalTable, toComplex, Complex.mul_re, Complex.mul_im]
  all_goals ring

private theorem middle_error (r s x y : ℝ) (E : ℝ)
    (hr : |r - x| ≤ E) (hs : |s - y| ≤ E) :
    ‖((r:ℂ) + Complex.I * s) - ((x:ℂ) + Complex.I * y)‖ ≤ 2 * E ∧
    ‖((r:ℂ) - Complex.I * s) - ((x:ℂ) - Complex.I * y)‖ ≤ 2 * E := by
  constructor <;> refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_ <;>
    simp [Complex.mul_re, Complex.mul_im] <;>
    first | linarith | (rw [show -s + y = -(s - y) by ring, abs_neg]; linarith)

private theorem modulus_error (p : ℕ) (q : ℚ × ℚ) (z : ℂ) (ε : ℝ)
    (hq : ‖toComplex q - z‖ ≤ ε) :
    |(modulus p q : ℝ) - ‖z‖| ≤ ε + 1 / (2 : ℝ) ^ p := by
  obtain ⟨hl, hh⟩ := modulus_interval p q
  obtain ⟨hli, hhi⟩ := abs_le.mp ((abs_norm_sub_norm_le _ _).trans hq)
  rw [abs_le]
  constructor <;> linarith [one_div_pos.mpr (show (0:ℝ) < 2 ^ p by positivity)]

private theorem rationalTable_error (p : ℕ) (qa qb : ℚ × ℚ) (a b : ℂ) (ε : ℝ)
    (ha : 1 / 5 ≤ ‖a‖) (hb : 1 / 5 ≤ ‖b‖)
    (hqa : ‖toComplex qa - a‖ ≤ ε) (hqb : ‖toComplex qb - b‖ ≤ ε)
    (hε : ε ≤ 1 / 40) (hp : 1 / (2 : ℝ) ^ p ≤ 1 / 40) (i : Fin 6) :
    let u := a / (‖a‖ : ℂ)
    let v := b / (‖b‖ : ℂ)
    let r := (‖a‖ : ℂ)
    let s := (‖b‖ : ℂ)
    ‖toComplex (rationalTable p qa qb i) -
      ![u, Complex.I * conj v, r + Complex.I * s, r - Complex.I * s, 1,
        -Complex.I * conj u * v] i‖ ≤ 90 * (ε + 1 / (2 : ℝ) ^ p) := by
  let U := toComplex (unitPhase p qa)
  let V := toComplex (unitPhase p qb)
  let u := a / (‖a‖ : ℂ)
  let v := b / (‖b‖ : ℂ)
  let δ := 1 / (2 : ℝ) ^ p
  let E := 10 * (2 * ε + δ)
  have hε' := (norm_nonneg _).trans hqa
  have hδ : 0 ≤ δ := by unfold δ; positivity
  have hE : E ≤ 1 := by dsimp [E, δ]; linarith
  have hU : ‖U - u‖ ≤ E := unitPhase_error p qa a ε ha hqa hε hp
  have hV : ‖V - v‖ ≤ E := unitPhase_error p qb b ε hb hqb hε hp
  have hMul := norm_mul_error (x' := conj U) (y' := V) (x := conj u) (y := v)
    (by simp [u, div_self (show ‖a‖ ≠ 0 by linarith)])
    (by simp [v, div_self (show ‖b‖ ≠ 0 by linarith)])
    (by simpa only [← map_sub, Complex.norm_conj] using hU) hV hE
  have hprod : ‖-Complex.I * conj U * V - -Complex.I * conj u * v‖ ≤ 3 * E := by
    simpa only [mul_assoc, ← mul_sub, norm_mul, norm_neg, Complex.norm_I, one_mul] using hMul
  have hIm : ‖Complex.I * conj V - Complex.I * conj v‖ ≤ E := by
    simpa only [← mul_sub, norm_mul, Complex.norm_I, one_mul, ← map_sub, Complex.norm_conj]
      using hV
  obtain ⟨h₁, h₂⟩ := middle_error (modulus p qa) (modulus p qb) ‖a‖ ‖b‖ (ε + δ)
    (modulus_error p qa a ε hqa) (modulus_error p qb b ε hqb)
  dsimp only
  rw [table_values]
  fin_cases i <;> change _ ≤ 90 * (ε + δ)
  · exact hU.trans (by dsimp [E]; linarith)
  · exact hIm.trans (by dsimp [E]; linarith)
  · exact h₁.trans (by linarith)
  · exact h₂.trans (by linarith)
  · change ‖(1 : ℂ) - 1‖ ≤ _
    rw [sub_self, norm_zero]
    positivity
  · exact hprod.trans (by dsimp [E]; linarith)

/-- Compute all six local diagonal factors for a complex rational approximation
to the scaled chirp multiplier. The guard is independent of the axis length. -/
def chirpPairTable (bits : ℕ) (q : ℚ × ℚ) : Fin 6 → ℚ × ℚ :=
  let p := bits + 10
  rationalTable p (rotatedA p q) (rotatedB p q)

/-- The computed coefficients approximate the six explicit factors of the
Walsh-rotated chirp pair. -/
theorem chirpPairTable_approximates (bits : ℕ) (q : ℚ × ℚ) (z : ℂ) (hz : ‖z‖ ≤ 1 / 2)
    (hq : ‖toComplex q - z‖ ≤ 1 / (2 : ℝ) ^ (bits + 10)) (i : Fin 6) :
    let t : ℂ := (Real.sqrt (1 - ‖z‖ ^ 2) : ℝ)
    let a := (SynchronizedPair.w : ℂ) * (z + t)
    let b := (SynchronizedPair.w : ℂ) * (t - conj z)
    ‖toComplex (chirpPairTable bits q i) - SynchronizedPair.tableEntry a b i‖ ≤
      1 / (2 : ℝ) ^ bits := by
  let p := bits + 10
  let δ : ℝ := 1 / 2 ^ p
  let t : ℂ := (Real.sqrt (1 - ‖z‖ ^ 2) : ℝ)
  let a := (SynchronizedPair.w : ℂ) * (z + t)
  let b := (SynchronizedPair.w : ℂ) * (t - conj z)
  have hm : 1 ≤ (2 : ℝ) ^ bits := one_le_pow₀ (by norm_num)
  have hδ : δ ≤ 1 / 1024 := by
    dsimp [δ, p]
    rw [pow_add, div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num
    linarith
  obtain ⟨ha,hb,_⟩ := synchronizedPair_bounds z hz
  obtain ⟨hA,hB⟩ := rotatedPair_error p q z δ hz hq (by linarith)
  have he := rationalTable_error p (rotatedA p q) (rotatedB p q) a b (4 * (δ + δ))
    ha hb hA hB (by linarith) (by change δ ≤ _; linarith) i
  refine he.trans ?_
  dsimp [δ, p]
  rw [pow_add]
  field_simp
  norm_num

/-- The same six ideal entries synthesize the two-coordinate unitary through
three identical normalized Walsh rounds. -/
theorem chirpPairTable_error (bits : ℕ) (q : ℚ × ℚ) (z : ℂ) (hz : ‖z‖ ≤ 1 / 2)
    (hq : ‖toComplex q - z‖ ≤ 1 / (2 : ℝ) ^ (bits + 10)) :
    ∃ e : Fin 6 → ℂ, (∀ i, ‖e i‖ = 1) ∧
      (∀ i, ‖toComplex (chirpPairTable bits q i) - e i‖ ≤ 1 / (2 : ℝ) ^ bits) ∧
      SynchronizedPair.pair z = SynchronizedPair.walsh * SynchronizedPair.diag (e 0) (e 1) *
        SynchronizedPair.walsh * SynchronizedPair.diag (e 2) (e 3) *
        SynchronizedPair.walsh * SynchronizedPair.diag (e 4) (e 5) :=
  ⟨_, (SynchronizedPair.pair_eq_table hz).1,
    chirpPairTable_approximates bits q z hz hq, (SynchronizedPair.pair_eq_table hz).2⟩

end PhaseTable

end NearSquareRoot
end Computability
end OAI
