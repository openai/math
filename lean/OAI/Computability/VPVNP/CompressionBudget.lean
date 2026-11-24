import OAI.Computability.VPVNP.RAMClock
import OAI.Computability.VPVNP.Compression
import OAI.Computability.VPVNP.CompressionParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Communication budgets for a compressed pair of groups

Sections 12 and 13 of *VP and VNP differ over every field* compare the
compressed bit count and the number of external accesses with the budget
of a live group. All bounds below are uniform in the choice of compression
terms, with thresholds depending only on the fixed constants.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open Filter Asymptotics

/-- Every fixed power of the binary logarithm is eventually absorbed by any
positive gap between two real power exponents, with any prescribed coefficient. -/
theorem eventually_absorb_polylog (A : ℝ) (k : ℕ) {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ a * (n.log2 + 1 : ℝ) ^ k ≤ ε * (n : ℝ) ^ b := by
  let D := ⌈(b - a)⁻¹⌉₊ + 1
  let M := ⌈A / ε⌉₊
  have hD : 0 < (D : ℝ) := by dsimp [D]; positivity
  have hgap : (D : ℝ)⁻¹ ≤ b - a := by
    have hceil := Nat.le_ceil ((b - a)⁻¹)
    have hle : (b - a)⁻¹ ≤ (D : ℝ) := by dsimp [D]; push_cast; linarith
    simpa only [inv_inv] using (inv_le_inv₀ hD (inv_pos.mpr (sub_pos.mpr hab))).mpr hle
  filter_upwards [BurstRAM.eventually_polylog_le (M ^ D) (k * D), eventually_ge_atTop 1] with n hn hn1
  have hbase : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : 0 < (n : ℝ) := by linarith
  have hpoly : ((M : ℝ) * (n.log2 + 1 : ℝ) ^ k) ^ D ≤ n := by
    rw [mul_pow, ← pow_mul]
    exact_mod_cast hn
  have hsmall : (M : ℝ) * (n.log2 + 1 : ℝ) ^ k ≤ (n : ℝ) ^ (b - a) := by
    apply le_trans _ (Real.rpow_le_rpow_of_exponent_le hbase hgap)
    apply (Real.le_rpow_inv_iff_of_pos (by positivity) hnpos.le hD).mpr
    simpa only [Real.rpow_natCast] using hpoly
  have hA : A ≤ ε * M := by
    have hm := Nat.le_ceil (A / ε)
    rwa [div_le_iff₀ hε, mul_comm] at hm
  calc
    _ ≤ (ε * M) * (n : ℝ) ^ a * (n.log2 + 1 : ℝ) ^ k := by gcongr
    _ = ε * (n : ℝ) ^ a * ((M : ℝ) * (n.log2 + 1 : ℝ) ^ k) := by ring
    _ ≤ ε * (n : ℝ) ^ a * (n : ℝ) ^ (b - a) := by gcongr
    _ = ε * (n : ℝ) ^ b := by rw [mul_assoc, ← Real.rpow_add hnpos]; ring_nf

/-- The live address exponent can be fixed after the polynomial preparation
exponent. The multiplicative constant and the polylogarithmic power may
still depend on the chosen address exponent. -/
theorem preparation_isLittleO_processors (A : ℕ → ℝ) (k : ℕ → ℕ) {e B : ℕ} (he : e < B) :
    (fun n : ℕ => A B * (n : ℝ) ^ e * (n.log2 + 1 : ℝ) ^ k B) =o[atTop]
      (fun n : ℕ => (2 : ℝ) ^ (B * Nat.clog 2 n)) := by
  apply IsLittleO.of_bound
  intro ε hε
  have hsmall := eventually_absorb_polylog |A B| (k B) (show (e : ℝ) < B by exact_mod_cast he) hε
  filter_upwards [hsmall] with n h
  have hn : (n : ℝ) ^ B ≤ (2 : ℝ) ^ (B * Nat.clog 2 n) := by
    rw [Nat.mul_comm, pow_mul]
    exact_mod_cast Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) n) B
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
    abs_of_nonneg (by positivity : 0 ≤ (n.log2 + 1 : ℝ)), abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  exact (by simpa only [Real.rpow_natCast] using h : _ ≤ ε * (n : ℝ) ^ B).trans
    (mul_le_mul_of_nonneg_left hn hε.le)

/-- Equation (12.1) for every energy sequence satisfying the one-block recurrence.
`P` and `W` are the initial position count and width, and `R` is the live site count.
The eventual threshold is independent of these counts and the term choices. -/
theorem eventually_finalWidth_le {θ d c κ A B : ℝ} (hθ : 0 < θ) (hd : 0 ≤ d)
    (hc : 0 ≤ c) (hκ : 2 < κ) (hA : 0 ≤ A) (s t : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (R P W : ℕ) (L : ℕ → ℝ),
      (P : ℝ) ≤ A * R * (n : ℝ) ^ (3 / 4 : ℝ) * (n.log2 + 1 : ℝ) ^ s →
      (W : ℝ) ≤ B * (n : ℝ) ^ (1 / 4 : ℝ) * (n.log2 + 1 : ℝ) ^ t →
      0 ≤ L 0 → Real.sqrt (L 0) ≤ d * P * W →
      (∀ i < blockCount θ n, L (i + 1) ≤ L i / 4 + c * ((P : ℝ) / κ ^ i) ^ 2) →
      Real.sqrt (L (blockCount θ n)) ≤ (R : ℝ) * (n : ℝ) ^ (1 - θ / 2) := by
  let D := Real.sqrt (4 * c / (1 - 4 / κ ^ 2))
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hterm₁ := eventually_absorb_polylog (2 * d * A * B) (s + t)
    (show 1 - θ < 1 - θ / 2 by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
  have hterm₂ := eventually_absorb_polylog (2 * A * D) s
    (show 3 / 4 - θ < 1 - θ / 2 by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hterm₁, hterm₂, eventually_ge_atTop 1] with n h₁ h₂ hn
  intro R P W L hP hW hinit hstart hstep
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ ≤ (Real.sqrt (L 0) + P * D) / 2 ^ blockCount θ n :=
      sqrtEnergy_le L _ (by positivity) hc hκ hinit hstep
    _ ≤ (d * P * W + P * D) * (2 * (n : ℝ) ^ (-θ)) := by
      rw [div_eq_mul_one_div]; gcongr; exact inv_two_pow_blockCount θ hn
    _ ≤ (d * (A * R * (n : ℝ) ^ (3 / 4 : ℝ) * (n.log2 + 1 : ℝ) ^ s) *
          (B * (n : ℝ) ^ (1 / 4 : ℝ) * (n.log2 + 1 : ℝ) ^ t) +
          (A * R * (n : ℝ) ^ (3 / 4 : ℝ) * (n.log2 + 1 : ℝ) ^ s) * D) *
          (2 * (n : ℝ) ^ (-θ)) := by gcongr
    _ = (R : ℝ) * ((2 * d * A * B) * (n : ℝ) ^ (1 - θ) * (n.log2 + 1 : ℝ) ^ (s + t) +
          (2 * A * D) * (n : ℝ) ^ (3 / 4 - θ) * (n.log2 + 1 : ℝ) ^ s) := by
      rw [show (1 - θ) = (3 / 4 + 1 / 4) + (-θ) by ring, Real.rpow_add hnpos, Real.rpow_add hnpos,
        sub_eq_add_neg, Real.rpow_add hnpos, pow_add]
      ring
    _ ≤ (R : ℝ) * ((1/2) * (n : ℝ) ^ (1-θ/2) + (1/2) * (n : ℝ) ^ (1-θ/2)) := by gcongr
    _ = _ := by ring

/-- Proposition 13.1's external calls and probes use a vanishing fraction of
`R K`. The hypotheses separate the initial geometry, final bit count and the
per-path operation estimate from this asymptotic comparison. -/
theorem simulationCost_isLittleO {R P F work : ℕ → ℕ} {θ δ A C : ℝ} {s t : ℕ}
    (hθ : 0 < θ) (hθ' : θ < 1 / 100) (hδ : δ < θ / 10) (hC : 0 ≤ C)
    (hP : ∀ᶠ n in atTop, (P n : ℝ) ≤ A * R n * (n : ℝ) ^ (3 / 4 : ℝ) * (n.log2 + 1 : ℝ) ^ s)
    (hF : ∀ᶠ n in atTop, (F n : ℝ) ≤ R n * (n : ℝ) ^ (1 - θ / 2))
    (hwork : ∀ᶠ n in atTop, (work n : ℝ) ≤ C *
      (P n * (n : ℝ) ^ (1 / 100 : ℝ) * (n.log2 + 1 : ℝ) ^ t + F n)) :
    (fun n => (work n : ℝ)) =o[atTop] (fun n => (R n : ℝ) * liveBucket δ n) := by
  apply IsLittleO.of_bound
  intro ε hε
  have hs := eventually_absorb_polylog (C * A) (s + t)
    (show 3 / 4 + 1 / 100 < 1 - δ by linarith) (half_pos hε)
  have hf := eventually_absorb_polylog C 0
    (show 1 - θ / 2 < 1 - δ by linarith) (half_pos hε)
  filter_upwards [hP, hF, hwork, hs, hf, eventually_ge_atTop 1] with n hpos hbits hcost hsmall hfinal hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  simp only [pow_zero, mul_one] at hfinal
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc
    _ ≤ _ := hcost
    _ ≤ C * (A * R n * (n : ℝ) ^ (3 / 4 : ℝ) * (n.log2 + 1 : ℝ) ^ s *
          (n : ℝ) ^ (1 / 100 : ℝ) * (n.log2 + 1 : ℝ) ^ t + R n * (n : ℝ) ^ (1 - θ / 2)) := by gcongr
    _ = R n * ((C * A) * (n : ℝ) ^ (3 / 4 + 1 / 100 : ℝ) * (n.log2 + 1 : ℝ) ^ (s + t) +
          C * (n : ℝ) ^ (1 - θ / 2)) := by rw [Real.rpow_add hnpos, pow_add]; ring
    _ ≤ R n * ((ε / 2) * (n : ℝ) ^ (1 - δ) + (ε / 2) * (n : ℝ) ^ (1 - δ)) := by gcongr
    _ = ε * ((R n : ℝ) * (n : ℝ) ^ (1 - δ)) := by ring
    _ ≤ _ := by gcongr; exact (liveBucket_bounds (by linarith : δ ≤ 1) hn).1

/-- Combine the wire-energy and operation estimates for an entire family of paths.
The final bit count is the sum of the actual final arc widths. Only the per-block
recurrence, initial envelopes, and accounting inequality for the simulated path
are required as input. -/
theorem pairSimulation_budget {Wire : ℕ → Type*} [∀ n, Fintype (Wire n)]
    (width : ∀ n, Wire n → ℕ) (mass : ∀ n, Wire n → ℝ)
    (hmass : ∀ᶠ n in atTop, ∀ e, 0 < mass n e) (hnorm : ∀ᶠ n in atTop, ∑ e, mass n e = 1)
    {R P W work : ℕ → ℕ} {L : ℕ → ℕ → ℝ} {θ δ d c κ A B C : ℝ} {s t k : ℕ}
    (hθ : 0 < θ) (hθ' : θ < 1 / 100) (hδ : δ < θ / 10)
    (hd : 0 ≤ d) (hc : 0 ≤ c) (hκ : 2 < κ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hP : ∀ᶠ n in atTop, (P n : ℝ) ≤ A * R n * (n : ℝ) ^ (3/4 : ℝ) * (n.log2 + 1 : ℝ) ^ s)
    (hW : ∀ᶠ n in atTop, (W n : ℝ) ≤ B * (n : ℝ) ^ (1/4 : ℝ) * (n.log2 + 1 : ℝ) ^ t)
    (hinit : ∀ᶠ n in atTop, 0 ≤ L n 0 ∧ Real.sqrt (L n 0) ≤ d * P n * W n)
    (hstep : ∀ᶠ n in atTop, ∀ i < blockCount θ n,
      L n (i + 1) ≤ L n i / 4 + c * ((P n : ℝ) / κ ^ i) ^ 2)
    (hfinal : ∀ᶠ n in atTop, ∑ e, (width n e : ℝ) ^ 2 / mass n e ≤ L n (blockCount θ n))
    (hwork : ∀ᶠ n in atTop, (work n : ℝ) ≤ C *
      (P n * (n : ℝ) ^ (1 / 100 : ℝ) * (n.log2 + 1 : ℝ) ^ k + ↑(∑ e, width n e))) :
    (∀ᶠ n in atTop, (∑ e, (width n e : ℝ)) ≤ R n * (n : ℝ) ^ (1 - θ / 2)) ∧
    (fun n => (work n : ℝ)) =o[atTop] (fun n => (R n : ℝ) * liveBucket δ n) := by
  have hF : ∀ᶠ n in atTop, (∑ e, (width n e : ℝ)) ≤ R n * (n : ℝ) ^ (1 - θ / 2) := by
    filter_upwards [hP, hW, hinit, hstep, hfinal, hmass, hnorm,
      eventually_finalWidth_le (B := B) hθ hd hc hκ hA s t] with n hp hw hi hs hf hm hunit hbound
    exact (widthSum_le_sqrtEnergy (fun e => (width n e : ℝ)) (mass n) hm hunit).trans
      ((Real.sqrt_le_sqrt hf).trans (hbound (R n) (P n) (W n) (L n) hp hw hi.1 hi.2 hs))
  exact ⟨hF, simulationCost_isLittleO (F := fun n => ∑ e, width n e) hθ hθ' hδ hC hP
    (by simpa using hF) hwork⟩

/-- In a regular network with `P d` arcs of equal mass, bounding each width by `W`
bounds the initial square-root energy by `P d W`, also for an empty network. -/
theorem regularWire_sqrtEnergy_le {Wire : Type*} [Fintype Wire] (width : Wire → ℕ)
    {P d W : ℕ} (hcard : Fintype.card Wire = P * d) (hW : ∀ e, width e ≤ W) :
    Real.sqrt (∑ e, (width e : ℝ) ^ 2 / (1 / ((P : ℝ) * d))) ≤ (P : ℝ) * d * W := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ _e : Wire, (W : ℝ) ^ 2 / (1 / ((P : ℝ) * d)) :=
      Finset.sum_le_sum fun e _ => by gcongr; exact_mod_cast hW e
    _ = _ := by simp [hcard, div_eq_mul_inv]; ring

/-- Field lengths and local monomial degrees satisfy the section 12 exponents
whenever the block growth bound is `C₂^T (W+1)`, with any fixed multiplier. -/
theorem eventually_fieldGrowth_le {θ C₂ A B : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C₂)
    (hexp : θ * Real.logb 2 C₂ ≤ 1 / 100) (hA : 0 ≤ A) (t : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℕ,
      (W : ℝ) ≤ B * (n : ℝ) ^ (1 / 4 : ℝ) * (n.log2 + 1 : ℝ) ^ t →
      A * C₂ ^ blockCount θ n * (W + 1 : ℝ) ≤ (n : ℝ) ^ (3 / 10 : ℝ) ∧
      A * C₂ ^ blockCount θ n * (W + 1 : ℝ) ≤ (n : ℝ) ^ (2 / 5 : ℝ) := by
  have hmain := eventually_absorb_polylog (A * (B + 1)) t
    (show (1/100 + 1/4 : ℝ) < 3/10 by norm_num) zero_lt_one
  filter_upwards [hmain, eventually_ge_atTop 1] with n hmain hn
  intro W hW
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hg : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (n.log2 + 1 : ℝ) ^ t :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hn1 (by norm_num))
      (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n.log2]))
  have hw : (W + 1 : ℝ) ≤ (B + 1) * (n : ℝ) ^ (1/4 : ℝ) * (n.log2 + 1 : ℝ) ^ t := by
    calc _ ≤ B * (n : ℝ) ^ (1/4 : ℝ) * (n.log2 + 1 : ℝ) ^ t +
              (n : ℝ) ^ (1/4 : ℝ) * (n.log2 + 1 : ℝ) ^ t := add_le_add hW hg
         _ = _ := by ring
  have hlen : A * C₂ ^ blockCount θ n * (W + 1 : ℝ) ≤ (n : ℝ) ^ (3/10 : ℝ) := calc
    _ ≤ A * (n : ℝ) ^ (1/100 : ℝ) * ((B + 1) * (n : ℝ) ^ (1/4 : ℝ) * (n.log2 + 1 : ℝ) ^ t) := by
      gcongr; exact history_pow_blockCount_le hC hθ hn hexp
    _ = A * (B + 1) * (n : ℝ) ^ (1/100 + 1/4 : ℝ) * (n.log2 + 1 : ℝ) ^ t := by
      rw [Real.rpow_add (zero_lt_one.trans_le hn1)]; ring
    _ ≤ _ := by simpa only [one_mul] using hmain
  exact ⟨hlen, hlen.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))⟩

/-- Fetching the incident bits and history descriptors at one final vertex fits
in a live bucket. The fixed number of counter updates may be included in `A`. -/
theorem eventually_burst_le {δ : ℝ} (hδ : δ ≤ 1 / 2) (A : ℝ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      A * ((n : ℝ) ^ (3/10 : ℝ) + (n : ℝ) ^ (1/100 : ℝ) * (n.log2 + 1 : ℝ) ^ k) ≤
        (n : ℝ) ^ (1/2 : ℝ) ∧ (n : ℝ) ^ (1/2 : ℝ) ≤ liveBucket δ n := by
  have h₁ := eventually_absorb_polylog A 0 (show (3/10 : ℝ) < 1/2 by norm_num)
    (show (0 : ℝ) < 1/2 by norm_num)
  have h₂ := eventually_absorb_polylog A k (show (1/100 : ℝ) < 1/2 by norm_num)
    (show (0 : ℝ) < 1/2 by norm_num)
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with n ha hb hn
  simp only [pow_zero, mul_one] at ha
  constructor
  · linarith only [ha, hb]
  · exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)).trans
      (liveBucket_bounds (by linarith) hn).1

/-- With `R ≥ n^5` the total increment from at most `P n^0.01` map occurrences
of degree at most `n^0.4` fits strictly below `R²`, the limit of a `2r`-bit counter. -/
theorem eventually_counter_lt (A : ℝ) (s : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ R P : ℕ, n ^ 5 ≤ R →
      (P : ℝ) ≤ A * R * (n : ℝ) ^ (3/4 : ℝ) * (n.log2 + 1 : ℝ) ^ s →
      (P : ℝ) * (n : ℝ) ^ (1/100 : ℝ) * (n : ℝ) ^ (2/5 : ℝ) < (R : ℝ) ^ 2 := by
  have hsmall := eventually_absorb_polylog A s
    (show (3/4 + 1/100 + 2/5 : ℝ) < 4 by norm_num) zero_lt_one
  filter_upwards [hsmall, eventually_ge_atTop 2] with n hsmall hn
  intro R P hR hP
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast hn
  have hR' : (n : ℝ)^5 ≤ R := by exact_mod_cast hR
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans hn1
  have hpos : 0 < (R : ℝ) := (pow_pos hnpos 5).trans_le hR'
  calc
    _ ≤ (A * R * (n : ℝ) ^ (3/4 : ℝ) * (n.log2 + 1 : ℝ) ^ s) *
        (n : ℝ) ^ (1/100 : ℝ) * (n : ℝ) ^ (2/5 : ℝ) := by gcongr
    _ = (R : ℝ) * (A * (n : ℝ) ^ (3/4 + 1/100 + 2/5 : ℝ) * (n.log2 + 1 : ℝ) ^ s) := by
      rw [Real.rpow_add hnpos, Real.rpow_add hnpos]; ring
    _ ≤ (R : ℝ) * (n : ℝ) ^ (4 : ℕ) := by gcongr; simpa using hsmall
    _ < (R : ℝ) * (n : ℝ) ^ (5 : ℕ) :=
      mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hn1 (by decide)) hpos
    _ ≤ _ := by rw [pow_two]; gcongr

end Compression

end VPVNP
end Computability
end OAI
