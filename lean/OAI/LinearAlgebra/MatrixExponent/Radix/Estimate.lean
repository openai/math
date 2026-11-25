import OAI.LinearAlgebra.MatrixExponent.Radix.Budget
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# From wide records to logarithmic-width tagged permutations

If the wide-record threshold at overhead exponent 1/2 is w^A, set
t = 1/A. Use s = floor(w^t) bits per digit and 2^s records per pack.
Each local call has height 2s+3 and each global call has width at
least 2^s. Both calls cost at most O(w^(t/2)) per payload bit. There
are O(w^(1-t)) passes, yielding the exponent 2-t/2.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix
open Filter

private theorem scales {t : ℝ} (ht : 0 < t) (ht' : t < 1) (B : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∃ s : ℕ, 3 ≤ s ∧ 2 * s ≤ w ∧
      (s : ℝ) ≤ (w : ℝ) ^ t ∧ (w : ℝ) ^ t ≤ 2 * s ∧ w ^ B ≤ 2 ^ s := by
  have hn : Tendsto (fun w : ℕ => (w : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hr := (tendsto_rpow_atTop ht).comp hn
  have he := isLittleO_rpow_exp_pos_mul_atTop ((B : ℝ) / t)
    (by positivity : 0 < Real.log 2 / 2)
  filter_upwards [eventually_ge_atTop 1, hr.eventually_ge_atTop 4,
    ((tendsto_rpow_atTop (sub_pos.mpr ht')).comp hn).eventually_ge_atTop 2,
    hr.eventually he.eventuallyLE] with w hw hl hu hx
  change 4 ≤ (w : ℝ) ^ t at hl
  change 2 ≤ (w : ℝ) ^ (1 - t) at hu
  have hw' : 0 < (w : ℝ) := by exact_mod_cast hw
  let s := ⌊(w : ℝ) ^ t⌋₊
  have hs : (s : ℝ) ≤ (w : ℝ) ^ t := Nat.floor_le (by positivity)
  have hh : (w : ℝ) ^ t < (s : ℝ) + 1 := Nat.lt_floor_add_one _
  have htwo : (w : ℝ) ^ t ≤ 2 * s := by linarith
  refine ⟨s, by exact_mod_cast (show 3 ≤ (s : ℝ) by linarith), ?_, hs, htwo, ?_⟩
  · have h : 2 * (s : ℝ) ≤ w := calc
      _ ≤ (w : ℝ) ^ (1 - t) * (w : ℝ) ^ t := mul_le_mul hu hs (by positivity) (by positivity)
      _ = w := by rw [← Real.rpow_add hw', sub_add_cancel, Real.rpow_one]
    exact_mod_cast h
  · have h : (w : ℝ) ^ B ≤ (2 : ℝ) ^ s := calc
      _ = ((w : ℝ) ^ t) ^ ((B : ℝ) / t) := by
        rw [← Real.rpow_mul hw'.le, mul_div_cancel₀ _ ht.ne', Real.rpow_natCast]
      _ ≤ Real.exp (Real.log 2 / 2 * (w : ℝ) ^ t) := by
        simpa only [Function.comp_apply, Real.norm_of_nonneg
          (by positivity : 0 ≤ ((w : ℝ) ^ t) ^ ((B : ℝ) / t)),
          Real.norm_of_nonneg (Real.exp_nonneg _)] using hx
      _ ≤ Real.exp (s * Real.log 2) := Real.exp_le_exp.mpr (by
        linarith [mul_le_mul_of_nonneg_left htwo (by positivity : 0 ≤ Real.log 2)])
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    exact_mod_cast h

private theorem local_width {s w A : ℕ} {t : ℝ}
    (ht : t * (A : ℝ) = 1) (hs : 3 ≤ s) (hu : (s : ℝ) ≤ (w : ℝ) ^ t) :
    (s + (s + 2) + 1) ^ A ≤ 3 ^ A * w ∧
      ((s + (s + 2) + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤ 3 * (w : ℝ) ^ (t / 2) := by
  have hl : ((s + (s + 2) + 1 : ℕ) : ℝ) ≤ 3 * (w : ℝ) ^ t := by
    have : (3 : ℝ) ≤ s := by exact_mod_cast hs
    push_cast
    linarith
  constructor
  · have hh := pow_le_pow_left₀ (by positivity) hl A
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), ht, Real.rpow_one] at hh
    exact_mod_cast hh
  · calc
      _ ≤ (3 * (w : ℝ) ^ t) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hl (by norm_num)
      _ = (3 : ℝ) ^ (1 / 2 : ℝ) * (w : ℝ) ^ (t / 2) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul (by positivity), mul_one_div]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by positivity)

private theorem pass_bound {q b k w U x y : ℕ} {L : ℝ} (he : q + (b + k) = w + 2)
    (hL : 1 ≤ L) (hx : (x : ℝ) ≤ L * (2 : ℝ) ^ (q + b + 1) * U)
    (hy : (y : ℝ) ≤ L * (2 : ℝ) ^ (b + k + 1) * ((U : ℝ) * 2 ^ q)) :
    (passCost q b k U (U * 2 ^ q) x y : ℝ) ≤ 20000000000 * L * (2 : ℝ) ^ w * U := by
  have h₁ : (2 : ℝ) ^ k * 2 ^ (q + b + 1) = 8 * 2 ^ w := by
    rw [← pow_add, show k + (q + b + 1) = 3 + w by omega, pow_add]; norm_num
  have h₂ : (2 : ℝ) ^ (b + k + 1) * 2 ^ q = 8 * 2 ^ w := by
    rw [← pow_add, show b + k + 1 + q = 3 + w by omega, pow_add]; norm_num
  unfold passCost
  push_cast
  calc
    _ ≤ (2 : ℝ) ^ k * (4 * (L * 2 ^ (q + b + 1) * U) + 10000000 * 2 ^ (q + b + 1) * U) +
        (4 * (L * 2 ^ (b + k + 1) * (U * 2 ^ q)) + 2000000000 * 2 ^ (b + k + 1) * (U * 2 ^ q)) := by gcongr
    _ = (2 ^ k * 2 ^ (q + b + 1)) * (4 * L + 10000000) * U +
        (2 ^ (b + k + 1) * 2 ^ q) * (4 * L + 2000000000) * U := by ring
    _ = 8 * (8 * L + 2010000000) * (2 : ℝ) ^ w * U := by rw [h₁, h₂]; ring
    _ ≤ _ := by
      have : 8 * (8 * L + 2010000000) ≤ 20000000000 * L := by linarith
      gcongr

private theorem budget_bound {w s q b k U V x y : ℕ} {D t : ℝ}
    (hw : 1 ≤ w) (ht : t < 1) (hs : (w : ℝ) ^ t ≤ 2 * s)
    (hp : (passCost q b k U V x y : ℝ) ≤ D * (2 : ℝ) ^ w * w * (w : ℝ) ^ (t / 2)) :
    (budget w s q b k U V x y : ℝ) ≤ (5 * D + 400000) * (2 : ℝ) ^ w * (w : ℝ) ^ (2 - t / 2) := by
  have hw' : 1 ≤ (w : ℝ) := by exact_mod_cast hw
  have hw0 : 0 < (w : ℝ) := zero_lt_one.trans_le hw'
  have hdiv : ((2 * w / s : ℕ) : ℝ) * s ≤ 2 * w := by exact_mod_cast Nat.div_mul_le_self (2 * w) s
  have hcnt : ((2 * w / s + 1 : ℕ) : ℝ) ≤ 5 * (w : ℝ) ^ (1 - t) := by
    apply le_of_mul_le_mul_right _ (Real.rpow_pos_of_pos hw0 t)
    rw [mul_assoc, ← Real.rpow_add hw0, sub_add_cancel, Real.rpow_one, Nat.cast_add, Nat.cast_one]
    linarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) (2 * w / s)),
      Real.rpow_le_self_of_one_le hw' ht.le]
  have hsum : (w : ℝ) ^ (1 - t) * w * (w : ℝ) ^ (t / 2) = (w : ℝ) ^ (2 - t / 2) := by
    rw [show (2 : ℝ) - t / 2 = (1 - t + 1) + t / 2 by ring, Real.rpow_add hw0, Real.rpow_add hw0, Real.rpow_one]
  have hl : (w : ℝ) + 1 ≤ 2 * (w : ℝ) ^ (2 - t / 2) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hw' (show 1 ≤ 2 - t / 2 by linarith)
    rw [Real.rpow_one] at hh
    linarith
  unfold budget
  rw [Nat.cast_add, Nat.cast_mul]
  calc
    _ ≤ 5 * (w : ℝ) ^ (1 - t) * (D * (2 : ℝ) ^ w * w * (w : ℝ) ^ (t / 2)) +
        200000 * (2 : ℝ) ^ w * (2 * (w : ℝ) ^ (2 - t / 2)) := by
      apply add_le_add (mul_le_mul hcnt hp (by positivity) (by positivity))
      push_cast
      gcongr
    _ = _ := by rw [← hsum]; ring

private theorem extend_bound {F : Type} [Field F] {C p : ℝ} (hp : 0 ≤ p)
    (h : ∀ᶠ w : ℕ in atTop, ∃ v, Tag F w w v ∧ (v : ℝ) ≤ C * (2 : ℝ) ^ w * (w : ℝ) ^ p) :
    Lookup.ShortTag F p := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  choose v hv using tag_exists F
  let D := max C (∑ i ∈ Finset.range N, (v i : ℝ))
  refine ⟨D, fun w hw => ?_⟩
  by_cases h : N ≤ w
  · obtain ⟨m, hm, hm'⟩ := hN w h
    exact ⟨m, hm, hm'.trans (by gcongr; exact le_max_left _ _)⟩
  have hh : (v w : ℝ) ≤ D :=
    (Finset.single_le_sum (f := fun i => (v i : ℝ)) (fun i _ => by positivity)
      (Finset.mem_range.mpr (lt_of_not_ge h))).trans (le_max_right _ _)
  refine ⟨_, hv w, ?_⟩
  have hD : 0 ≤ D := (Nat.cast_nonneg _).trans hh
  calc
    (v w : ℝ) ≤ D * 1 * 1 := by simpa using hh
    _ ≤ D * (2 : ℝ) ^ w * (w : ℝ) ^ p :=
      mul_le_mul (mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) hD)
        (Real.one_le_rpow (by exact_mod_cast hw) hp) (by norm_num) (by positivity)

theorem short_of_wide {F : Type} [Field F]
    (wide : WideTag F) : ∃ p : ℝ, 1 < p ∧ p < 2 ∧ Lookup.ShortTag F p := by
  obtain ⟨A, hA, C, hC⟩ := wide (1 / 2) (by norm_num)
  have hA' : 1 < (A : ℝ) := by exact_mod_cast hA
  let t := 1 / (A : ℝ)
  have ht : 0 < t := by unfold t; positivity
  have ht' : t < 1 := (div_lt_one (by linarith)).mpr hA'
  have htA : t * (A : ℝ) = 1 := div_mul_cancel₀ _ (by linarith)
  obtain ⟨B, _, E, hE⟩ := wide (t / 2) (by linarith)
  let D := max 1 (max C E)
  have hD : 1 ≤ D := le_max_left _ _
  have hCD : C ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hED : E ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  let T : ℕ := 30 * 3 ^ A
  let R : ℝ := 20000000000 * 3 * D * T
  refine ⟨2 - t / 2, by linarith, by linarith, ?_⟩
  apply extend_bound (C := 5 * R + 400000) (by linarith)
  filter_upwards [scales ht ht' B] with w h
  obtain ⟨s, hs, hs2, hsu, hsl, hexp⟩ := h
  let b := s + 2
  let k := w - 2 * s
  let U := T * w
  have he : s + (b + k) = w + 2 := by omega
  have hg : b + k + 1 ≤ w := by omega
  have hw : 1 ≤ w := by omega
  have hU : 10 * (w + 2) ≤ U := calc
    _ ≤ 30 * w := by omega
    _ ≤ (30 * 3 ^ A) * w := Nat.mul_le_mul_right w (Nat.le_mul_of_pos_right 30 (by positivity))
  obtain ⟨hwidth, hlocal⟩ := local_width htA hs hsu
  obtain ⟨x, hx, hx'⟩ := hC (s + b + 1) U (by omega)
    (hwidth.trans (Nat.mul_le_mul_right w (Nat.le_mul_of_pos_left _ (by decide))))
  obtain ⟨y, hy, hy'⟩ := hE (b + k + 1) (U * 2 ^ s) (by omega)
    ((Nat.pow_le_pow_left hg B).trans (hexp.trans (Nat.le_mul_of_pos_left _ (by omega))))
  obtain ⟨v, hv, hv'⟩ := budget_net F w s s b k U (U * 2 ^ s) x y (by omega) le_rfl he hU
    (Nat.mul_le_mul_right _ hU) hx hy
  refine ⟨v, hv', (Nat.cast_le.mpr hv).trans (budget_bound hw ht' hsl ?_)⟩
  have hρ : 1 ≤ (w : ℝ) ^ (t / 2) := Real.one_le_rpow (by exact_mod_cast hw) (by linarith)
  have hglobal : ((b + k + 1 : ℕ) : ℝ) ^ (t / 2) ≤ 3 * (w : ℝ) ^ (t / 2) := by
    have hh : ((b + k + 1 : ℕ) : ℝ) ^ (t / 2) ≤ (w : ℝ) ^ (t / 2) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hg) (by linarith)
    linarith
  let L := 3 * D * (w : ℝ) ^ (t / 2)
  have hL : 1 ≤ L := by unfold L; nlinarith
  have hx'' : (x : ℝ) ≤ L * (2 : ℝ) ^ (s + b + 1) * U := calc
    _ ≤ _ := hx'
    _ ≤ D * (2 : ℝ) ^ (s + b + 1) * U * (3 * (w : ℝ) ^ (t / 2)) := by gcongr
    _ = _ := by unfold L; ring
  have hy'' : (y : ℝ) ≤ L * (2 : ℝ) ^ (b + k + 1) * ((U : ℝ) * 2 ^ s) := calc
    _ ≤ _ := hy'
    _ ≤ D * (2 : ℝ) ^ (b + k + 1) * (U * 2 ^ s : ℕ) * (3 * (w : ℝ) ^ (t / 2)) := by gcongr
    _ = _ := by unfold L; push_cast; ring
  refine (pass_bound he hL hx'' hy'').trans_eq ?_
  unfold L U R
  rw [Nat.cast_mul]
  ring

end OAI.LinearAlgebra.MatrixExponent.Radix
