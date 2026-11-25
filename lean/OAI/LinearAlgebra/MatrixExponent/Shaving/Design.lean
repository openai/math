import OAI.LinearAlgebra.MatrixExponent.Shaving.FieldStage
import Mathlib.Analysis.SpecificLimits.Normed

section
/-!
# Iteration budgets

Work with exponents of two throughout. A grouping of `2^r` blocks
consumes exactly `r` bits of the block index. After `s j` such
groupings there are `2^(M l)` blocks, each descended from stacks
of `2^t` independent copies.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Shaving
open Filter

private theorem round_up (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (2 : ℝ) ^ (x * k) ≤ (2 : ℝ) ^ (k*⌈x⌉₊) ∧ (2 : ℝ) ^ (k*⌈x⌉₊) ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ (x * k) := by
  rw [← Real.rpow_natCast 2 (k*⌈x⌉₊), Nat.cast_mul, ← Real.rpow_natCast 2 k,
    ← Real.rpow_add (by norm_num)]
  have lo := mul_le_mul_of_nonneg_right (Nat.le_ceil x) (Nat.cast_nonneg k)
  have hi := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hx).le (Nat.cast_nonneg k)
  constructor <;> exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- Set `G=2^g`, `q=2^p`. Choose a round count `j`, stack exponent `t`
and height exponent `l`. The final bound covers the complete replication
cost with group exponent `c(j+1)`, uniformly before seeing any input. -/
theorem stage_parameters (g p c s M : ℕ) (hg : 0 < g) (a b δ ξ : ℝ)
    (ha : 0 < a) (ha' : a ≤ 1) (hb : 0 < b) (hb' : b ≤ 1)
    (hp : (p : ℝ) ≤ g * (1 + δ / 3)) (hξ : 0 < ξ) :
    ∀ᶠ n : ℕ in atTop,
      let h : ℝ := Nat.clog 2 n
      ∃ j t l : ℕ, 0 < j ∧ h ≤ (2 : ℝ) ^ l ∧ (2 : ℝ) ^ l ≤ 2 * h ∧
        h ^ b ≤ (2 : ℝ) ^ t ∧ (2 : ℝ) ^ t ≤ 2 * h ^ b ∧
        h ^ a ≤ (2 : ℝ) ^ (g * j) ∧ (2 : ℝ) ^ (g * j) ≤ (2 : ℝ) ^ g * h ^ a ∧
        (2 : ℝ) ^ (p * j) ≤ (2 : ℝ) ^ p * h ^ ((1 + δ / 3) * a) ∧
        (2 : ℝ) ^ (c * (j + 1)) ≤ (2 : ℝ) ^ (2 * c) * h ^ (c * a) ∧
        (2 : ℝ) ^ (t + M * l + c * (j + 1) * (s * j)) ≤ (n : ℝ) ^ ξ := by
  let K := 2 + 1 / Real.log 2
  let C := (1 + M + c * s : ℝ) * K ^ 2
  have hlog : 0 < Real.log 2 := by positivity
  have hk : 1 ≤ K := by unfold K; linarith [one_div_pos.mpr hlog]
  filter_upwards [tendsto_height.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_height).eventually_ge_atTop 1,
    tendsto_height.eventually (cost_le C (by norm_num : (0 : ℝ) < 1 / 2)),
    batch_le hξ] with n hh hl hpoly hbatch
  let h : ℝ := Nat.clog 2 n
  change 1 < h at hh
  change 1 ≤ Real.log h at hl
  let x := Real.log h / Real.log 2
  have hx : 0 < x := div_pos (by linarith) hlog
  have he : (2 : ℝ) ^ x = h := by
    unfold x
    rw [Real.rpow_def_of_pos (by norm_num), mul_div_cancel₀ _ hlog.ne', Real.exp_log (by linarith)]
  have bound (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
      h ^ (u * k) ≤ (2 : ℝ) ^ (k*⌈x * u⌉₊) ∧ (2 : ℝ) ^ (k*⌈x * u⌉₊) ≤ (2 : ℝ) ^ k * h ^ (u * k) := by
    rw [← he, ← Real.rpow_mul (by norm_num), ← mul_assoc]
    exact round_up _ (mul_nonneg hx.le hu) k
  let v := a / g
  have hgr : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hv : 0 < v := div_pos ha hgr
  have hva : v ≤ a := div_le_self ha.le (by exact_mod_cast hg)
  have hvg : v * g = a := div_mul_cancel₀ _ hgr.ne'
  let l := ⌈x * 1⌉₊
  let t := ⌈x * b⌉₊
  let j := ⌈x * v⌉₊
  have hj : 0 < j := Nat.ceil_pos.mpr (mul_pos hx hv)
  have hL : h ≤ (2 : ℝ) ^ l ∧ (2 : ℝ) ^ l ≤ 2 * h := by simpa [l] using bound 1 zero_le_one 1
  have hT : h ^ b ≤ (2 : ℝ) ^ t ∧ (2 : ℝ) ^ t ≤ 2 * h ^ b := by simpa [t] using bound b hb.le 1
  have hG := bound v hv.le g
  rw [hvg] at hG
  refine ⟨j, t, l, hj, hL.1, hL.2, hT.1, hT.2, hG.1, hG.2, ?_, ?_, ?_⟩
  · refine (bound v hv.le p).2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hh.le ?_) (by positivity))
    have := mul_le_mul_of_nonneg_left hp hv.le
    rwa [← mul_assoc, hvg, mul_comm a] at this
  · have hc : v * c ≤ (c : ℝ) * a := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hva (Nat.cast_nonneg _)
    calc
      _ = (2 : ℝ) ^ c * (2 : ℝ) ^ (c * j) := by rw [← pow_add]; congr 1; ring
      _ ≤ (2 : ℝ) ^ c * ((2 : ℝ) ^ c * h ^ ((c : ℝ) * a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (bound v hv.le c).2.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hh.le hc) (by positivity))
      _ = _ := by rw [← mul_assoc, ← pow_add, ← two_mul]
  · let H := K * Real.log h
    have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hk hl
    have small (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) : (⌈x * u⌉₊:ℝ) + 1 ≤ H := by
      have := Nat.ceil_lt_add_one (mul_nonneg hx.le hu)
      have hxu := mul_le_mul_of_nonneg_left hu' hx.le
      have hH' : H = 2 * Real.log h + x := by unfold H K x; ring
      linarith
    have hsq : H ≤ H ^ 2 := by nlinarith
    have ht' : (t : ℝ) ≤ H ^ 2 := by linarith [small b hb.le hb']
    have hl' : (l : ℝ) ≤ H ^ 2 := by linarith [small 1 zero_le_one le_rfl]
    have hj' : (j : ℝ) + 1 ≤ H := small v hv.le (hva.trans ha')
    apply hbatch
    refine le_trans ?_ hpoly
    push_cast
    change (t : ℝ) + M * l + c * (j + 1) * (s * j) ≤ C * (Real.log h) ^ 2
    calc
      _ ≤ H ^ 2 + M * H ^ 2 + c * H * (s * H) := by gcongr; linarith
      _ = _ := by unfold C H; ring

/-- Choose the exponent controlling all group sizes before the height
is known. The factor `C^(j+1)` covers growth in host occurrences. -/
theorem group_exponent (C G q ε : ℝ) (hC : 1 ≤ C) (hG : 1 ≤ G) (hq : 1 ≤ q)
    (hε : 0 < ε) (r₀ : ℝ) :
    ∃ c : ℕ, ∀ i j : ℕ, i ≤ j →
      r₀ ≤ (2 : ℝ) ^ (c * (j + 1)) ∧ C ^ (j + 1) * (q * G) ^ i ≤ ε * (2 : ℝ) ^ (c * (j + 1)) := by
  let B := C * (q * G)
  have hqG := one_le_mul_of_one_le_of_one_le hq hG
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hC hqG
  have ht := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  obtain ⟨c, hc, hr, hd⟩ := ((ht.eventually_ge_atTop B).and
    ((ht.eventually_ge_atTop r₀).and (ht.eventually_ge_atTop (B / ε)))).exists
  refine ⟨c, fun i j hij => ?_⟩
  rw [pow_mul]
  have hb := hB.trans hc
  constructor
  · exact hr.trans (by simpa using pow_le_pow_right₀ hb (by omega : 1 ≤ j + 1))
  · calc
      _ ≤ B ^ (j + 1) := by
        rw [show B = C * (q * G) by rfl, mul_pow C]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hqG (hij.trans (Nat.le_succ _))) (by positivity)
      _ = B ^ j * B := pow_succ _ _
      _ ≤ ((2 : ℝ) ^ c) ^ j * ((2 : ℝ) ^ c * ε) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hc j)
          ((div_le_iff₀ hε).mp hd) (by positivity) (by positivity)
      _ = _ := by rw [pow_succ]; ring

/-- Check both admission conditions of round `i`. Here `A` counts all
allocated occurrences at the current grouping step and `T,L` are the
initial scale and total width budget. -/
theorem iteration_slack {D G q C L T A m d h a e ε r : ℝ} {i j : ℕ}
    (hD : 0 < D) (hG : 1 ≤ G) (hq : 1 ≤ q) (hh : 0 < h)
    (dr : 0 < r) (hm : 0 ≤ m) (hd : 0 ≤ d) (hij : i ≤ j)
    (initial : m * d ≤ L) (allocated : A * T ≤ C ^ (j + 1) * L)
    (steps : G ^ j ≤ G * h ^ a) (height : D * G ≤ h ^ a)
    (group : C ^ (j + 1) * (q * G) ^ i ≤ ε * r) (exterior : e ≤ m * h ^ (-(2 * a))) :
    A * (T * q ^ i) / r ≤ ε * (L / G ^ i) ∧ e * d ≤ (L / G ^ i) / D := by
  have hL : 0 ≤ L := (mul_nonneg hm hd).trans initial
  have hg : 0 < G ^ i := pow_pos (zero_lt_one.trans_le hG) _
  constructor
  · rw [← mul_div_assoc, div_le_div_iff₀ dr hg]
    calc
      _ = (A * T) * (q * G) ^ i := by rw [mul_pow]; ring
      _ ≤ (C ^ (j + 1) * L) * (q * G) ^ i := mul_le_mul_of_nonneg_right allocated (by positivity)
      _ = L * (C ^ (j + 1) * (q * G) ^ i) := by ring
      _ ≤ L * (ε * r) := mul_le_mul_of_nonneg_left group hL
      _ = _ := by ring
  · rw [le_div_iff₀ hD, le_div_iff₀ hg]
    have hcap : D * G ^ i ≤ h ^ (2 * a) := calc
      _ ≤ D * (G * h ^ a) := mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hG hij).trans steps) hD.le
      _ ≤ h ^ a * h ^ a := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right height (by positivity)
      _ = _ := by rw [← Real.rpow_add hh, ← two_mul]
    calc
      _ = (e * d) * (D * G ^ i) := by ring
      _ ≤ (m * h ^ (-(2 * a)) * d) * h ^ (2 * a) :=
        mul_le_mul (mul_le_mul_of_nonneg_right exterior hd) hcap (by positivity) (by positivity)
      _ = m * d := by rw [mul_right_comm m, mul_assoc, ← Real.rpow_add hh]; simp
      _ ≤ _ := initial

end OAI.LinearAlgebra.MatrixExponent.Shaving
end

section
/-!
# Volume and arity at the end of a stage

The iteration saves `h^a` in total width. Split the logarithmic slack
`aδ` between the descriptions, the cost of realizing the transcript, and
the remaining constant factors.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Shaving
open Filter

/-- Any fixed power of the logarithm fits in any positive power budget. -/
theorem polylog_le (C : ℝ) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in atTop, C * (Real.log h) ^ r ≤ h ^ ε := by
  have hl := (isLittleO_log_rpow_rpow_atTop r hε).const_mul_left C
  filter_upwards [eventually_ge_atTop 0, hl.eventuallyLE] with h hh ht
  rw [Real.rpow_natCast, Real.norm_of_nonneg (Real.rpow_nonneg hh ε)] at ht
  exact (le_abs_self _).trans ht

/-- Quasipolynomial work in the height uses at most `1/h` of a linear
input-size budget. -/
theorem assembly_remainder (C : ℝ) (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, let h : ℝ := Nat.clog 2 n
      (2 : ℝ) ^ (C * (Real.log h) ^ r) * h ≤ n := by
  filter_upwards [tendsto_height.eventually_gt_atTop 1,
    tendsto_height.eventually (polylog_le (3*|C|) r (by norm_num : (0 : ℝ) < 1 / 2)),
    tendsto_height.eventually (polylog_le (3 / Real.log 2) 1 (by norm_num : (0 : ℝ) < 1 / 2)),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) |>.comp tendsto_height).eventually_ge_atTop 3,
    batch_le (by norm_num : (0 : ℝ) < 1)] with n hh h₁ h₂ h₃ hb
  let h : ℝ := Nat.clog 2 n
  change 1 < h at hh
  change 3*|C| * (Real.log h) ^ r ≤ h ^ (1 / 2 : ℝ) at h₁
  change 3 / Real.log 2 * (Real.log h) ^ 1 ≤ h ^ (1 / 2 : ℝ) at h₂
  change 3 ≤ h ^ (1 / 2 : ℝ) at h₃
  let x := |C| * (Real.log h) ^ r + Real.log h / Real.log 2
  have hlog : 0 < Real.log h := Real.log_pos hh
  have hx : 0 ≤ x := by unfold x; positivity
  have he : (2 : ℝ) ^ (Real.log h / Real.log 2) = h := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_div_cancel₀ _ (by positivity),
      Real.exp_log (by linarith)]
  have hsmall : (⌈x⌉₊:ℝ) ≤ h ^ (1 / 2 : ℝ) := by
    refine (Nat.ceil_lt_add_one hx).le.trans ?_
    unfold x
    simp only [pow_one, div_eq_mul_inv] at h₂ ⊢
    linarith
  calc
    _ ≤ (2 : ℝ) ^ x := by
      unfold x
      rw [Real.rpow_add (by norm_num), he]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))) (by positivity)
    _ ≤ (2 : ℝ)^⌈x⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ ≤ _ := by simpa only [Real.rpow_one] using hb _ hsmall

/-- `P` is the processor count, `V` the record volume, `m` the input size,
`S` the initial block count and `d` the replication factor. The five volume
terms are common work, short control, terminal payloads, exposed bits,
and the subpolynomial additive error. -/
theorem assembly_saving {h m S d K P V size arity a b C C₀ C₂ M δ : ℝ}
    (hh : 1 ≤ h) (hm : 0 ≤ m) (hS : 0 ≤ S) (hd : S * h ^ b ≤ d)
    (hK : 0 ≤ K) (ha : 0 ≤ a) (ha' : a ≤ 1) (hδ : 0 < δ)
    (hC : C * a + 2 * a ≤ b) (h₀ : C₀ ≤ M) (h₂ : C₂ ≤ M) :
    let τ := a * δ / 3
    7 * K ≤ h ^ τ →
    P ≤ m * S * h ^ (C * a + τ) / h ^ M →
    V ≤ P * h ^ C₂ + m * S * h ^ (C * a + τ) + m * d * h ^ (-a + τ) + m * d * h ^ (-(2 * a) + τ) + m * d / h →
    size ≤ K * (P * h ^ C₀ + V * h ^ τ + m * d / h) →
    arity ≤ K * (h ^ (b + (1 + δ / 3) * a) + h ^ (C * a + τ)) →
    size ≤ m * d * h ^ (-((1 - δ) * a)) ∧ arity ≤ h ^ (b + (1 + δ) * a) := by
  intro τ large processors volume work key
  have ht : 0 ≤ τ := by unfold τ; positivity
  have hh' : 0 < h := zero_lt_one.trans_le hh
  have hd' : 0 ≤ d := (mul_nonneg hS (by positivity)).trans hd
  let z := m * d * h ^ (-a + τ)
  have hz : 0 ≤ z := by unfold z; positivity
  have ctrl : m * S * h ^ (C * a + τ) ≤ z := calc
    _ ≤ m * S * h ^ (b + (-a + τ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hh (by linarith)) (by positivity)
    _ = m * (S * h ^ b) * h ^ (-a + τ) := by rw [Real.rpow_add hh']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hm) (by positivity)
  have setup (r : ℝ) (hr : r ≤ M) : P * h ^ r ≤ z := calc
    _ ≤ (m * S * h ^ (C * a + τ) / h ^ M) * h ^ r := mul_le_mul_of_nonneg_right processors (by positivity)
    _ ≤ (m * S * h ^ (C * a + τ) / h ^ M) * h ^ M :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hh hr) (by positivity)
    _ ≤ _ := by rw [div_mul_cancel₀ _ (by positivity)]; exact ctrl
  have ext : m * d * h ^ (-(2 * a) + τ) ≤ z :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hh (by linarith)) (by positivity)
  have rem : m * d / h ≤ z := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hh (by linarith)) (by positivity)
  have hV : V ≤ 5 * z := by
    change V ≤ _ + _ + z + _ + _ at volume
    linarith [setup C₂ h₂]
  have hτ : 1 ≤ h ^ τ := Real.one_le_rpow hh ht
  constructor
  · calc
      _ ≤ K * (P * h ^ C₀ + V * h ^ τ + m * d / h) := work
      _ ≤ 7 * K * z * h ^ τ := by
        have hvol := mul_le_mul_of_nonneg_right hV (by positivity : 0 ≤ h ^ τ)
        have hx := le_mul_of_one_le_right hz hτ
        have := mul_le_mul_of_nonneg_left
          (show P * h ^ C₀ + V * h ^ τ + m * d / h ≤ 7 * z * h ^ τ by linarith [setup C₀ h₀]) hK
        linarith
      _ ≤ h ^ τ * z * h ^ τ := by gcongr
      _ = _ := by
        rw [show -((1 - δ) * a) = τ + (-a + τ) + τ by unfold τ; ring,
          Real.rpow_add hh', Real.rpow_add hh']
        unfold z; ring
  · let e := b + (1 + δ / 3) * a
    have hx : C * a + τ ≤ e := by unfold e τ; linarith
    have hinc : h ^ (C * a + τ) ≤ h ^ e := Real.rpow_le_rpow_of_exponent_le hh hx
    calc
      _ ≤ K * (h ^ e + h ^ (C * a + τ)) := key
      _ ≤ K * (h ^ e + h ^ e) := by gcongr
      _ = (2 * K) * h ^ e := by ring
      _ ≤ h ^ τ * h ^ e := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := by
        rw [← Real.rpow_add hh']
        apply Real.rpow_le_rpow_of_exponent_le hh
        unfold e τ at *
        linarith

end OAI.LinearAlgebra.MatrixExponent.Shaving
end

section
/-!
# Dyadic parameters of one round

Write `D = 2^d`, `G = 2^g`, `q = 2^p`. Run exactly `2g` beats.
Any fixed power of the logarithm of `D` fits into both `G` and `q/G`.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Shaving
open Filter

private theorem absorbs_power (K : ℝ) (r : ℕ) :
    ∀ᶠ t : ℕ in atTop, K * (t : ℝ) ^ r ≤ (2 : ℝ) ^ t := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) r
    (by norm_num : (1 : ℝ) < 2)).const_mul_left K
  filter_upwards [h.eventuallyLE] with t ht
  exact (le_abs_self _).trans (by simpa using ht)

/-- The beat multiplier and all logarithmic losses are independent of
`D`. The lower cutoff on its logarithm is arbitrary. -/
theorem choose_round {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) (B K : ℝ)
    (hK : 0 ≤ K) (r d₀ : ℕ) :
    ∃ d g p : ℕ, d₀ ≤ d ∧ 0 < g ∧ 100 * g ≤ d ∧
      B ^ (2 * g) ≤ ((2 : ℝ) ^ d) ^ (1 / 100 : ℝ) ∧
      (g : ℝ) * (1 + δ / 4) ≤ p ∧ (p : ℝ) ≤ g * (1 + δ / 3) ∧
      2 * K * (1 + d) ^ r ≤ (2 : ℝ) ^ g ∧ 2 * K * (1 + d) ^ r * (2 : ℝ) ^ g ≤ (2 : ℝ) ^ p := by
  let e := ⌈3 / δ⌉₊
  have he : 0 < e := Nat.ceil_pos.mpr (by positivity)
  have he₁ : 3 ≤ (e : ℝ) * δ := (div_le_iff₀ hδ).mp (Nat.le_ceil _)
  have he₂ : (e : ℝ) * δ ≤ 4 := by
    have := mul_le_mul_of_nonneg_right
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ 3 / δ)).le hδ.le
    rw [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul] at this
    exact this.trans (by linarith)
  obtain ⟨b, hb, hB⟩ := ((eventually_gt_atTop 0).and
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop (B ^ 2))).exists
  let f := 100 * b * e
  obtain ⟨t, ht, hpoly⟩ := ((eventually_gt_atTop d₀).and
    (absorbs_power (2 * K * (1 + f) ^ r) r)).exists
  let g := e * t
  let d := f * t
  let p := g + t
  have htg : t ≤ g := Nat.le_mul_of_pos_left _ he
  have hd : d = 100 * (b * g) := by simp [d, f, g, mul_assoc]
  have hgd : 100 * g ≤ d := by rw [hd]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hb)
  have hc : 2 * K * (1 + d) ^ r ≤ (2 : ℝ) ^ t := by
    refine le_trans ?_ hpoly
    rw [mul_assoc (2 * K), ← mul_pow]
    gcongr
    have : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    simp only [d, Nat.cast_mul]
    linarith
  refine ⟨d, g, p, by omega, by omega, hgd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_mul]
    calc
      _ ≤ ((2 : ℝ) ^ b) ^ g := pow_le_pow_left₀ (sq_nonneg B) hB _
      _ = _ := by
        rw [← pow_mul, ← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast 2 (b * g), hd]
        congr 1
        push_cast
        ring
  · have := mul_le_mul_of_nonneg_right he₂ (Nat.cast_nonneg t)
    simp only [p, g, Nat.cast_add, Nat.cast_mul]
    linarith
  · have := mul_le_mul_of_nonneg_right he₁ (Nat.cast_nonneg t)
    simp only [p, g, Nat.cast_add, Nat.cast_mul]
    linarith
  · exact hc.trans (pow_le_pow_right₀ (by norm_num) htg)
  · rw [show p = t + g by simp [p, add_comm], pow_add]
    exact mul_le_mul_of_nonneg_right hc (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Shaving
end
