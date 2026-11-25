import OAI.ThreeFlat.ExpanderParameters
import OAI.ThreeFlat.ExpanderCloudIteration
import OAI.ThreeFlat.ExpanderRounding

namespace OAI
/-! # Amplification of dimension-independent sparse inner kernels

When a symmetric kernel on `D^(d^j)` points has support `K^j * D` and
quadratic Poincaré constant `C * α^j`, with `α < d`, dyadic rounding and
iterated cloud replacement give a common bounded-degree family.
-/

namespace Hierarchy.NonlinearExpanders

open Finset Filter Topology Matrix Computability.VPVNP.SpectralGeometry
open ThreeFlat.Expander
open scoped Classical

universe u v

/-- At arbitrarily late indices, the factor `d^j` absorbs both terms in
the bound for the graph of ports. -/
private theorem amplification_index {d : ℕ} (hd : 2 ≤ d) {α C : ℝ} (hα : 0 < α) (hαd : α < d)
    (_hC : 0 ≤ C) (j₀ : ℕ) :
    ∃ j ≥ j₀, 3456 * max 1 (C * α^j) ≤ (d : ℝ)^j / 8 := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hd1 : 1 < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
  have decay (a c : ℝ) (ha : 0 ≤ a) (had : a < d) :
      ∀ᶠ j : ℕ in atTop, 3456 * (c * a^j) ≤ (d : ℝ)^j / 8 := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha hdpos.le)
      ((div_lt_one hdpos).mpr had)
    have hlim : Tendsto (fun j : ℕ => (27648*c) * (a/d)^j) atTop (𝓝 0) := by
      simpa using hp.const_mul (27648*c)
    filter_upwards [hlim.eventually_lt_const (by norm_num : (0:ℝ) < 1)] with j hj
    have hsmall : (27648 * c * a^j) / (d:ℝ)^j < 1 := by
      simpa only [div_pow, ← mul_div_assoc] using hj
    have hlt := (div_lt_one (by positivity : (0:ℝ) < (d:ℝ)^j)).mp hsmall
    linarith
  have both : ∀ᶠ j : ℕ in atTop,
      j₀ ≤ j ∧ 3456 * max 1 (C * α^j) ≤ (d:ℝ)^j / 8 := by
    filter_upwards [eventually_ge_atTop j₀, decay 1 1 zero_le_one hd1,
      decay α C hα.le hαd] with j hj hone hpow
    refine ⟨hj, ?_⟩
    rcases le_total 1 (C * α^j) with h | h
    · rwa [max_eq_right h]
    · simpa [max_eq_left h] using hone
  exact both.exists

/-- Choose the sparse kernel's dimension, its power-of-two degree, and an even
dyadic time for which the cloud matching has integral multiplicities. Both
iteration depth and base dimension may be chosen above prescribed thresholds. -/
private theorem amplification_parameters {d K : ℕ} (hd : 2 ≤ d) (hK : 0 < K) {α C : ℝ}
    (hα : 0 < α) (hαd : α < d) (hC : 0 ≤ C) (j₀ n₀ : ℕ) :
    ∃ j ≥ j₀, ∃ n ≥ n₀, ∃ a b : ℕ,
      let D : ℕ := 2^n
      let Q := D^(d^j)
      let t : ℕ := 2*2^a
      let h : ℕ := 2^b
      2*K^j*D ≤ h ∧ h ≤ 4*K^j*D ∧ t*(4*h)^t ∣ Q ∧
        1728 * max 1 (C * α^j) / (t : ℝ) ≤ 1/2 := by
  obtain ⟨j, hj, hratio⟩ := amplification_index hd hα hαd hC (max j₀ 2)
  have hj₂ : 2 ≤ j := (le_max_right _ _).trans hj
  let L : ℕ := d^j
  have hL : 4 ≤ L := calc
    4 = (2:ℕ)^2 := by decide
    _ ≤ d^2 := Nat.pow_le_pow_left hd 2
    _ ≤ d^j := Nat.pow_le_pow_right (by omega) hj₂
  have hlog : 2 ≤ L.log2 := (Nat.le_log2 (by omega)).mpr (by simpa using hL)
  let a := L.log2 - 2
  let t : ℕ := 2*2^a
  have ht : 0 < t := by dsimp [t]; positivity
  have htPow : t = 2^(a+1) := by simp [t, pow_succ, Nat.mul_comm]
  have htwice : 2*t = 2^L.log2 := by
    have eqn : a+2 = L.log2 := Nat.sub_add_cancel hlog
    rw [← eqn, pow_add]
    dsimp [t]
    ring
  have htL : t < L := by
    have hbound := Nat.log2_self_le (n := L) (by omega)
    omega
  have hLt : L < 4*t := by
    calc
      _ < 2^(L.log2+1) := Nat.lt_log2_self
      _ = _ := by rw [pow_succ, ← htwice]; ring
  let f : ℕ := K^j
  let m := f.log2 + 2
  have hf : f ≠ 0 := by dsimp [f]; positivity
  have hmlo : 2*f ≤ 2^m := by
    calc
      _ ≤ 2 * 2^(f.log2+1) := Nat.mul_le_mul_left 2 Nat.lt_log2_self.le
      _ = _ := by simp [m, pow_succ, Nat.mul_comm]
  have hmhi : 2^m ≤ 4*f := by
    calc
      _ = 4*2^f.log2 := by simp [m, pow_add, Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left 4 (Nat.log2_self_le hf)
  let n := max n₀ (a+1 + (m+2)*t)
  let b := n+m
  refine ⟨j,(le_max_left _ _).trans hj,n,le_max_left _ _,a,b,?_⟩
  change 2*f*2^n ≤ 2^b ∧ 2^b ≤ 4*f*2^n ∧ t*(4*2^b)^t ∣ (2^n)^(d^j) ∧ _
  have hb : (2:ℕ)^b = 2^m*2^n := by
    change 2^(n+m) = _
    rw [pow_add, Nat.mul_comm]
  refine ⟨by rw [hb]; exact Nat.mul_le_mul_right _ hmlo,
    by rw [hb]; exact Nat.mul_le_mul_right _ hmhi, ?_, ?_⟩
  · have expo : a+1 + (2+b)*t ≤ n*L := by
      calc
        _ = (a+1+(m+2)*t) + n*t := by dsimp [b]; ring
        _ ≤ n + n*t := Nat.add_le_add_right (le_max_right _ _) _
        _ = n*(t+1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left n htL
    have hfour : 4*2^b = (2:ℕ)^(2+b) := by rw [pow_add (2:ℕ) 2 b]; norm_num
    have hin : t*(4*2^b)^t = (2:ℕ)^(a+1+(2+b)*t) := by
      calc
        _ = 2^(a+1) * (2^(2+b))^t := by rw [← htPow, hfour]
        _ = _ := by rw [pow_add (2:ℕ) (a+1) ((2+b)*t), pow_mul (2:ℕ) (2+b) t]
    rw [hin, ← pow_mul]
    exact Nat.pow_dvd_pow 2 expo
  · change 1728 * max 1 (C * α^j) / (t : ℝ) ≤ 1/2
    have hLt' : (d : ℝ)^j < 4 * (t : ℝ) := by
      change d^j < 4*t at hLt
      exact_mod_cast hLt
    apply (div_le_iff₀ (by exact_mod_cast ht : (0:ℝ)<t)).mpr
    linarith


/-- A simultaneous family of sparse inner kernels can be rounded and amplified
to regular multigraphs at unbounded dyadic orders. -/
theorem amplify_sparse_kernels {d K : ℕ} (hd : 2 ≤ d) (hK : 0 < K)
    {α C : ℝ} (hα : 0 < α) (hαd : α < d) (hC : 0 ≤ C)
    {I : Type v} (X : I → Type u) [∀ i, PseudoMetricSpace (X i)] [∀ i, CompleteSpace (X i)]
    (geom : ∀ i, HasCATZeroSegments (X i))
    (kernels : ∀ n j : ℕ, ∃ G : Matrix (Fin ((2^n)^(d^j))) (Fin ((2^n)^(d^j))) ℝ,
      G ∈ rowStochastic ℝ _ ∧ (∀ a b, G a b = G b a) ∧
      (∀ a, (univ.filter fun b => G a b ≠ 0).card ≤ K^j*2^n) ∧
      ∀ i, Bound G (X i) (C*α^j)) :
    ∃ (h : ℕ) (γ : ℝ), 0 < h ∧ 0 ≤ γ ∧
      ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ c : Fin (2^n) → Fin (2^n) → ℕ,
        (∀ a b, c a b = c b a) ∧ (∀ a, ∑ b, c a b = h) ∧
        ∀ i, Bound (transition c h) (X i) γ := by
  classical
  obtain ⟨j, _, n, hn, a, b, lo, _, dvd, slope⟩ :=
    amplification_parameters hd hK hα hαd (C := 2*C) (by positivity) 0 1
  let q : ℕ := (2^n)^(d^j)
  let k : ℕ := 2^a
  let h : ℕ := 2^b
  let β : ℝ := max 1 ((2*C)*α^j)
  have hq : 0 < q := by dsimp [q]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hβ : 1 ≤ β := le_max_left _ _
  have size : 2*(K^j*2^n) ≤ h := by simpa only [Nat.mul_assoc] using lo
  obtain ⟨G, row, sym, supp, inner⟩ := kernels n j
  let c := roundedCounts G h
  have rounded (i : I) : Bound (transition c h) (X i) β := by
    intro x
    apply ((inner i).roundedCounts (mul_nonneg hC (pow_nonneg hα.le _)) hh x).trans
    apply mul_le_mul_of_nonneg_right _ (energy_transition_nonneg c h x)
    rw [←mul_assoc]
    exact le_max_right _ _
  have small : 1728 * β / (2 * (k:ℝ)) ≤ 1/2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using slope
  refine ⟨2*h,3480*β,by omega,mul_nonneg (by norm_num) (by linarith),?_⟩
  intro n₀
  obtain ⟨g, gs, gr, gb⟩ := exists_cloud_expander_family.{u} hh hk hq dvd
    c (roundedCounts_symmetric sym h) (sum_roundedCounts row supp size) hβ small n₀
  have e : q^n₀ = 2^(n * d^j * n₀) := by dsimp [q]; rw [pow_mul, pow_mul]
  have pos : 1 ≤ n * d^j := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  refine ⟨n * d^j * n₀, by simpa using Nat.mul_le_mul_right n₀ pos, ?_⟩
  let f := finCongr e.symm
  exact ⟨fun s t => g (f s) (f t), fun s t => gs _ _,
    fun s => (f.sum_comp (g (f s))).trans (gr _),
    fun i => Bound.transition_reindex f g (gb (X i) (geom i) (rounded i))⟩

end Hierarchy.NonlinearExpanders

end OAI
