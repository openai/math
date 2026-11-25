import OAI.Geometry.Hirsch.Asymptotics

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch

theorem pad_excess (poly : Polytope) (reg : poly.sys.Regular)
    {d excess moves : ℕ} (hd : poly.dimension + 3 ≤ d) (hf : poly.facetCount + 2 ≤ excess)
    (hm : 1 ≤ moves) (first last : poly.V) :
    ∃ padded : Polytope, padded.sys.Regular ∧ padded.dimension = d ∧
      padded.facetCount = d + excess ∧ ∃ src dst : padded.V,
        poly.dist moves first last ≤ padded.dist moves src dst := by
  obtain ⟨sim, hs, hsd, hsf⟩ := simplex (d - poly.dimension - 2) (by omega)
  obtain ⟨gon, hg, hgd, hgf⟩ := polygon (excess + poly.dimension - poly.facetCount + 1) (by omega)
  let pad := sim.product gon
  have hp := sim.product_regular gon hs hg
  refine ⟨poly.product pad, poly.product_regular pad reg hp, ?_, ?_, ?_⟩
  · rw [poly.product_dimension pad reg hp, show pad.dimension = _ from sim.product_dimension gon hs hg,
      hsd, hgd]
    omega
  · rw [poly.product_facetCount pad reg hp, show pad.facetCount = _ from sim.product_facetCount gon hs hg,
      hsf, hgf]
    omega
  · let anchor : pad.V := Classical.arbitrary _
    exact ⟨poly.pair pad first anchor, poly.pair pad last anchor,
      poly.product_dist pad reg hp hm (poly.pair pad first anchor) (poly.pair pad last anchor)⟩

theorem excess_of_cap (cap : CapLemma) : ExcessTheorem := by
  intro aa bb ha hb
  obtain ⟨power, hpow⟩ := exists_nat_gt (max aa bb)
  let degree := 4 * power + 2
  obtain ⟨base, hbase, gamma, hg, hseed⟩ := cap degree (by omega) (1/2) (by norm_num) (by norm_num)
  obtain ⟨start, hseed⟩ := eventually_atTop.mp hseed
  have scales := eventually_scale hbase start (lo := 1/4) (hi := 1/3) (by norm_num) (by norm_num)
  have budget := eventually_dominate (lo := (1/3) * 2) (hi := 1) (by norm_num) 8
  obtain ⟨threshold, hth⟩ := eventually_atTop.mp ((eventually_ge_atTop 8).and (scales.and budget))
  refine ⟨1/4, (1/4) * gamma, by norm_num, by positivity, threshold, ?_⟩
  intro d excess hlarge
  let size := min d excess
  obtain ⟨hsize, ⟨height, hh, lower, upper⟩, hbudget⟩ := hth size hlarge
  let scale := base ^ height
  have hs : (1 : ℝ) ≤ size := by exact_mod_cast (show 1 ≤ size by omega)
  have hd : (size : ℝ) ≤ d := Nat.cast_le.mpr (min_le_left _ _)
  have he : (size : ℝ) ≤ excess := Nat.cast_le.mpr (min_le_right _ _)
  have hn : (1 : ℝ) ≤ scale := (Real.one_le_rpow hs (by norm_num)).trans lower
  have hbnd : 8 * (scale : ℝ)^2 ≤ size := by
    rw [Real.rpow_one, Real.rpow_mul (by positivity), Real.rpow_two] at hbudget
    apply le_trans _ hbudget
    gcongr
  have hden : 0 < 2 * (scale : ℝ)^2 := by positivity
  let ratio := excess / (2 * (scale : ℝ)^2)
  let mult := ⌊ratio⌋₊
  have hr : 2 ≤ ratio := (le_div_iff₀ hden).mpr (by linarith)
  have hrpos : 1 ≤ mult := Nat.le_floor (by simpa using (one_le_two.trans hr))
  have hru : (mult : ℝ) * (2 * (scale : ℝ)^2) ≤ excess :=
    (le_div_iff₀ hden).mp (Nat.floor_le (show 0 ≤ ratio by linarith))
  have hrl : (excess : ℝ) ≤ 2 * mult * (2 * (scale : ℝ)^2) := by
    apply (div_le_iff₀ hden).mp
    change ratio ≤ 2 * mult
    have hh' : ratio < (mult : ℝ) + 1 := Nat.lt_floor_add_one ratio
    linarith
  obtain ⟨poly, obj, reg, hdim, hfac, cost⟩ := hseed height hh mult hrpos
  have hsq : ∀ exp : ℝ, exp ≤ 2 → (scale : ℝ) ^ exp ≤ (scale : ℝ)^2 := by
    intro exp hx
    simpa using Real.rpow_le_rpow_of_exponent_le hn hx
  have hdim' : poly.dimension + 3 ≤ d := by
    have hu := hdim.trans (hsq _ (by norm_num))
    have hv : (8 : ℝ) ≤ size := Nat.cast_le.mpr hsize
    exact_mod_cast (show (poly.dimension : ℝ) + 3 ≤ d by linarith)
  have hfac' : poly.facetCount + 2 ≤ excess := by
    have hu := hfac.trans (mul_le_mul_of_nonneg_left (hsq _ (by norm_num)) (Nat.cast_nonneg _))
    have hv : (8 : ℝ) ≤ size := Nat.cast_le.mpr hsize
    exact_mod_cast (show (poly.facetCount : ℝ) + 2 ≤ excess by linarith)
  let moves := ⌊(size : ℝ) ^ ((1/4) * gamma)⌋₊
  have hm : 1 ≤ moves := Nat.le_floor (by simpa using Real.one_le_rpow hs (show 0 ≤ 1/4 * gamma by positivity))
  have hm' : moves ≤ ⌊(scale : ℝ) ^ gamma⌋₊ := by
    apply Nat.floor_mono
    rw [Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow (by positivity) lower hg.le
  obtain ⟨padded, hp, hpd, hpf, src, dst, hdist⟩ :=
    pad_excess poly reg hdim' hfac' hm obj.high obj.low
  refine ⟨padded, hp.simple, padded.connected hp le_rfl, hpd, hpf, src, dst, ?_⟩
  have hfar := ((cost _ _).1 obj.gap_extremes).trans
    ((poly.dist_anti reg hm hm' obj.high obj.low).trans hdist)
  have hmin : min ((excess : ℝ)^aa) ((d : ℝ)^bb) ≤ (size : ℝ)^(power : ℝ) := by
    rcases le_total d excess with hle | hle
    · rw [show size = d from min_eq_left hle]
      exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_exponent_le (hs.trans hd)
        ((le_max_right _ _).trans hpow.le))
    · rw [show size = excess from min_eq_right hle]
      exact (min_le_left _ _).trans (Real.rpow_le_rpow_of_exponent_le (hs.trans he)
        ((le_max_left _ _).trans hpow.le))
  have hpower : (size : ℝ)^(power : ℝ) ≤ (scale : ℝ)^(4 * power) := by
    have eqn : (power : ℝ) = (1/4) * (4 * power : ℕ) := by push_cast; ring
    rw [eqn, Real.rpow_mul (by positivity), Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) lower _
  calc
    _ ≤ ((mult : ℝ) * (scale : ℝ)^2) * (scale : ℝ)^(4 * power) :=
      mul_le_mul (by linarith) (hmin.trans hpower) (by positivity) (by positivity)
    _ = (mult * scale ^ degree : ℕ) := by simp [degree, pow_add]; ring
    _ ≤ _ := Nat.cast_le.mpr hfar

end OAI.Geometry.Hirsch
