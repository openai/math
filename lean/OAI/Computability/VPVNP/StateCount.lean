import OAI.Computability.VPVNP.ShiftedFactorization
import Lemmata.FockCircuits.PartitionAnalysis
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Fin

/-!
# State counts for the shifted crossing

Appendix B of *VP and VNP differ over every field* bounds the sizes of two
integral factorizations using different energy cutoffs. Energies here are
doubled, so a signed integer shift changes the cutoff by twice that integer.

We use the fermionic partition asymptotic from Khoruzhii's development, count
the finite-mode states, and evaluate the two dimension sequences and both
factorization bounds for the same shift.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

open Filter
open scoped Topology BigOperators
open Lemmata.FockCircuits (partitionSlice partitionDimension mem_partitionSlice fermionIntegral
  fermionIntegral_pos partitionDimension_zero partition_cumulative_log_tendsto cumulativeWeight)

/-- Number of fermionic states of doubled energy at most `H`. Each occupied
mode `i` contributes `2*i+1`. -/
def cutoffCount (H : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (H+1), partitionDimension k

/-- Base-two growth constant for a cutoff measured in doubled energy. -/
noncomputable def stateExponent : ℝ :=
  2 * Real.sqrt (fermionIntegral / 2) / Real.log 2

theorem stateExponent_pos : 0 < stateExponent :=
  div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (half_pos fermionIntegral_pos)))
    (Real.log_pos (by norm_num))

theorem cutoffCount_pos (H : ℕ) : 0 < cutoffCount H := by
  have h := Finset.single_le_sum (s := Finset.range (H+1)) (f := partitionDimension)
    (fun _ _ => Nat.zero_le _) (a := 0) (Finset.mem_range.mpr (Nat.zero_lt_succ H))
  exact (Nat.zero_lt_one.trans_le (by simpa only [partitionDimension_zero, cutoffCount] using h))

/-- The partition-function asymptotic in the logarithmic base and energy units
of the two shifted flattening bounds. -/
theorem cutoffCount_limit :
    Tendsto (fun k : ℕ => Real.logb 2 (cutoffCount k) / Real.sqrt k)
      atTop (𝓝 stateExponent) := by
  have h := partition_cumulative_log_tendsto.div_const (Real.log 2)
  apply h.congr fun k => ?_
  simp only [cumulativeWeight, Real.logb, cutoffCount, Nat.cast_sum]
  ring

private def partitionCutoff (k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (k+1)).biUnion partitionSlice

private theorem mem_partitionCutoff {k : ℕ} {s : Finset ℕ} :
    s ∈ partitionCutoff k ↔ Lemmata.FockCircuits.doubledEnergy s ≤ k := by
  simp only [partitionCutoff, Finset.mem_biUnion, Finset.mem_range, mem_partitionSlice]
  constructor
  · rintro ⟨e, he, rfl⟩
    omega
  · intro hs
    exact ⟨_, by omega, rfl⟩

private theorem card_partitionCutoff (k : ℕ) :
    (partitionCutoff k).card = cutoffCount k := by
  apply Finset.card_biUnion
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro s hsa hsb
  exact hab ((mem_partitionSlice.mp hsa).symm.trans (mem_partitionSlice.mp hsb))

theorem doubledEnergy_map_val {N : ℕ} (s : Occupation N) :
    (Lemmata.FockCircuits.doubledEnergy (s.map Fin.valEmbedding) : ℤ) = doubledEnergy s := by
  simp [Lemmata.FockCircuits.doubledEnergy, doubledEnergy, Fin.valEmbedding]

private def forgetModeBound (N k : ℕ) :
    {s : Occupation N // doubledEnergy s ≤ (k : ℤ)} ↪ partitionCutoff k where
  toFun s := ⟨s.val.map Fin.valEmbedding, mem_partitionCutoff.mpr (by
    exact_mod_cast ((doubledEnergy_map_val s.val).le.trans s.property))⟩
  inj' := fun _ _ h => Subtype.ext <| Finset.map_injective Fin.valEmbedding (congrArg Subtype.val h)

/-- The dimension bound for finite occupation states of doubled energy at most `k`. -/
theorem occupationCount_le (N k : ℕ) :
    Fintype.card {s : Occupation N // doubledEnergy s ≤ (k : ℤ)} ≤
      cutoffCount k := by
  rw [← card_partitionCutoff, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective _ (forgetModeBound N k).injective

/-- Once modes below `k` are included, the entire partition cutoff occurs. -/
theorem occupationCount_eq (N k : ℕ) (hk : k ≤ N) :
    Fintype.card {s : Occupation N // doubledEnergy s ≤ (k : ℤ)} =
      cutoffCount k := by
  rw [← card_partitionCutoff, ← Fintype.card_coe]
  apply Fintype.card_of_bijective (f := forgetModeBound N k)
  refine ⟨(forgetModeBound N k).injective, ?_⟩
  intro s
  have hs := mem_partitionCutoff.mp s.property
  have hb (i : ℕ) (hi : i ∈ s.val) : i < N := by
    have hi' := Finset.single_le_sum (f := fun j : ℕ => 2*j+1) (fun j _ => Nat.zero_le _) hi
    change 2*i+1 ≤ Lemmata.FockCircuits.doubledEnergy s.val at hi'
    omega
  refine ⟨⟨s.val.attachFin hb, ?_⟩, ?_⟩
  · rw [← doubledEnergy_map_val, Finset.map_valEmbedding_attachFin]
    exact_mod_cast hs
  · exact Subtype.ext (Finset.map_valEmbedding_attachFin hb)

/-- A negative doubled-energy cutoff contains no states, including the vacuum. -/
theorem occupationCount_of_neg (N : ℕ) {B : ℤ} (hB : B < 0) :
    Fintype.card {s : Occupation N // doubledEnergy s ≤ B} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun s => ?_⟩
  have h := s.property
  rw [← doubledEnergy_map_val] at h
  omega

/-- A signed integer cut at quadratic scale. In particular the displacement may be negative. -/
noncomputable def roundedQuadratic (a : ℝ) (n : ℕ) : ℤ :=
  ⌊(n : ℝ) ^ 2 * a⌋

theorem tendsto_roundedQuadratic (a : ℝ) :
    Tendsto (fun n : ℕ ↦ (roundedQuadratic a n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 a) := by
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp
      tendsto_natCast_atTop_atTop)
  have hlower : Tendsto (fun n : ℕ ↦ a - 1 / (n : ℝ) ^ 2) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : 0 < (n : ℝ) ^ 2 := by positivity
    change a - 1 / (n : ℝ) ^ 2 ≤ (⌊(n : ℝ) ^ 2 * a⌋ : ℝ) / (n : ℝ) ^ 2
    rw [le_div_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
    linarith only [Int.lt_floor_add_one ((n : ℝ) ^ 2 * a)]
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : 0 < (n : ℝ) ^ 2 := by positivity
    exact (div_le_iff₀ hn').2 (mul_comm a ((n : ℝ) ^ 2) ▸ Int.floor_le _)

/-- A nonnegative integer energy, obtained from the signed cut by truncation at zero. -/
noncomputable def quadraticEnergy (a : ℝ) (n : ℕ) : ℕ :=
  (roundedQuadratic a n).toNat

private theorem tendsto_quadraticScale_toNat {g : ℕ → ℤ} {a : ℝ} (ha : 0 < a)
    (hg : Tendsto (fun n : ℕ ↦ (g n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ ((g n).toNat : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 a) := by
  apply hg.congr'
  filter_upwards [hg.eventually_const_lt ha] with n hn
  have hnonneg : (0 : ℝ) ≤ g n := by
    by_contra! hneg
    exact hn.not_ge (div_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg _))
  have hcast := Int.toNat_of_nonneg (show 0 ≤ g n by exact_mod_cast hnonneg)
  have heq : ((g n).toNat : ℝ) = g n := by exact_mod_cast hcast
  exact congrArg (fun x : ℝ ↦ x / (n : ℝ) ^ 2) heq.symm

theorem tendsto_quadraticEnergy {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ (quadraticEnergy a n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 a) :=
  tendsto_quadraticScale_toNat ha (tendsto_roundedQuadratic a)

/-- Both shifted energies use the same integer displacement. -/
noncomputable def shiftedEnergy (v w δ : ℝ) (positive : Bool) (n : ℕ) : ℕ :=
  let base : ℤ := quadraticEnergy v n + (quadraticEnergy w n : ℤ)
  let displacement := 2 * roundedQuadratic δ n
  (if positive then base + displacement else base - displacement).toNat

theorem tendsto_shiftedEnergy {v w δ : ℝ} (hv : 0 < v) (hw : 0 < w) (positive : Bool)
    (h : 0 < (if positive then v + w + 2 * δ else v + w - 2 * δ)) :
    Tendsto (fun n : ℕ ↦ (shiftedEnergy v w δ positive n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (if positive then v + w + 2 * δ else v + w - 2 * δ)) := by
  have hbase := (tendsto_quadraticEnergy hv).add (tendsto_quadraticEnergy hw)
  have hdisp := (tendsto_roundedQuadratic δ).const_mul 2
  unfold shiftedEnergy
  apply tendsto_quadraticScale_toNat h
  cases positive
  · simpa only [Bool.false_eq_true, ↓reduceIte, Int.cast_sub, Int.cast_add, Int.cast_natCast,
      Int.cast_mul, Int.cast_ofNat, sub_div, add_div, mul_div_assoc] using hbase.sub hdisp
  · simpa only [↓reduceIte, Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat,
      add_div, mul_div_assoc] using hbase.add hdisp

/-- The logarithmic state-count asymptotic along an integral cutoff growing as
`v * n²`. The growth constant is expressed in base two. -/
theorem count_quadratic_limit (D H : ℕ → ℕ) {c v : ℝ} (hv : 0 < v)
    (hD : Tendsto (fun k : ℕ => Real.logb 2 (D k) / Real.sqrt k) atTop (𝓝 c))
    (hH : Tendsto (fun n : ℕ => (H n : ℝ) / (n : ℝ)^2) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ => Real.logb 2 (D (H n)) / n) atTop (𝓝 (c * Real.sqrt v)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hn2 : Tendsto (fun n : ℕ => (n : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hn
  have hHreal := hH.pos_mul_atTop hv hn2
  have hHtop : Tendsto H atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
    apply hHreal.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp [hn']
  have hs : Tendsto (fun n : ℕ => Real.sqrt (H n) / n) atTop (𝓝 (Real.sqrt v)) := by
    refine hH.sqrt.congr fun n => ?_
    rw [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  refine ((hD.comp hHtop).mul hs).congr' ?_
  filter_upwards [hHtop.eventually_gt_atTop 0] with n hn
  have hp : Real.sqrt (H n) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  change Real.logb 2 (D (H n)) / Real.sqrt (H n) * (Real.sqrt (H n) / n) =
    Real.logb 2 (D (H n)) / n
  field_simp [hp]

/-- A fixed power of the quadratic energy cutoff has subexponential size. -/
theorem logb_polynomial_overhead (h : ℕ → ℕ) (v : ℝ) (d : ℕ)
    (hh : Tendsto (fun n : ℕ ↦ (h n : ℝ) / (n : ℝ)^2) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ ↦ Real.logb 2 (((h n + 1)^d : ℕ) : ℝ) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ) / n) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have upper : Tendsto (fun n : ℕ ↦ ((d : ℝ) * 3) * (Real.logb 2 n / n)) atTop (𝓝 0) := by
    simpa using hlog.const_mul ((d : ℝ) * 3)
  apply squeeze_zero' _ _ upper
  · filter_upwards with n
    apply div_nonneg _ (Nat.cast_nonneg n)
    apply Real.logb_nonneg (by norm_num)
    exact_mod_cast Nat.one_le_pow _ _ (by omega)
  · filter_upwards [hh.eventually (gt_mem_nhds (show v < v + 1 by linarith)),
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (v+2),
      eventually_ge_atTop (1 : ℕ)] with n hn hv hn1
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : 0 < (n : ℝ) := by linarith
    have hh' : (h n : ℝ) < (v + 1) * (n : ℝ)^2 :=
      (div_lt_iff₀ (sq_pos_of_pos hnpos)).mp hn
    have bound : (h n : ℝ) + 1 ≤ (n : ℝ)^3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hv) (sq_nonneg (n : ℝ)),
        sq_nonneg ((n : ℝ)-1)]
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.logb_pow]
    calc
      _ ≤ (d : ℝ) * Real.logb 2 ((n : ℝ)^3) / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.logb_le_logb_of_le (by norm_num) (by positivity) bound) (by positivity))
          (by positivity)
      _ = _ := by rw [Real.logb_pow]; push_cast; ring

/-- Removing the empty state preserves any positive exponential growth rate. -/
theorem logb_pred_rate (D : ℕ → ℕ) (t : ℝ) (ht : 0 < t)
    (hD : Tendsto (fun n : ℕ ↦ Real.logb 2 (D n : ℝ) / n) atTop (𝓝 t)) :
    Tendsto (fun n : ℕ ↦ Real.logb 2 ((D n - 1 : ℕ) : ℝ) / n) atTop (𝓝 t) := by
  have hlarge : ∀ᶠ n in atTop, 2 ≤ D n := by
    filter_upwards [hD.eventually (lt_mem_nhds ht)] with n hn
    by_contra! h
    have heq : D n = 0 ∨ D n = 1 := by omega
    rcases heq with h0 | h1 <;> simp_all
  have hlower : Tendsto (fun n : ℕ ↦ Real.logb 2 (D n : ℝ) / n - 1 / n) atTop (𝓝 t) := by
    simpa using hD.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hD
  · filter_upwards [hlarge] with n hn
    have h1 : 0 < ((D n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < D n - 1 by omega)
    have h2 : (D n : ℝ) ≤ ((D n - 1 : ℕ) : ℝ) * 2 := by
      exact_mod_cast (show D n ≤ (D n - 1) * 2 by omega)
    have H := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (by exact_mod_cast (show 0 < D n by omega)) h2
    rw [Real.logb_mul h1.ne' (by norm_num), Real.logb_self_eq_one (by norm_num)] at H
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · filter_upwards [hlarge] with n hn
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Real.logb_le_logb_of_le (by norm_num)
      (by exact_mod_cast (show 0 < D n - 1 by omega)) (by exact_mod_cast Nat.sub_le (D n) 1)

/-- Doubled-energy cutoff of a wire with prescribed base-two logarithmic rate. -/
noncomputable def crossingEnergy (t : ℝ) (n : ℕ) : ℕ :=
  quadraticEnergy ((t / stateExponent)^2) n

/-- The integer shift shared by the two crossing factorizations. -/
noncomputable def crossingShift (δ : ℝ) (n : ℕ) : ℤ :=
  roundedQuadratic (δ / (2 * stateExponent^2)) n

/-- The number of available factor coordinates on one of the two cuts, including
the polynomial cost of summing over cardinalities, energies, and monomials. -/
noncomputable def crossingFactorBound (t u δ : ℝ) (positive : Bool) (n : ℕ) : ℕ :=
  let H := crossingEnergy t n
  let E := crossingEnergy u n
  let s := crossingShift δ n
  let B : ℤ := if positive then H + (E : ℤ) + 2*s else H + (E : ℤ) - 2*s
  (H+1)^4 * cutoffCount B.toNat

theorem crossingEnergy_count_limit (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => Real.logb 2 (cutoffCount (crossingEnergy t n)) / n)
      atTop (𝓝 t) := by
  have hp := div_pos ht stateExponent_pos
  have h := count_quadratic_limit cutoffCount (crossingEnergy t) (sq_pos_of_pos hp)
    cutoffCount_limit (tendsto_quadraticEnergy (sq_pos_of_pos hp))
  rwa [Real.sqrt_sq hp.le, mul_div_cancel₀ _ stateExponent_pos.ne'] at h

/-- The exponential rates in Theorem 3.1, using one integral displacement for both
bounds. The first dimension omits the empty state and the second includes it. -/
theorem shiftedCrossing_rates (t u δ : ℝ) (ht : 0 < t) (hu : 0 < u)
    (hlo : -(t^2+u^2) < δ) (hhi : δ < t^2+u^2) :
    Tendsto (fun n : ℕ => Real.logb 2 ((cutoffCount (crossingEnergy t n) - 1 : ℕ) : ℝ) / n)
      atTop (𝓝 t) ∧
    Tendsto (fun n : ℕ => Real.logb 2 (cutoffCount (crossingEnergy u n)) / n)
      atTop (𝓝 u) ∧
    ∀ positive : Bool,
      Tendsto (fun n : ℕ => Real.logb 2 (crossingFactorBound t u δ positive n) / n) atTop
        (𝓝 (Real.sqrt (if positive then t^2+u^2+δ else t^2+u^2-δ))) := by
  refine ⟨logb_pred_rate _ t ht (crossingEnergy_count_limit t ht),
    crossingEnergy_count_limit u hu, ?_⟩
  intro positive
  let v := (t / stateExponent)^2
  let w := (u / stateExponent)^2
  let d := δ / (2 * stateExponent^2)
  let T := if positive then t^2+u^2+δ else t^2+u^2-δ
  have hc := stateExponent_pos
  have hv : 0 < v := sq_pos_of_pos (div_pos ht hc)
  have hw : 0 < w := sq_pos_of_pos (div_pos hu hc)
  have hT : 0 < T := by cases positive <;> dsimp [T] <;> linarith
  have hscale : (if positive then v + w + 2*d else v + w - 2*d) = T / stateExponent^2 := by
    cases positive <;> dsimp [v, w, d, T] <;> field_simp
  have hpos : 0 < (if positive then v + w + 2*d else v + w - 2*d) :=
    hscale ▸ div_pos hT (sq_pos_of_pos hc)
  have hcount := count_quadratic_limit cutoffCount (shiftedEnergy v w d positive)
    hpos cutoffCount_limit (tendsto_shiftedEnergy hv hw positive hpos)
  rw [hscale, Real.sqrt_div hT.le, Real.sqrt_sq hc.le, mul_div_cancel₀ _ hc.ne'] at hcount
  have hpoly := logb_polynomial_overhead (crossingEnergy t) v 4 (tendsto_quadraticEnergy hv)
  have htotal := hpoly.add hcount
  rw [zero_add] at htotal
  apply htotal.congr fun n => ?_
  change Real.logb 2 (((crossingEnergy t n + 1)^4 : ℕ) : ℝ) / n +
    Real.logb 2 (cutoffCount (shiftedEnergy v w d positive n)) / n =
    Real.logb 2 ((((crossingEnergy t n + 1)^4 : ℕ) *
      cutoffCount (shiftedEnergy v w d positive n) : ℕ) : ℝ) / n
  have hn : 0 < (cutoffCount (shiftedEnergy v w d positive n) : ℝ) := by
    exact_mod_cast cutoffCount_pos _
  rw [Nat.cast_mul, Real.logb_mul (by positivity) hn.ne', add_div]

end Crossing

end VPVNP
end Computability
end OAI
