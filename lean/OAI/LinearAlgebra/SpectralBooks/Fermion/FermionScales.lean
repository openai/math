import OAI.LinearAlgebra.SpectralBooks.Energy
import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionOverhead

/-! # Logarithmic dimensions of the shifted fermionic crossing

At quadratic cutoffs the state-count asymptotic gives linear logarithmic
dimensions. Rounding the cutoffs and shifting the two intermediate energies
gives the two different square-root rates.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace Fermion

open Filter Real
open scoped Topology

private abbrev countCoefficient : ℝ := 2 * √fermionFreeEnergy / log 2

private theorem countCoefficient_pos : 0 < countCoefficient :=
  div_pos (mul_pos (by norm_num) (sqrt_pos.mpr fermionFreeEnergy_pos)) (log_pos (by norm_num))

private theorem tendsto_natCast_sq :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2) atTop atTop :=
  (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop

private theorem tendsto_floor_scaled (a : ℝ) :
    Tendsto (fun n : ℕ ↦ (⌊a * (n : ℝ) ^ 2⌋ : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 a) := by
  have he : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_sq
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using tendsto_const_nhds.sub he)
    (tendsto_const_nhds (x := a))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : 0 < (n : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ hn', sub_mul, inv_mul_cancel₀ hn'.ne']
    linarith [Int.lt_floor_add_one (a * (n : ℝ)^2)]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (div_le_iff₀ (by positivity)).mpr (Int.floor_le _)

/-- A positive quadratic energy rate determines the normalized logarithmic
state count, including for signed integer cutoffs which are eventually positive. -/
private theorem tendsto_states_log {B : ℕ → ℤ} {w : ℝ} (hw : 0 < w)
    (hB : Tendsto (fun n : ℕ ↦ (B n : ℝ) / 2 / (n : ℝ)^2) atTop
      (𝓝 (w / countCoefficient ^ 2))) :
    Tendsto (fun n : ℕ ↦ logb 2 ((states (B n)).card) / n) atTop (𝓝 (√w)) := by
  have hc := countCoefficient_pos
  let X (n : ℕ) : ℝ := (B n : ℝ) / 2
  have hp : 0 < w / countCoefficient ^ 2 := by positivity
  have hX : Tendsto X atTop atTop := by
    refine (hB.pos_mul_atTop hp tendsto_natCast_sq).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_mul_cancel₀ _ (by positivity)
  have hs : Tendsto (fun n : ℕ ↦ √(X n) / n) atTop (𝓝 (√w / countCoefficient)) := by
    simpa only [Real.sqrt_div (show 0 ≤ w from hw.le), Real.sqrt_sq hc.le,
      Real.sqrt_div' _ (sq_nonneg (_ : ℝ)), Real.sqrt_sq (Nat.cast_nonneg _)] using hB.sqrt
  have ha := (tendsto_logb_fermionCount_div_sqrt.comp hX).mul hs
  change Tendsto _ _ (𝓝 (countCoefficient * (√w / countCoefficient))) at ha
  rw [show countCoefficient * (√w / countCoefficient) = √w by rw [mul_comm, div_mul_cancel₀ _ hc.ne']] at ha
  refine ha.congr' ?_
  filter_upwards [hX.eventually_gt_atTop 0] with n hn
  change logb 2 (fermionCount (X n)) / √(X n) * (√(X n) / n) = _
  rw [states_eq_fermionStates]
  unfold fermionCount
  field_simp [ne_of_gt (sqrt_pos.mpr hn)]
  rfl

private def scaledCutoff (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(2 * x ^ 2 / countCoefficient ^ 2) * (n : ℝ) ^ 2⌋₊

private def scaledShift (δ : ℝ) (n : ℕ) : ℤ :=
  ⌊(δ / countCoefficient ^ 2) * (n : ℝ) ^ 2⌋

private theorem scaledCutoff_le (x : ℝ) (n : ℕ) :
    (scaledCutoff x n : ℝ) ≤ (2 * x ^ 2 / countCoefficient ^ 2) * (n : ℝ)^2 :=
  Nat.floor_le (by positivity)

private theorem tendsto_scaledCutoff (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (scaledCutoff x n : ℝ) / 2 / (n : ℝ)^2) atTop
      (𝓝 (x ^ 2 / countCoefficient ^ 2)) := by
  have h := ((tendsto_nat_floor_mul_div_atTop
    (show 0 ≤ 2 * x ^ 2 / countCoefficient ^ 2 by positivity)).comp tendsto_natCast_sq).div_const 2
  convert h using 1
  · funext n
    dsimp [scaledCutoff]
    ring
  · congr 1
    ring

private theorem tendsto_scaledShift (δ : ℝ) :
    Tendsto (fun n : ℕ ↦ (scaledShift δ n : ℝ) / (n : ℝ)^2) atTop
      (𝓝 (δ / countCoefficient ^ 2)) :=
  tendsto_floor_scaled _

private theorem tendsto_shifted_cutoffs (t u δ : ℝ) :
    Tendsto (fun n : ℕ ↦ (((scaledCutoff u n : ℤ) + scaledCutoff t n +
      2 * scaledShift δ n : ℤ) : ℝ) / 2 / (n : ℝ)^2) atTop
        (𝓝 ((t^2 + u^2 + δ) / countCoefficient ^ 2)) ∧
    Tendsto (fun n : ℕ ↦ (((scaledCutoff u n : ℤ) + scaledCutoff t n -
      2 * scaledShift δ n : ℤ) : ℝ) / 2 / (n : ℝ)^2) atTop
        (𝓝 ((t^2 + u^2 - δ) / countCoefficient ^ 2)) := by
  have h := (tendsto_scaledCutoff t).add (tendsto_scaledCutoff u)
  constructor
  · convert h.add (tendsto_scaledShift δ) using 1
    · funext n
      push_cast
      ring
    · congr 1
      ring
  · convert h.sub (tendsto_scaledShift δ) using 1
    · funext n
      push_cast
      ring
    · congr 1
      ring

private theorem eventually_dim_pos {D : ℕ → ℕ} {l : ℝ} (hl : 0 < l)
    (h : Tendsto (fun n : ℕ ↦ logb 2 (D n) / n) atTop (𝓝 l)) :
    ∀ᶠ n in atTop, 0 < D n := by
  filter_upwards [h.eventually_const_lt hl] with n hn
  by_contra! h
  simp [Nat.eq_zero_of_le_zero h] at hn

private theorem tendsto_logb_product {D Q : ℕ → ℕ} {w : ℝ} (hw : 0 < w)
    (hD : Tendsto (fun n : ℕ ↦ logb 2 (D n) / n) atTop (𝓝 w))
    (hQ : Tendsto (fun n : ℕ ↦ logb 2 (Q n) / n) atTop (𝓝 0)) (hq : ∀ n, 0 < Q n) :
    Tendsto (fun n : ℕ ↦ logb 2 (Q n * D n : ℕ) / n) atTop (𝓝 w) := by
  refine (by simpa using hQ.add hD : Tendsto _ _ (𝓝 w)).congr' ?_
  filter_upwards [eventually_dim_pos hw hD] with n hn
  simp only [Nat.cast_mul, logb_mul (b := 2) (x := (Q n : ℝ)) (y := (D n : ℝ))
    (by exact_mod_cast (hq n).ne') (by exact_mod_cast hn.ne'), add_div]

/-- The label and state dimensions have the prescribed rates, and the two
tagged intermediate state spaces have the shifted square-root rates. -/
theorem exists_scaled_dimensions (t u δ : ℝ) (ht : 0 < t) (hu : 0 < u)
    (hlo : -(t^2 + u^2) < δ) (hhi : δ < t^2 + u^2) :
    ∃ (H E : ℕ → ℕ) (s : ℕ → ℤ),
      (∀ᶠ n in atTop, 0 < Fintype.card (Label (H n)) ∧ 0 < (states (E n)).card) ∧
      Tendsto (fun n : ℕ ↦ logb 2 (Fintype.card (Label (H n))) / n) atTop (𝓝 t) ∧
      Tendsto (fun n : ℕ ↦ logb 2 ((states (E n)).card) / n) atTop (𝓝 u) ∧
      Tendsto (fun n : ℕ ↦ logb 2 (((H n+1)^3 * (states ((E n : ℤ) + H n + 2*s n)).card : ℕ)) / n)
        atTop (𝓝 (√(t^2 + u^2 + δ))) ∧
      Tendsto (fun n : ℕ ↦ logb 2 (((H n+1)^3 * (states ((E n : ℤ) + H n - 2*s n)).card : ℕ)) / n)
        atTop (𝓝 (√(t^2 + u^2 - δ))) := by
  let H := scaledCutoff t
  let E := scaledCutoff u
  let s := scaledShift δ
  have hstate (x : ℝ) (hx : 0 < x) :
      Tendsto (fun n : ℕ ↦ logb 2 ((states (scaledCutoff x n)).card) / n) atTop (𝓝 x) := by
    have hx' := @tendsto_states_log (fun n ↦ (scaledCutoff x n : ℤ)) (x^2) (by positivity)
      (by simpa only [Int.cast_natCast] using tendsto_scaledCutoff x)
    simpa only [sqrt_sq hx.le] using hx'
  have hlabel := tendsto_label_log_of_states ht (hstate t ht)
  have htag := tendsto_logb_cube_overhead (by positivity : 0 ≤ 2 * t^2 / countCoefficient^2)
    (scaledCutoff_le t)
  obtain ⟨hp, hm⟩ := tendsto_shifted_cutoffs t u δ
  refine ⟨H, E, s, (eventually_dim_pos ht hlabel).and (eventually_dim_pos hu (hstate u hu)),
    hlabel, hstate u hu, ?_, ?_⟩
  · exact tendsto_logb_product (sqrt_pos.mpr (by linarith)) (tendsto_states_log (by linarith) hp)
      (by simpa only [H, Nat.cast_pow] using htag) (fun _ ↦ by positivity)
  · exact tendsto_logb_product (sqrt_pos.mpr (by linarith)) (tendsto_states_log (by linarith) hm)
      (by simpa only [H, Nat.cast_pow] using htag) (fun _ ↦ by positivity)

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
