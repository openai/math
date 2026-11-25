import OAI.Computability.NearSquareRoot.PrecisionRecordArithmetic

/-! # Multiplying a data record by a guarded phase coefficient

Input and coefficient may have different fractional precisions and signed
widths. The P192 command drops the coefficient's fractional bits after the
full signed product and writes the result at the original data width.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

def multiplyCoefficient {wd wc : ℕ} (pc : ℕ) (x : Dusk.Grain wd) (c : Dusk.Grain wc) :
    Dusk.Grain wd := Grid.launch (x, Code.tally pc, Dusk.mark c)

theorem multiplyCoefficient_encoding {wd wc : ℕ} (pc : ℕ) (x : Dusk.Grain wd) (c : Dusk.Grain wc) :
    Grid.adjust (Dusk.mark x, Code.tally pc, Dusk.mark c) =
      Dusk.mark (multiplyCoefficient pc x c) := Grid.inject ..

private theorem mixedContent {wd wc : ℕ} (pc : ℕ) (x : Dusk.Grain wd) (c : Dusk.Grain wc)
    (h : Grid.focus wd (Grid.divA pc (Grid.aspect x * Grid.aspect c))) :
    Grid.aspect (multiplyCoefficient pc x c) = Grid.divA pc (Grid.aspect x * Grid.aspect c) := by
  let row := Grid.rest (Code.tally pc, Grid.timesG (Grid.disp (Dusk.mark x), Grid.disp (Dusk.mark c)))
  have hr : Grid.content row = Grid.divA pc (Grid.aspect x * Grid.aspect c) := by
    dsimp only [row]
    rw [Grid.rest_r, Grid.key_M, Grid.pullG, Grid.pullG]
  have hr' : Grid.focus (wd+1) (Grid.content row) := by
    rw [hr, Grid.focus, Grid.tiny, pow_succ]
    have hn := pow_pos (by norm_num : (0:ℤ)<2) wd
    unfold Grid.focus Grid.tiny at h
    norm_num1 at *
    exact ⟨by omega, by omega⟩
  change Grid.aspect (Grid.wrapMap wd (Grid.content (Grid.fit (Code.tally (wd+1), row)))) = _
  rw [Grid.fit_small _ _ hr', hr, Grid.recovers _ h]

/-- The quantization error is determined by the output mesh alone. This also
covers a wider scalar obtained by a long prefix product of local phases. -/
theorem multiplyCoefficient_error {wd wc : ℕ} (pd pc : ℕ) (x : Dusk.Grain wd) (c : Dusk.Grain wc)
    (h : ‖Grid.meaning pd wd x * Grid.meaning pc wc c‖ * (2 : ℝ)^pd + 2 < 2^wd) :
    ‖Grid.meaning pd wd (multiplyCoefficient pc x c) - Grid.meaning pd wd x * Grid.meaning pc wc c‖ ≤
      2 / (2 : ℝ)^pd := by
  let a := Grid.aspect x * Grid.aspect c
  have he : Grid.toC a / (2 : ℂ)^pc / (2 : ℂ)^pd =
      Grid.meaning pd wd x * Grid.meaning pc wc c := by
    simp only [a, map_mul, Grid.meaning]
    field
  have emb := Grid.embedded pc a
  have hb : ‖Grid.toC (Grid.divA pc a)‖ ≤ ‖Grid.toC a / (2 : ℂ)^pc‖ + 2 := by
    have le := norm_le_norm_sub_add (Grid.toC (Grid.divA pc a)) (Grid.toC a / (2 : ℂ)^pc)
    linarith
  have hd : ‖Grid.toC a / (2 : ℂ)^pc‖ =
      ‖Grid.meaning pd wd x * Grid.meaning pc wc c‖ * 2^pd := by
    rw [← he, norm_div (Grid.toC a / (2 : ℂ)^pc), norm_pow, show ‖(2 : ℂ)‖ = (2:ℝ) by norm_num,
      div_mul_cancel₀ _ (by positivity)]
  rw [hd] at hb
  rw [Grid.meaning, mixedContent pc x c (Grid.short _ (Grid.into _) (hb.trans_lt h)), ← he,
    ← sub_div, norm_div, norm_pow, show ‖(2 : ℂ)‖ = (2:ℝ) by norm_num]
  exact div_le_div_of_nonneg_right emb (by positivity)

variable {ι : Type*} [Fintype ι]

/-- A full encoded phase pass with a separate coefficient width and shared
fractional descriptor. Only the final coefficient accuracy is assumed. -/
theorem applyPhase_error {k pc wc : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card ι = 2^k)
    (x : ι → Record k) (c : ι → Dusk.Grain wc) (phase : ι → ℂ) (hu : ∀ j, ‖phase j‖ = 1)
    (hx : ‖recordArray x‖ ≤ (2 : ℝ)^(13*k))
    (hc : ∀ j, ‖Grid.meaning pc wc (c j) - phase j‖ ≤ 1 / (2 : ℝ)^(70*k)) :
    ‖recordArray (fun j => multiplyCoefficient pc (x j) (c j)) -
        phaseLayerIsometry phase hu (recordArray x)‖ ≤ 1 / (2 : ℝ)^(50*k) := by
  rw [one_div]
  apply phaseLayer_dyadic_error_le hk hcard phase (fun j => Grid.meaning pc wc (c j)) _ _ hx
    (by simpa only [one_div] using hc)
  intro j
  have hcn : ‖Grid.meaning pc wc (c j)‖ ≤ 2 := by
    have hh := norm_le_norm_sub_add (Grid.meaning pc wc (c j)) (phase j)
    rw [hu] at hh
    linarith [hc j, (div_le_one (by positivity : 0 < (2:ℝ)^(70*k))).mpr (one_le_pow₀ (by norm_num))]
  have hcn' : ‖Grid.meaning pc wc (c j)‖ ≤ (2 : ℝ)^(13*k) := by
    apply hcn.trans
    simpa only [pow_one] using (pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num)
      (show 1 ≤ 13*k by omega))
  have fit := product_fits ((PiLp.norm_apply_le (recordArray x) j).trans hx) hcn'
  have he := multiplyCoefficient_error (fractionBits k) pc (x j) (c j) fit
  rw [fractionBits, pow_succ] at he
  change ‖value k (multiplyCoefficient pc (x j) (c j)) - Grid.meaning pc wc (c j) * value k (x j)‖ ≤ _
  rw [mul_comm (Grid.meaning pc wc (c j))]
  exact he.trans_eq (by field_simp)

end FixedPoint

end NearSquareRoot
end Computability
end OAI
