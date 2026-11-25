import OAI.Combinatorics.Sunflower.Filter
import OAI.Combinatorics.Sunflower.Prices
import OAI.Combinatorics.Sunflower.Summability
import OAI.Combinatorics.Sunflower.Alphabet

/-! # A uniform price for testing equality

The resource ratio at each step increases by the cost of one correction divided
by the value of the diagonal of all nonzero directions. A strictly positive
gap makes the resulting increments summable independently of the alphabet.
-/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

open Binary Control

variable {I : Type*} [Fintype I] [Nonempty I]

private theorem coeff_ne_zero_of_value_pos
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    {X : Raw.{0} I ℂ} (hX : 0 < spectralValue φ X) : X.coeff ≠ 0 := by
  intro h
  simp [spectralValue, (ofRaw_eq_zero_iff X).mpr h, φ.property.1] at hX

omit [Nonempty I] in
/-- A filter remains correct after restricting its controls to an embedded alphabet. -/
theorem EqualityMaps.precompose {P T : Finset I} {R Q : Raw.{0} I ℂ}
    {A B : Type} (e : B ↪ A) (h : EqualityMaps P T A R Q) :
    EqualityMaps P T B R Q := by
  obtain ⟨M, hM⟩ := h
  refine ⟨pre (fun _ => e) M, ?_⟩
  intro x y c hc₁ hc₂ o
  rw [eval_pre, hM (e x) (e y) (fun i => e (c i))
    (fun i hi => congrArg e (hc₁ i hi)) (fun i hi => congrArg e (hc₂ i hi))]
  simp

private theorem bounded_filter_induction
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (P T : Finset I) (hK : (P ∪ T).Nonempty) {d B : ℝ} (hd : 0 < d)
    (hbase : EqualityMaps P T (Word 0) (Raw.one I ℂ) (Raw.one I ℂ))
    (hstep : ∀ (b : ℕ) (R Q : Raw.{0} I ℂ), EqualityMaps P T (Word b) R Q →
      ∃ U V : Raw.{0} I ℂ, U.coeff ≠ 0 ∧ V.coeff ≠ 0 ∧
        rawLogPrice φ 1 U - rawLogPrice φ 1 V ≤
          (maskDiagonalPrice φ 1 (P ∪ T) - d) * ((b : ℝ) + 1) + B ∧
        let D := Raw.maskDiagonal ℂ (P ∪ T) (Direction (b + 1))
        EqualityMaps P T (Word (b + 1))
          ((R.mul (V.mul D)).add (Q.mul U)) (Q.mul (V.mul D))) :
    ∃ C : ℝ, ∀ n : ℕ, ∃ R Q : Raw.{0} I ℂ, R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧
      rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤ C ∧ EqualityMaps P T (Fin n) R Q := by
  classical
  let θ := maskDiagonalPrice φ 1 (P ∪ T)
  let f : ℕ → ℝ := Nat.rec 1 (fun b f => f + (2 : ℝ) ^ ((B + θ - d) - d * (b : ℝ)))
  have hf (b : ℕ) : f (b + 1) = f b + (2 : ℝ) ^ ((B + θ - d) - d * (b : ℝ)) := rfl
  obtain ⟨M, hM, hbound⟩ := filterRatio_bounded_of_affine hd (fun b => (hf b).le)
  have hlevels (b : ℕ) : ∃ R Q : Raw.{0} I ℂ, R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧
      spectralValue φ R / spectralValue φ Q ≤ f b ∧ EqualityMaps P T (Word b) R Q := by
    induction b with
    | zero =>
      have hn : (Raw.one.{0} I ℂ).coeff ≠ 0 := by
        exact fun he => one_ne_zero (congrFun he (fun _ => PUnit.unit))
      refine ⟨_, _, hn, hn, ?_, hbase⟩
      simp [f, (spectralValue_pos φ hn).ne']
    | succ b ih =>
      obtain ⟨R, Q, hR, hQ, hratio, hmaps⟩ := ih
      obtain ⟨U, V, hU, hV, hc, hnext⟩ := hstep b R Q hmaps
      let D := Raw.maskDiagonal ℂ (P ∪ T) (Direction (b+1))
      have hD : D.coeff ≠ 0 := Raw.maskDiagonal_ne_zero _ hK _
      have hvalD : spectralValue φ D = ((2 ^ (b+1) - 1 : ℕ) : ℝ) ^ θ := by
        simpa [D, θ] using spectralValue_maskDiagonal_card φ (P ∪ T) hK (Direction (b+1))
      have hinc := filterIncrement_le_of_cost b (d := d) (B := B) (spectralValue_pos φ hU)
        (spectralValue_pos φ hV) (maskDiagonalPrice_nonneg φ zero_le_one (P ∪ T))
        (by simpa [rawLogPrice, spectralValue] using hc)
      have hR' : 0 < spectralValue φ ((R.mul (V.mul D)).add (Q.mul U)) := by
        simp only [spectralValue_add, spectralValue_mul]
        exact add_pos (mul_pos (spectralValue_pos φ hR)
          (mul_pos (spectralValue_pos φ hV) (spectralValue_pos φ hD)))
          (mul_pos (spectralValue_pos φ hQ) (spectralValue_pos φ hU))
      have hQ' : 0 < spectralValue φ (Q.mul (V.mul D)) := by
        simp only [spectralValue_mul]
        exact mul_pos (spectralValue_pos φ hQ)
          (mul_pos (spectralValue_pos φ hV) (spectralValue_pos φ hD))
      refine ⟨_, _, coeff_ne_zero_of_value_pos φ hR', coeff_ne_zero_of_value_pos φ hQ', ?_, hnext⟩
      rw [spectralRatio_filter_step φ R Q U V D hQ hV hD, hvalD, hf]
      exact add_le_add hratio hinc
  refine ⟨Real.logb 2 M, fun n => ?_⟩
  obtain ⟨R, Q, hR, hQ, hratio, hmaps⟩ := hlevels n
  refine ⟨R, Q, hR, hQ, ?_, hmaps.precompose (alphabetEmbedding n)⟩
  have hposR := spectralValue_pos φ hR
  have hposQ := spectralValue_pos φ hQ
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (div_pos hposR hposQ) (hratio.trans (hbound n))
  simpa [rawLogPrice, spectralValue, Real.logb_div hposR.ne' hposQ.ne'] using hl

/-- Corrections with a strictly smaller slope than the price of the direction
diagonal yield bounded-cost equality filters for every finite alphabet. -/
theorem exists_equality_filter_of_corrections
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (P T : Finset I) (hK : (P ∪ T).Nonempty) {d B : ℝ} (hd : 0 < d)
    (hcorr : ∀ b : ℕ, ∃ U V : Raw.{0} I ℂ, U.coeff ≠ 0 ∧ V.coeff ≠ 0 ∧
      rawLogPrice φ 1 U - rawLogPrice φ 1 V ≤
        (maskDiagonalPrice φ 1 (P ∪ T) - d) * ((b : ℝ) + 1) + B ∧
      CorrectionMaps P T b U V) :
    ∃ C : ℝ, ∀ n : ℕ, ∃ R Q : Raw.{0} I ℂ, R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧
      rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤ C ∧ EqualityMaps P T (Fin n) R Q := by
  apply bounded_filter_induction φ P T hK hd (B := B)
  · exact equalityMaps_one P T
  · intro b R Q hmaps
    obtain ⟨U, V, hU, hV, hc, hC⟩ := hcorr b
    exact ⟨U, V, hU, hV, hc, filter_step_maps (Classical.choice inferInstance) hmaps hC⟩

end
end Sunflower
end Combinatorics
end OAI
