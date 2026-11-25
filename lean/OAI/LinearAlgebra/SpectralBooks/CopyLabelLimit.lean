import OAI.LinearAlgebra.SpectralBooks.CopyLabelOneShot
import OAI.LinearAlgebra.SpectralBooks.CopyLabelPower

/-! # Removing the bounded overhead in the copying degeneration

On a tensor power the shared word has `q ^ m` labels. The logarithm of the
auxiliary diagonal is at most `m * log₂ q + 2`; only its linear term survives
when dividing the price estimate by `m`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor

open scoped Classical
noncomputable section

variable {I : Type} [Fintype I] [Nonempty I] {K : Type*} [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (c : ℝ)

private theorem rawLogPrice_of_power {X Y : Raw.{0} I K} {m : ℕ}
    (h : ofRaw Y = ofRaw X ^ m) : rawLogPrice φ c Y = m * rawLogPrice φ c X := by
  let f := normalizedSpectrum.toRingHom φ
  change c * Real.logb 2 (f (ofRaw Y) : ℝ) = m * (c * Real.logb 2 (f (ofRaw X) : ℝ))
  rw [h, map_pow, NNReal.coe_pow, Real.logb_pow]
  ring

private theorem logb_copy_overhead (q m : ℕ) (hq : 0 < q) :
    Real.logb 2 (4 * (q ^ m - 1) + 1 : ℕ) ≤ 2 + m * Real.logb 2 q := by
  have hp : 0 < q ^ m := pow_pos hq m
  have hsize : 4 * (q ^ m - 1) + 1 ≤ 4 * q ^ m := by omega
  have hlog4 : Real.logb 2 4 = 2 := by
    convert Real.logb_pow 2 (2 : ℝ) 2 using 1 <;> norm_num [Real.logb_self_eq_one]
  calc
    _ ≤ Real.logb 2 (4 * (q : ℝ) ^ m) := by
      apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
      exact_mod_cast hsize
    _ = _ := by rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, hlog4]

variable [Infinite K]

/-- The infinite-field copying bound for any placement of the three sites.
The labels at the two original recipients need only agree on the support
of the original tensor. -/
theorem rawLogPrice_copy_infinite (hc : 0 ≤ c) (T : Raw.{0} I K) (σ : Fin 3 → I)
    {q : ℕ} (hq : 0 < q) (hA : T.Leg (σ 0) → Fin q) (hB : T.Leg (σ 1) → Fin q)
    (hmatch : ∀ x, T.coeff x ≠ 0 → hA (x (σ 0)) = hB (x (σ 1))) (hT : T.coeff ≠ 0) :
    rawLogPrice φ c (T.appendLabel (σ 2) (Fin q) (fun z => hA (z (σ 0)))) ≤
      rawLogPrice φ c T + (rawLogPrice φ c ((Raw.diagonal (Fin 3) K (Fin 2)).group σ) -
        rawWireDistance φ c (σ 0) (σ 1)) * Real.logb 2 q := by
  let a := rawLogPrice φ c T
  let b := rawLogPrice φ c (T.appendLabel (σ 2) (Fin q) (fun z => hA (z (σ 0))))
  let d := rawWireDistance φ c (σ 0) (σ 1)
  let δ := rawLogPrice φ c ((Raw.diagonal (Fin 3) K (Fin 2)).group σ)
  let l := Real.logb 2 q
  have hδ : 0 ≤ δ := rawLogPrice_nonneg φ hc _
  change b ≤ a + (δ - d) * l
  by_contra! h
  have hgap : 0 < b - (a + (δ - d) * l) := sub_pos.mpr h
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * δ / (b - (a + (δ - d) * l)))
  let e : (Fin m → Fin q) ≃ Fin (q ^ m) := Fintype.equivFinOfCardEq (by simp)
  let A (x : (T.powerTensor m).Leg (σ 0)) := e (fun j => hA (x j))
  let B (x : (T.powerTensor m).Leg (σ 1)) := e (fun j => hB (x j))
  have finite := rawLogPrice_copy_one_shot φ c hc (T.powerTensor m) σ (pow_pos hq m) A B
    (T.powerTensor_labels_match hA hB hmatch m e) (T.powerTensor_ne_zero hT m)
  have hbase := rawLogPrice_of_power φ c (T.ofRaw_powerTensor m)
  have hcopy := rawLogPrice_of_power φ c
    (T.ofRaw_appendLabel_power (σ 2) (fun z => hA (z (σ 0))) m e)
  change rawLogPrice φ c ((T.powerTensor m).appendLabel (σ 2) (Fin (q ^ m))
    (fun x => A (x (σ 0)))) = m * b at hcopy
  rw [hcopy, hbase, Nat.cast_pow, Real.logb_pow] at finite
  have overhead := mul_le_mul_of_nonneg_left (logb_copy_overhead q m hq) hδ
  have hh : (m : ℝ) * b + d * (m * l) ≤ m * a + δ * (2 + m * l) :=
    finite.trans (add_le_add_right overhead _)
  have large := (div_lt_iff₀ hgap).mp hm
  linarith

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
