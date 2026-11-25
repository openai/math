import OAI.Computability.NearSquareRoot.KernelScaleBank
import OAI.Computability.NearSquareRoot.PrecisionDiagonal

/-! # Euclidean gain and numerical accuracy of a selected dyadic scale

The same gain bounds every active address and spectator copy. The truncation
error accounts for every complex record output in the bank.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelScaleNorm
open IntegerMultiplication KernelPass
variable {q : ℕ} {ι : Type*} [Fintype ι]

def gain (t : (Fin q → ZMod 2) → Coefficient) : ℕ :=
  1 + Finset.univ.sup (fun s => (t s).1.natAbs)

private theorem norm_value_bound (a : Coefficient) : ‖(value a : ℂ)‖ ≤ (a.1.natAbs : ℝ) := by
  rw [value]
  push_cast
  simp only [norm_div, Complex.norm_intCast, norm_pow]
  rw [Complex.norm_ofNat, div_le_iff₀ (by positivity)]
  simpa using le_mul_of_one_le_right (abs_nonneg (a.1 : ℝ))
    (one_le_pow₀ (show 1 ≤ ‖(2:ℂ)‖ by norm_num) : 1 ≤ ‖(2:ℂ)‖^a.2)

theorem table_bound (t : (Fin q → ZMod 2) → Coefficient) (s : Fin q → ZMod 2) :
    ‖(value (t s) : ℂ)‖ ≤ gain t := by
  apply (norm_value_bound _).trans
  have hs := Finset.le_sup (f := fun j => (t j).1.natAbs) (Finset.mem_univ s)
  exact_mod_cast (show (t s).1.natAbs ≤ gain t by unfold gain; omega)

noncomputable def action (t : (Fin q → ZMod 2) → Coefficient) (key : ι → Fin q → ZMod 2)
    (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun z => (value (t (key z)) : ℂ) * v z

theorem gain_bound (t : (Fin q → ZMod 2) → Coefficient) (key : ι → Fin q → ZMod 2)
    (v : EuclideanSpace ℂ ι) : ‖action t key v‖ ≤ gain t * ‖v‖ := by
  apply euclidean_norm_le_mul_of_coordinates _ _ (by positivity)
  intro z
  change ‖(value (t (key z)) : ℂ) * v z‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (table_bound _ _) (norm_nonneg _)

/-- In the single-bank index type this pointwise map is the interpreted
normalized instruction. -/
theorem action_matrix {A h : ℕ} (test : Column A → Fin q → ZMod 2)
    (t : (Fin q → ZMod 2) → Coefficient) (v : EuclideanSpace ℂ (Fin 1 × Addr A h)) :
    action t (fun z => ∑ j, test (z.2 j)) v =
      WithLp.toLp 2 (Matrix.mulVec (((Plan.scale q test t).eval h).map (fun r => (r : ℂ))) v.ofLp) := by
  apply WithLp.ofLp_injective
  funext z
  rcases z with ⟨j,y⟩
  have e : j = 0 := Subsingleton.elim _ _
  subst j
  exact (KernelScaleBank.scale_mulVec test t v.ofLp y).symm

private theorem raw_norm (p w : ℕ) (t : (Fin q → ZMod 2) → Coefficient)
    (key : ι → Fin q → ZMod 2) (x : ι → Dusk.Grain w) (M : ℝ)
    (hb : ‖(WithLp.toLp 2 (Grid.meaning p w ∘ x) : EuclideanSpace ℂ ι)‖ ≤ M)
    (hw : (gain t : ℝ)*M*2^p < 2^w) (i : ι) :
    ‖(value (t (key i)) : ℂ) * Grid.toC (Grid.aspect (x i))‖ < (2:ℝ)^w := by
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 (Grid.meaning p w ∘ x)
  have hs := (PiLp.norm_apply_le (action t key v) i).trans ((gain_bound t key v).trans
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)))
  change ‖(value (t (key i)) : ℂ) * (Grid.toC (Grid.aspect (x i)) / 2^p)‖ ≤ _ at hs
  rw [← mul_div_assoc, norm_div, norm_pow, Complex.norm_ofNat, div_le_iff₀ (by positivity)] at hs
  exact hs.trans_lt hw

theorem fits_of_norm (p w : ℕ) (t : (Fin q → ZMod 2) → Coefficient)
    (key : ι → Fin q → ZMod 2) (x : ι → Dusk.Grain w) (M : ℝ)
    (hb : ‖(WithLp.toLp 2 (Grid.meaning p w ∘ x) : EuclideanSpace ℂ ι)‖ ≤ M)
    (hw : (gain t : ℝ)*M*2^p < 2^w) (i : ι) :
    KernelScaleRecord.fits (t (key i)) (x i) :=
  KernelScaleRecord.fits_of_norm _ _ (raw_norm p w t key x M hb hw i)

theorem round_scale_perturbed (p w : ℕ) (t : (Fin q → ZMod 2) → Coefficient)
    (key : ι → Fin q → ZMod 2) (x : ι → Dusk.Grain w) (u : EuclideanSpace ℂ ι) (M : ℝ)
    (hb : ‖(WithLp.toLp 2 (Grid.meaning p w ∘ x) : EuclideanSpace ℂ ι)‖ ≤ M)
    (hw : (gain t : ℝ)*M*2^p < 2^w) :
    ‖WithLp.toLp 2 (fun z => Grid.meaning p w (KernelScaleRecord.rounded (t (key z)) (x z))) -
      action t key u‖ ≤ Real.sqrt (Fintype.card ι) * (2/(2:ℝ)^p) +
        gain t * ‖WithLp.toLp 2 (Grid.meaning p w ∘ x) - u‖ := by
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 (Grid.meaning p w ∘ x)
  have sub : action t key v - action t key u = action t key (v-u) := by
    ext z
    exact (mul_sub _ _ _).symm
  apply (norm_sub_le_norm_sub_add_norm_sub _ (action t key v) _).trans
  apply add_le_add _ ((sub ▸ gain_bound t key (v-u)))
  apply euclidean_norm_le_of_coordinates _ (by positivity)
  intro i
  exact KernelScaleRecord.error _ _ _ (raw_norm p w t key x M hb hw i)

end KernelScaleNorm

end NearSquareRoot
end Computability
end OAI
