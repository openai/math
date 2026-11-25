import OAI.Computability.NearSquareRoot.PrecisionButterfly
import OAI.Computability.NearSquareRoot.PrecisionInvSqrtWord

/-! # One normalized Walsh bit with a computed binary scaling constant -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication

private theorem walshNormalization : 2 * SynchronizedPair.w ^ 2 = 1 := by
  rw [SynchronizedPair.w, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

variable (ι : Type*) [Fintype ι]

/-- Exact normalized Walsh on the least significant bit. Each contiguous
pair of tape records is one fiber. -/
noncomputable def directWalsh : EuclideanSpace ℂ (ι × Bool) →ₗᵢ[ℂ] EuclideanSpace ℂ (ι × Bool) where
  toFun x := WithLp.toLp 2 (fun j => (SynchronizedPair.w : ℂ) *
    butterflySum j.2 (x (j.1,false)) (x (j.1,true)))
  map_add' x y := by
    ext ⟨j,b⟩
    cases b <;> simp [butterflySum, PiLp.add_apply] <;> ring
  map_smul' z x := by
    ext ⟨j,b⟩
    cases b <;> simp [butterflySum, PiLp.smul_apply] <;> ring
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_bool]
    apply Finset.sum_congr rfl
    intro i _
    change ‖(SynchronizedPair.w : ℂ) * (x (i,false) - x (i,true))‖ ^ 2 +
        ‖(SynchronizedPair.w : ℂ) * (x (i,false) + x (i,true))‖ ^ 2 = _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have hp := parallelogram_law_with_norm ℂ (x (i,false)) (x (i,true))
    linear_combination SynchronizedPair.w^2 * hp +
      (‖x (i,false)‖^2 + ‖x (i,true)‖^2) * walshNormalization

/-- Applying the same layer again gives its inverse transform. -/
theorem directWalsh_involutive : Function.Involutive (directWalsh ι) := by
  have hw : 2 * (SynchronizedPair.w : ℂ)^2 = 1 := by exact_mod_cast walshNormalization
  intro x
  ext ⟨i,b⟩
  cases b <;>
    simp only [directWalsh, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      PiLp.toLp_apply, butterflySum, Bool.false_eq_true, ite_false, ite_true] <;>
    first | linear_combination x (i,false) * hw | linear_combination x (i,true) * hw

/-- Record prepared by the P192 binary integer square-root program for each
direct two-point normalization. -/
def butterflyCoefficient (k : ℕ) : Record k :=
  invSqrtRecord (fractionBits k) (componentBits k) 2

theorem butterflyCoefficient_error (k : ℕ) :
    ‖value k (butterflyCoefficient k) - (SynchronizedPair.w : ℂ)‖ ≤ 1 / (2 : ℝ)^(70*k) := by
  have h := invSqrtRecord_error (p := fractionBits k) (w := componentBits k) (by decide : 0 < 2)
    (by unfold fractionBits componentBits; omega)
  apply h.le.trans
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (by unfold fractionBits; omega)

/-- Layer-local guarantee for every permitted represented input. The
coefficient is computed on the finite grid and is independent of the inputs. -/
theorem directWalsh_record_error {k : ℕ} (hk : 1 ≤ k) (hcard : Fintype.card (ι × Bool) ≤ 2^k)
    (x : ι × Bool → Record k) (hx : ‖recordArray x‖ ≤ (2 : ℝ)^(13*k)) :
    ‖recordArray (fun j : ι × Bool =>
        normalizedBranch k j.2 (x (j.1,false)) (x (j.1,true)) (butterflyCoefficient k)) -
      directWalsh ι (recordArray x)‖ ≤ 1 / (2 : ℝ)^(50*k) :=
  directWalshLayer_error hk hcard x _ hx (butterflyCoefficient_error k)

end FixedPoint

end NearSquareRoot
end Computability
end OAI
