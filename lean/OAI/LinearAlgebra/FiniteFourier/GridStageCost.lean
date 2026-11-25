import OAI.LinearAlgebra.FiniteFourier.ExtensionCostBound
import OAI.LinearAlgebra.FiniteFourier.MonomialLayer
import OAI.LinearAlgebra.FiniteFourier.ShearLayerCost
import OAI.LinearAlgebra.FiniteFourier.ShearDescent

/-! # Cost of a pair of extension-field grid layers -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- A monomial layer charges fixed-scalar multiplication at each spatial
coordinate. A shear layer charges a ground-field layer at each basis
coordinate. The resulting bounds have the same dependence on both sizes. -/
theorem grid_stage_cost {K E : Type*} [Field K] [Field E] [Algebra K E]
    {I : Type} [Fintype I] [DecidableEq I] (b : PowerBasis K E)
    {β C t : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) (hC : 0 ≤ C)
    (hconv : FixedConvolutionBound K β C) (hshear : ShearTensorBound K β C)
    (hI : 0 < Fintype.card I) (he : Real.logb 2 b.dim ≤ t) (hsp : Real.logb 2 (Fintype.card I) ≤ t) :
    ∃ mc sc : ℕ,
      (∀ M : Matrix I I E, LayerMatrix .monomial M → RealizableAtMost (restrictMatrix b.basis M) mc) ∧
      (∀ S : Matrix I I E, LayerMatrix .shear S → RealizableAtMost (restrictMatrix b.basis S) sc) ∧
      ((mc + sc : ℕ) : ℝ) ≤ (7*C+1) * b.dim * Fintype.card I * (1+t)^β := by
  let n := Fintype.card I
  let q := (1+t)^β
  have hlog (i : ℕ) (hi : 0 < i) : 0 ≤ Real.logb 2 i :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hi)
  have hq : 0 ≤ q := Real.rpow_nonneg (by linarith [hlog b.dim b.dim_pos]) _
  have hpow (i : ℕ) (hi : 0 < i) (ht : Real.logb 2 i ≤ t) : (1+Real.logb 2 i)^β ≤ q :=
    Real.rpow_le_rpow (by linarith [hlog i hi]) (by linarith) hβ
  let m := (6*C+1) * b.dim * q
  let s := C * n * q
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  refine ⟨n * ⌊m⌋₊, b.dim * ⌊s⌋₊, ?_, ?_, ?_⟩
  · intro M hM
    apply hM.restrictMatrix_monomial_uniform b.basis
    intro u
    apply (complexity_le_iff ..).mp
    apply Nat.le_floor
    exact (hconv.powerBasis_scalar hβ hβ' hC b u).trans
      (mul_le_mul_of_nonneg_left (hpow _ b.dim_pos he) (by positivity))
  · intro S hS
    have hcost (B : Matrix I I K) (hB : LayerMatrix .shear B) : RealizableAtMost B ⌊s⌋₊ := by
      apply (complexity_le_iff ..).mp
      apply Nat.le_floor
      exact (shearLayer_complexity_le hB hC hβ hshear).trans
        (mul_le_mul_of_nonneg_left (hpow _ hI hsp) (by positivity))
    simpa only [Fintype.card_fin] using realizable_restrict_shear b.basis hS hcost
  · push_cast
    calc
      _ ≤ (n : ℝ)*m + (b.dim : ℝ)*s := by
        exact add_le_add (mul_le_mul_of_nonneg_left (Nat.floor_le hm) (Nat.cast_nonneg _))
          (mul_le_mul_of_nonneg_left (Nat.floor_le hs) (Nat.cast_nonneg _))
      _ = _ := by dsimp [m,s,n,q]; ring

end FiniteFourier
end LinearAlgebra
end OAI
