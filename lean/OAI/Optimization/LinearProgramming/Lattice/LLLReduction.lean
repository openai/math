import OAI.Optimization.LinearProgramming.Lattice.LLLScale
import OAI.Optimization.LinearProgramming.Lattice.LLLRational

/-! The executable reduction from rational generators to integer LLL. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

variable {p n : ℕ}

/-- An integral row divided by a common positive denominator, as an integer-linear map. -/
def unscaleIntegerRow (d : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun x j := (x j : ℚ) / d
  map_add' x y := by ext j; simp [add_div]
  map_smul' a x := by ext j; simp [zsmul_eq_mul, mul_div_assoc]

/-- Integer rows viewed in the Euclidean ambient space. -/
def euclideanIntegerRow (b : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (b j : ℝ))

private theorem euclideanRow_unscale (d : ℕ) (v : Fin n → ℤ) :
    euclideanRow (unscaleIntegerRow d v) = (d : ℝ)⁻¹ • euclideanIntegerRow v := by
  ext j
  simp [euclideanRow, euclideanIntegerRow, unscaleIntegerRow, div_eq_mul_inv, mul_comm]

private theorem unscale_integralRows (A : Matrix (Fin p) (Fin n) ℚ) (i : Fin p) :
    unscaleIntegerRow (matrixDenominator A) (integralRows A i) = A i := by
  ext j
  change (integralRows A i j : ℚ) / (matrixDenominator A : ℚ) = A i j
  rw [integralRows_spec, mul_div_cancel_left₀ _ (by exact_mod_cast (matrixDenominator_pos A).ne')]

private theorem euclidean_integralRows (A : Matrix (Fin p) (Fin n) ℚ) (i : Fin p) :
    euclideanIntegerRow (integralRows A i) = (matrixDenominator A : ℝ) • euclideanRow (A i) := by
  ext j
  change (integralRows A i j : ℝ) = (matrixDenominator A : ℝ) * (A i j : ℝ)
  exact_mod_cast integralRows_spec A i j

/-- Clearing denominators preserves real row independence. -/
theorem integralRows_linearIndependent (A : Matrix (Fin p) (Fin n) ℚ)
    (hA : LinearIndependent ℝ (fun i => euclideanRow (A i))) :
    LinearIndependent ℝ (fun i => euclideanIntegerRow (integralRows A i)) := by
  have hd : (matrixDenominator A : ℝ) ≠ 0 := by exact_mod_cast (matrixDenominator_pos A).ne'
  simp_rw [euclidean_integralRows]
  exact hA.units_smul (fun _ => Units.mk0 (matrixDenominator A : ℝ) hd)

/-- Clear the denominators, apply the supplied integer reduction, and scale the rows back. -/
def reduceRationalWith (red : Matrix (Fin p) (Fin n) ℤ → Matrix (Fin p) (Fin n) ℤ)
    (A : Matrix (Fin p) (Fin n) ℚ) : Matrix (Fin p) (Fin n) ℚ :=
  fun i => unscaleIntegerRow (matrixDenominator A) (red (integralRows A) i)

/-- A correct integer reducer yields a rational reducer preserving the precise integer row lattice
and both LLL inequalities in the original Euclidean coordinates. -/
theorem reduceRationalWith_spec
    (red : Matrix (Fin (p+1)) (Fin n) ℤ → Matrix (Fin (p+1)) (Fin n) ℤ)
    (hred : ∀ B, LinearIndependent ℝ (fun i => euclideanIntegerRow (B i)) →
      LLLReduced (fun i => euclideanIntegerRow (red B i)) ∧
      Submodule.span ℤ (Set.range (red B)) = Submodule.span ℤ (Set.range B))
    (A : Matrix (Fin (p+1)) (Fin n) ℚ) (hA : LinearIndependent ℝ (fun i => euclideanRow (A i))) :
    LLLReduced (fun i => euclideanRow (reduceRationalWith red A i)) ∧
      Submodule.span ℤ (Set.range (reduceRationalWith red A)) = Submodule.span ℤ (Set.range A) := by
  have hd : (matrixDenominator A : ℝ) ≠ 0 := by exact_mod_cast (matrixDenominator_pos A).ne'
  obtain ⟨hlll, hspan⟩ := hred (integralRows A) (integralRows_linearIndependent A hA)
  refine ⟨?_, ?_⟩
  · simpa only [reduceRationalWith, euclideanRow_unscale] using hlll.scale (inv_ne_zero hd)
  · let f := unscaleIntegerRow (n := n) (matrixDenominator A)
    have hout : Set.range (reduceRationalWith red A) = f '' Set.range (red (integralRows A)) :=
      Set.range_comp' f (red (integralRows A))
    have hin : (fun i => f (integralRows A i)) = A := funext (unscale_integralRows A)
    have hm := congrArg (Submodule.map f) hspan
    rw [Submodule.map_span, Submodule.map_span] at hm
    have hin' : f '' Set.range (integralRows A) = Set.range A :=
      (Set.range_comp' f (integralRows A)).symm.trans (congrArg Set.range hin)
    exact (congrArg (Submodule.span ℤ) hout).trans (hm.trans (congrArg (Submodule.span ℤ) hin'))

end Lattice
end LinearProgramming
end Optimization
end OAI
