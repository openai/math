import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.TriangleAPFormat
import OAI.LinearAlgebra.SpectralBooks.PlacedSpectralWires

/-! # The price of a three-wire tensor

The cyclic basis presentation of the three wires is matrix multiplication in
the same three pairs of coordinates. Its spectral value factors into the
values on its three edges. A quadratic lower bound on its subrank therefore
bounds the price of the full diagonal by half the perimeter.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open SiteTensor Foundation
open scoped NNReal Classical

/-- The cyclic three-wire basis tensor in the fixed pair-coordinate format is
the matrix multiplication tensor. -/
theorem triangleWire_class (K : Type*) [Field K] (q : ℕ) :
    ofCoeffs (Crossing.basisTensor (F := K) (triangleWireTerm q)) =
      ofRaw (ofThree (matrixTensor K q q q)) := by
  classical
  let e : ∀ i : Fin 3, (Fin q × Fin q) ≃ (ofThree (matrixTensor K q q q)).Leg i :=
    Fin.cons (Equiv.refl _) (Fin.cons (Equiv.refl _) (Fin.cons (Equiv.refl _) (fun i ↦ i.elim0)))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (show
    (if (x 0).2 = (x 1).1 ∧ (x 1).2 = (x 2).1 ∧ (x 2).2 = (x 0).1
     then (1 : K) else 0) = _ from ?_)
  swap
  · unfold ofThree matrixTensor Tensor.matrixCoefficients
    congr 1
  simp only [Crossing.basisTensor]
  let s := ((x 0).1, (x 0).2, (x 1).2)
  have he (t : Fin q × Fin q × Fin q) : x = triangleWireTerm q t ↔
      (x 0).2 = (x 1).1 ∧ (x 1).2 = (x 2).1 ∧ (x 2).2 = (x 0).1 ∧ t = s := by
    constructor
    · intro h
      subst x
      exact ⟨rfl,rfl,rfl,rfl⟩
    · rintro ⟨h₁, h₂, h₃, rfl⟩
      funext i
      fin_cases i
      · rfl
      · exact Prod.ext h₁.symm rfl
      · exact Prod.ext h₂.symm h₃
  simp_rw [he]
  by_cases h₁ : (x 0).2 = (x 1).1 <;> by_cases h₂ : (x 1).2 = (x 2).1 <;>
    by_cases h₃ : (x 2).2 = (x 0).1 <;> simp [h₁, h₂, h₃]

/-- Evaluating the cyclic basis tensor is multiplication of all three wire values. -/
theorem triangleWire_value (K : Type*) [Field K] (q : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop)) :
    coeffValue φ (Crossing.basisTensor (F := K) (triangleWireTerm q)) =
      φ.val (ofRaw (Raw.maskDiagonal K {0,1} (Fin q))) *
        φ.val (ofRaw (Raw.maskDiagonal K {1,2} (Fin q))) *
        φ.val (ofRaw (Raw.maskDiagonal K {2,0} (Fin q))) := by
  rw [coeffValue, triangleWire_class, ← ofRaw_ofThree_wire12, ← ofRaw_ofThree_wire23,
    ← ofRaw_ofThree_wire31]
  let ψ := rankFunctionalOfSpectrum φ
  change ψ.value (matrixTensor K q q q) = ψ.value (wire12 K q) * ψ.value (wire23 K q) *
    ψ.value (wire31 K q)
  rw [matrixTensor_eq_wireProduct, ψ.pullback_equiv, ψ.product, ψ.product]

/-- If the three-wire tensor of order `2r` yields a diagonal of dimension
`r²` geometrically, its three binary edge log prices sum to at least two. -/
theorem two_le_sum_binary_wire_logs {K : Type*} [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))
    (hbound : ∀ r : ℕ, (r : ℝ≥0) ^ 2 ≤
      coeffValue φ (Crossing.basisTensor (F := K) (triangleWireTerm (2 * r)))) :
    let D (i j : Fin 3) := Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K {i,j} (Fin 2))) : ℝ)
    2 ≤ D 0 1 + D 1 2 + D 2 0 := by
  let D (i j : Fin 3) (q : ℕ) := (φ.val (ofRaw (Raw.maskDiagonal K {i,j} (Fin q))) : ℝ)
  let b := Real.logb 2 (D 0 1 2) + Real.logb 2 (D 1 2 2) + Real.logb 2 (D 2 0 2)
  change 2 ≤ b
  have hb (n : ℕ) : 2 * (n : ℝ) ≤ b * (n+1) := by
    let r := 2 ^ n
    let q := 2 * r
    have hr : 0 < r := by positivity
    have hq : 0 < q := by positivity
    have h := hbound r
    rw [triangleWire_value] at h
    have h' : (r : ℝ)^2 ≤ D 0 1 q * D 1 2 q * D 2 0 q := by exact_mod_cast h
    have hpos (i j : Fin 3) : 0 < D i j q := by
      let : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
      have hne := Raw.maskDiagonal_ne_zero (K := K) {i,j} (Finset.insert_nonempty _ _) (Fin q)
      have hone := φ.property.2.2.2.2 _ _ (show (1 : TensorClass.{0} (Fin 3) K) ≤ ofRaw (Raw.maskDiagonal K {i,j} (Fin q)) from
        Raw.one_restricts_of_nonzero _ hne)
      rw [φ.property.2.1] at hone
      exact_mod_cast zero_lt_one.trans_le hone
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity) h'
    have logr : Real.logb 2 r = n := by simp [r, Real.logb_pow]
    have logq : Real.logb 2 q = n+1 := by
      simp [q, Nat.cast_mul, Real.logb_mul, hr.ne', logr, add_comm]
    have scale (i j : Fin 3) : Real.logb 2 (D i j q) = Real.logb 2 (D i j 2) * (n+1) := by
      rw [← logq]
      exact maskDiagonal_log_price φ {i,j} (Finset.insert_nonempty _ _) hq
    rw [Real.logb_pow, logr, Real.logb_mul (mul_pos (hpos 0 1) (hpos 1 2)).ne' (hpos 2 0).ne',
      Real.logb_mul (hpos 0 1).ne' (hpos 1 2).ne', scale, scale, scale] at hlog
    simpa only [b, add_mul, Nat.cast_ofNat] using hlog
  by_contra! hsmall
  obtain ⟨n, hn⟩ := exists_nat_gt (b / (2-b))
  have := (div_lt_iff₀ (sub_pos.mpr hsmall)).mp hn
  linarith [hb n]

end SpectralBooks
end LinearAlgebra
end OAI
