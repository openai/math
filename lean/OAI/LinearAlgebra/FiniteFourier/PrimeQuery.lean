import OAI.LinearAlgebra.FiniteFourier.Cyclic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-! # The quadratic query on two Fourier digits

The positive-sign transform uses the phase `ζ^(xX)`. Summing the
quadratic multiplier in both frequencies gives a scaled Fourier matrix
with the input digits exchanged and one diagonal phase on each side.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open scoped Kronecker

variable {ℓ : ℕ} [NeZero ℓ]

section Coefficients
variable {K : Type*} [CommRing K] {ζ : K}

/-- Evaluate a phase at a residue, using its least nonnegative representative. -/
def digitPhase (hζ : IsPrimitiveRoot ζ ℓ) : AddChar (ZMod ℓ) K :=
  AddChar.zmodChar ℓ hζ.pow_eq_one

theorem digitPhase_apply (hζ : IsPrimitiveRoot ζ ℓ) (x : ZMod ℓ) :
    digitPhase hζ x = ζ ^ x.val := rfl

/-- Orthogonality for the chosen root of unity in the coefficient ring. -/
class PrimeSpectrumOrthogonal (hζ : IsPrimitiveRoot ζ ℓ) : Prop where
  sum_eq (b : ZMod ℓ) :
    ∑ z : ZMod ℓ, digitPhase hζ (z * b) = if b = 0 then (ℓ : K) else 0

instance [IsDomain K] (hζ : IsPrimitiveRoot ζ ℓ) : PrimeSpectrumOrthogonal hζ where
  sum_eq b := by
    have h := AddChar.sum_mulShift b (AddChar.zmodChar_primitive_of_primitive_root ℓ hζ)
    by_cases hb : b = 0
    · simp [hb, ZMod.card]
    · simpa [digitPhase, hb] using h

/-- Translating the frequency sum by one multiplies it by `ζ^b`. A unit
difference therefore annihilates the sum only when the sum vanishes. -/
theorem digitPhase_orthogonality_of_unit_sub (hζ : IsPrimitiveRoot ζ ℓ)
    (hu : ∀ n : ℕ, 0 < n → n < ℓ → IsUnit (ζ ^ n - 1)) (b : ZMod ℓ) :
    ∑ z : ZMod ℓ, digitPhase hζ (z * b) = if b = 0 then (ℓ : K) else 0 := by
  by_cases hb : b = 0
  · simp [hb, ZMod.card]
  rw [ite_eq_right hb]
  let S := ∑ z : ZMod ℓ, digitPhase hζ (z * b)
  have hshift : digitPhase hζ b * S = S := calc
    _ = ∑ z : ZMod ℓ, digitPhase hζ ((1 + z) * b) := by
      simp [S, add_mul, AddChar.map_add_eq_mul, Finset.mul_sum]
    _ = S := Equiv.sum_comp (Equiv.addLeft (1 : ZMod ℓ)) (fun z : ZMod ℓ => digitPhase hζ (z * b))
  apply (hu b.val (ZMod.val_pos.mpr hb) b.val_lt).isRegular.left
  change (ζ^b.val - 1) * S = (ζ^b.val - 1) * 0
  rw [sub_mul, ← digitPhase_apply hζ b, hshift, one_mul, sub_self, mul_zero]

theorem PrimeSpectrumOrthogonal.of_unit_sub (hζ : IsPrimitiveRoot ζ ℓ)
    (hu : ∀ n : ℕ, 0 < n → n < ℓ → IsUnit (ζ ^ n - 1)) : PrimeSpectrumOrthogonal hζ :=
  ⟨digitPhase_orthogonality_of_unit_sub hζ hu⟩

/-- Character orthogonality is preserved by a coefficient homomorphism. -/
theorem PrimeSpectrumOrthogonal.map (hζ : IsPrimitiveRoot ζ ℓ) [h : PrimeSpectrumOrthogonal hζ]
    {S : Type*} [CommRing S] (φ : K →+* S) (hξ : IsPrimitiveRoot (φ ζ) ℓ) :
    PrimeSpectrumOrthogonal hξ where
  sum_eq b := by
    have hsum := congrArg φ (h.sum_eq b)
    simpa only [map_sum, digitPhase_apply, map_pow, apply_ite φ, map_natCast, map_zero] using hsum

/-- Summing a frequency digit produces a Kronecker delta at zero. -/
theorem digitPhase_orthogonality (hζ : IsPrimitiveRoot ζ ℓ) [h : PrimeSpectrumOrthogonal hζ]
    (b : ZMod ℓ) :
    ∑ z : ZMod ℓ, digitPhase hζ (z * b) = if b = 0 then (ℓ : K) else 0 :=
  h.sum_eq b

/-- The unnormalized sum, including for the manuscript's cyclotomic coefficient ring. -/
theorem sum_quadratic_query_phase (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (a : (ZMod ℓ)ˣ)
    (x y s t : ZMod ℓ) :
    (∑ X : ZMod ℓ, ∑ Z : ZMod ℓ,
      digitPhase hζ ((x - s) * X + (y - t) * Z + (a : ZMod ℓ) * X * Z)) =
        digitPhase hζ ((x - s) * ((a⁻¹ : (ZMod ℓ)ˣ) * (t - y))) * (ℓ : K) := by
  let freq : ZMod ℓ := (a⁻¹ : (ZMod ℓ)ˣ) * (t - y)
  have inner (X : ZMod ℓ) :
      (∑ Z : ZMod ℓ, digitPhase hζ ((x - s) * X + (y - t) * Z + (a : ZMod ℓ) * X * Z)) =
        if X = freq then digitPhase hζ ((x - s) * X) * (ℓ : K) else 0 := by
    have phase (Z : ZMod ℓ) :
        (x - s) * X + (y - t) * Z + (a : ZMod ℓ) * X * Z =
          (x - s) * X + Z * ((a : ZMod ℓ) * X - (t - y)) := by ring
    simp_rw [phase, AddChar.map_add_eq_mul]
    rw [← Finset.mul_sum, digitPhase_orthogonality]
    have heq : (a : ZMod ℓ) * X - (t - y) = 0 ↔ X = freq := by
      rw [sub_eq_zero, eq_comm, ← a.inv_mul_eq_iff_eq_mul, eq_comm]
    by_cases hX : X = freq
    · rw [ite_eq_left hX, ite_eq_left (heq.mpr hX)]
    · rw [ite_eq_right hX, ite_eq_right (heq.not.mpr hX), mul_zero]
  simp_rw [inner]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, freq]

/-- Quadratic summation over any coefficient ring with unit differences. -/
theorem sum_quadratic_query_phase_of_unit_sub (hζ : IsPrimitiveRoot ζ ℓ)
    (hu : ∀ n : ℕ, 0 < n → n < ℓ → IsUnit (ζ ^ n - 1)) (a : (ZMod ℓ)ˣ)
    (x y s t : ZMod ℓ) :
    (∑ X : ZMod ℓ, ∑ Z : ZMod ℓ,
      digitPhase hζ ((x - s) * X + (y - t) * Z + (a : ZMod ℓ) * X * Z)) =
        digitPhase hζ ((x - s) * ((a⁻¹ : (ZMod ℓ)ˣ) * (t - y))) * (ℓ : K) := by
  let := PrimeSpectrumOrthogonal.of_unit_sub hζ hu
  exact sum_quadratic_query_phase hζ a x y s t

end Coefficients

variable {K : Type*} [Field K] {ζ : K}

/-- Fourier inversion of a quadratic phase with any invertible coefficient.
For prime order this covers all nonzero powers of a query. -/
theorem primeQuery_kernel_unit (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (x y s t : ZMod ℓ) :
    (ℓ : K)⁻¹ ^ 2 * (∑ X : ZMod ℓ, ∑ Z : ZMod ℓ,
      digitPhase hζ ((x - s) * X + (y - t) * Z + (a : ZMod ℓ) * X * Z)) =
        (ℓ : K)⁻¹ * digitPhase hζ ((x - s) * ((a⁻¹ : (ZMod ℓ)ˣ) * (t - y))) := by
  rw [sum_quadratic_query_phase]
  field_simp [hζ.neZero'.out]

/-- Fourier inversion of the quadratic query `(X,Z) ↦ ζ^(XZ)`. -/
theorem primeQuery_kernel (hζ : IsPrimitiveRoot ζ ℓ) (x y s t : ZMod ℓ) :
    (ℓ : K)⁻¹ ^ 2 * (∑ X : ZMod ℓ, ∑ Z : ZMod ℓ,
      digitPhase hζ ((x - s) * X + (y - t) * Z + X * Z)) =
        (ℓ : K)⁻¹ * digitPhase hζ ((x - s) * (t - y)) := by
  simpa using primeQuery_kernel_unit hζ 1 x y s t

/-- The surviving phase separates into input and output chirps and a swapped Fourier phase. -/
theorem primeQuery_kernel_factor (hζ : IsPrimitiveRoot ζ ℓ) (x y s t : ZMod ℓ) :
    digitPhase hζ ((x - s) * (t - y)) =
      digitPhase hζ (-(x * y)) * digitPhase hζ (-(s * t)) *
        digitPhase hζ (x * t) * digitPhase hζ (y * s) := by
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The matrix on one residue digit with the positive-sign DFT convention. -/
def digitDftMatrix (hζ : IsPrimitiveRoot ζ ℓ) : Matrix (ZMod ℓ) (ZMod ℓ) K :=
  Matrix.of fun u v => digitPhase hζ (u * v)

/-- Ordering the residue digits by their standard representatives recovers the cyclic DFT. -/
theorem reindex_digitDftMatrix (hζ : IsPrimitiveRoot ζ ℓ) :
    Matrix.reindex (ZMod.finEquiv ℓ).toEquiv.symm (ZMod.finEquiv ℓ).toEquiv.symm
      (digitDftMatrix hζ) = dftMatrix ℓ ζ := by
  ext i j
  change ζ ^ ((ZMod.finEquiv ℓ i * ZMod.finEquiv ℓ j).val) = ζ ^ (i.val * j.val)
  rw [ZMod.val_mul, ← pow_eq_pow_mod _ hζ.pow_eq_one]
  cases ℓ with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl

/-- Unnormalized inverse Fourier phase on one digit. -/
private def backwardPhaseMatrix (hζ : IsPrimitiveRoot ζ ℓ) : Matrix (ZMod ℓ) (ZMod ℓ) K :=
  Matrix.of fun u v => digitPhase hζ (-(u * v))

/-- The product of queries in the ordinary basis on a single pair of digits. -/
def primeQueryMatrix (hζ : IsPrimitiveRoot ζ ℓ) : Matrix (ZMod ℓ × ZMod ℓ) (ZMod ℓ × ZMod ℓ) K :=
  ((ℓ : K)⁻¹ ^ 2) • ((backwardPhaseMatrix hζ ⊗ₖ backwardPhaseMatrix hζ) *
    Matrix.diagonal (fun w : ZMod ℓ × ZMod ℓ => digitPhase hζ (w.1 * w.2)) *
      (digitDftMatrix hζ ⊗ₖ digitDftMatrix hζ))

theorem primeQueryMatrix_apply (hζ : IsPrimitiveRoot ζ ℓ) (x y s t : ZMod ℓ) :
    primeQueryMatrix hζ (s, t) (x, y) = (ℓ : K)⁻¹ * digitPhase hζ ((x - s) * (t - y)) := by
  rw [← primeQuery_kernel hζ]
  simp only [primeQueryMatrix, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, digitDftMatrix, backwardPhaseMatrix, Matrix.kroneckerMap_apply,
    Matrix.of_apply, Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro X _
  apply Finset.sum_congr rfl
  intro Z _
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The ordinary query matrix differs from the swapped two-digit DFT by the
global scalar `1/ℓ` and one invertible diagonal phase on each side. -/
theorem primeQueryMatrix_eq_diagonal_swapped_dft (hζ : IsPrimitiveRoot ζ ℓ) :
    primeQueryMatrix hζ = (ℓ : K)⁻¹ •
      (Matrix.diagonal (fun p : ZMod ℓ × ZMod ℓ => digitPhase hζ (-(p.1 * p.2))) *
        (digitDftMatrix hζ ⊗ₖ digitDftMatrix hζ).submatrix id Prod.swap *
        Matrix.diagonal (fun p : ZMod ℓ × ZMod ℓ => digitPhase hζ (-(p.1 * p.2)))) := by
  ext ⟨s, t⟩ ⟨x, y⟩
  rw [primeQueryMatrix_apply, primeQuery_kernel_factor]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.submatrix_apply, Prod.swap_prod_mk, id_eq, Matrix.kroneckerMap_apply,
    digitDftMatrix, Matrix.of_apply]
  simp only [mul_comm s y, mul_comm t x]
  ring

/-- In the unrestricted binary circuit model the diagonal phases, normalization,
and digit exchange preserve the exact number of gates. -/
theorem complexity_primeQueryMatrix (hζ : IsPrimitiveRoot ζ ℓ) :
    complexity (primeQueryMatrix hζ) = complexity (digitDftMatrix hζ ⊗ₖ digitDftMatrix hζ) := by
  let M := digitDftMatrix hζ ⊗ₖ digitDftMatrix hζ
  let R := Matrix.reindex (Equiv.refl _) (Equiv.prodComm _ _) M
  let w := fun p : ZMod ℓ × ZMod ℓ => digitPhase hζ (-(p.1 * p.2))
  have hw (p) : w p ≠ 0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne ℓ))
  rw [primeQueryMatrix_eq_diagonal_swapped_dft, complexity_smul _ (inv_ne_zero hζ.neZero'.out)]
  have hmat : Matrix.diagonal w * M.submatrix id Prod.swap * Matrix.diagonal w =
      Matrix.of (fun o i => w o * (w i * R o i)) := by
    ext o i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    change w o * M o i.swap * w i = w o * (w i * M o i.swap)
    ring
  change complexity (Matrix.diagonal w * M.submatrix id Prod.swap * Matrix.diagonal w) = complexity M
  rw [hmat, complexity_diagonal _ w w hw hw]
  exact complexity_reindex _ _ _

end

end

end FiniteFourier
end LinearAlgebra
end OAI
