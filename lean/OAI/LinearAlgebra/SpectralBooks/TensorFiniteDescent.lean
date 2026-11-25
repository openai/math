import OAI.LinearAlgebra.SpectralBooks.TensorDiagonalCopies
import OAI.LinearAlgebra.SpectralBooks.ScalarExtensionSpectrum
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
import OAI.LinearAlgebra.SpectralBooks.PolynomialOverhead
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Descending tensor restriction along finite scalar extensions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v
open scoped Classical
variable {I K L : Type*} [Fintype I] [Field K] [Field L] [Algebra K L]

/-- Expand a product of extension-field matrix entries in a fixed ground-field
basis and project its output back to the ground field. -/
private theorem retract_prod {D : Type*} [Fintype D] (b : Module.Basis D K L)
    (P : L →ₗ[K] K) (m : I → L) :
    P (∏ i, m i) = ∑ j : I → D, P (∏ i, b (j i)) * ∏ i, b.repr (m i) (j i) := by
  classical
  have hm (i : I) : m i = ∑ j, algebraMap K L (b.repr (m i) j) * b j := by
    simpa only [Algebra.smul_def] using (b.sum_repr (m i)).symm
  conv_lhs => arg 2; arg 2; ext i; rw [hm i]
  rw [Fintype.prod_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.prod_mul_distrib, ← map_prod, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- Multiplying by a ground scalar before retraction multiplies the output by
the same scalar. -/
private theorem retract_mul (P : L →ₗ[K] K) (a : K) (b : L) :
    P (algebraMap K L a * b) = a * P b := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- A restriction over a degree-`d` extension expands in a basis into at
most `d ^ card I` restrictions over the ground field. -/
private theorem descend_coefficients [Nonempty I] [FiniteDimensional K L]
    {X Y : Raw.{v} I K}
    (h : (X.mapScalars (algebraMap K L)).Restricts (Y.mapScalars (algebraMap K L))) :
    let D := Fin (Module.finrank K L)
    ∃ M : ∀ (_ : I → D) i, X.Leg i → Y.Leg i → K, ∀ x, X.coeff x =
      ∑ j : I → D, ∑ y, Y.coeff y * ∏ i, M j i (x i) (y i) := by
  classical
  let D := Fin (Module.finrank K L)
  let b := Module.finBasis K L
  obtain ⟨P, hP⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective K L))
  obtain ⟨N, hN⟩ := h
  let t := Classical.arbitrary I
  let M (j : I → D) (i : I) (x : X.Leg i) (y : Y.Leg i) :=
    (if t = i then P (∏ k, b (j k)) else 1) * b.repr (N i x y) (j i)
  refine ⟨M, fun x => ?_⟩
  have hx := LinearMap.congr_fun hP (X.coeff x)
  change P (algebraMap K L (X.coeff x)) = X.coeff x at hx
  have heq := hN x
  change algebraMap K L (X.coeff x) =
    ∑ y, algebraMap K L (Y.coeff y) * ∏ i, N i (x i) (y i) at heq
  rw [← hx, heq, map_sum]
  have hterm (y : ∀ i, Y.Leg i) := retract_prod b P (fun i => N i (x i) (y i))
  simp_rw [retract_mul, hterm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro y _
  simp only [M, Finset.prod_mul_distrib, Fintype.prod_ite_eq]

/-- A restriction after a finite field extension descends at a uniform
cost of at most the extension degree to the number of sites. -/
theorem le_nat_mul_of_finite_baseChange [Nonempty I] [FiniteDimensional K L]
    {X Y : TensorClass.{v} I K}
    (h : mapScalars (algebraMap K L) X ≤ mapScalars (algebraMap K L) Y) :
    X ≤ ((Module.finrank K L ^ Fintype.card I : ℕ) : TensorClass.{v} I K) * Y := by
  classical
  induction X using Quotient.inductionOn with | _ X
  induction Y using Quotient.inductionOn with | _ Y
  change (X.mapScalars (algebraMap K L)).Restricts (Y.mapScalars (algebraMap K L)) at h
  obtain ⟨M, hM⟩ := descend_coefficients h
  let W := I → Fin (Module.finrank K L)
  let A := ULift.{v} (Fin (Fintype.card W))
  let e : A ≃ W := Equiv.ulift.trans (Fintype.equivFin W).symm
  have hc : X.Restricts ((Raw.diagonal I K A).mul Y) := by
    apply Raw.restricts_diagonal_mul_of_coefficients
    refine ⟨fun a => M (e a), fun x => ?_⟩
    rw [hM]
    exact (e.sum_comp _).symm
  change ofRaw X ≤ _ * ofRaw Y
  simpa only [ofRaw_mul, ofRaw_diagonal_eq_natCast, A, W, Fintype.card_ulift,
    Fintype.card_fin, Fintype.card_fun] using ofRaw_le_iff.mpr hc

/-- Every ground spectral point respects restrictions between ground tensors
established over a finite extension. The degree cost is independent of the
power, and therefore disappears after taking roots. -/
theorem spectral_le_of_finite_baseChange [Nonempty I] [FiniteDimensional K L]
    (φ : normalizedSpectrum (S := TensorClass.{v} I K) (· ≤ ·))
    {X Y : TensorClass.{v} I K}
    (h : mapScalars (algebraMap K L) X ≤ mapScalars (algebraMap K L) Y) :
    φ.val X ≤ φ.val Y := by
  let ψ := normalizedSpectrum.toRingHom φ
  let C := Module.finrank K L ^ Fintype.card I
  have hpow (n : ℕ) : mapScalars (algebraMap K L) (X ^ n) ≤ mapScalars (algebraMap K L) (Y ^ n) := by
    simp only [map_pow]
    induction n with
    | zero => simp
    | succ n ih => simpa only [pow_succ] using mul_mono ih h
  apply nnreal_le_of_pow_le_polynomial_mul_pow C
  intro n hn
  have hh : ψ (X ^ n) ≤ ψ ((C : TensorClass.{v} I K) * Y ^ n) :=
    φ.property.2.2.2.2 _ _ (le_nat_mul_of_finite_baseChange (hpow n))
  rw [map_mul, map_pow, map_pow, map_natCast] at hh
  have hC : C ≤ (n + 1) ^ C :=
    C.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) _)
  exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (by positivity))

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
