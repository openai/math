import OAI.LinearAlgebra.FiniteFourier.PrimeDigits
import OAI.LinearAlgebra.FiniteFourier.PrimeQueryTuple

/-! # Positive Fourier phases on paired digit tuples -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K : Type*} [Field K] {ℓ k : ℕ} [NeZero ℓ] {ζ : K}

private theorem finEquiv_symm_val (z : ZMod ℓ) : ((ZMod.finEquiv ℓ).symm z).val = z.val := by
  cases ℓ with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ ℓ => rfl

/-- Concatenating the two digit tuples and exchanging the two frequency tuples turns
the bilinear phase into an entry of the positive-sign Fourier transform. -/
theorem pairedDigitPhase_eq_primeTransform (hζ : IsPrimitiveRoot ζ ℓ) (x y s t : Fin k → ZMod ℓ) :
    digitPhase hζ (∑ i, (x i * t i + y i * s i)) =
      primeTransform ℓ (k + k) ζ
        (Fin.append ((ZMod.finEquiv ℓ).symm ∘ x) ((ZMod.finEquiv ℓ).symm ∘ y))
        (Fin.append ((ZMod.finEquiv ℓ).symm ∘ t) ((ZMod.finEquiv ℓ).symm ∘ s)) := by
  rw [primeTransform_apply, Fin.prod_univ_add, digitPhase_sum]
  simp only [Fin.append_left, Fin.append_right, Function.comp_apply, finEquiv_symm_val,
    AddChar.map_add_eq_mul, Finset.prod_mul_distrib, digitPhase_apply, ZMod.val_mul,
    hζ.eq_orderOf, pow_mod_orderOf]

/-- Fourier inversion of the quadratic multiplier on paired tuples equals a scaled,
diagonally weighted and permuted Fourier transform on twice as many digits. -/
theorem primeTupleKernel_eq_primeTransform (hζ : IsPrimitiveRoot ζ ℓ) (x y s t : Fin k → ZMod ℓ) :
    primeTupleKernel hζ x y s t =
      (ℓ : K)⁻¹ ^ k * digitPhase hζ (-(∑ i, x i * y i)) * digitPhase hζ (-(∑ i, s i * t i)) *
        primeTransform ℓ (k + k) ζ
          (Fin.append ((ZMod.finEquiv ℓ).symm ∘ x) ((ZMod.finEquiv ℓ).symm ∘ y))
          (Fin.append ((ZMod.finEquiv ℓ).symm ∘ t) ((ZMod.finEquiv ℓ).symm ∘ s)) := by
  rw [primeTupleKernel_eq_fourierPhase, pairedDigitPhase_eq_primeTransform, Fintype.card_fin]

open scoped Classical in
/-- The ordinary quadratic kernel on two digit tuples and the positive-sign Fourier
transform on all their digits have the same unrestricted binary linear circuit size. -/
theorem complexity_primeTupleKernel (hζ : IsPrimitiveRoot ζ ℓ) (k : ℕ) :
    complexity (Matrix.of fun o i : (Fin k → ZMod ℓ) × (Fin k → ZMod ℓ) =>
      primeTupleKernel hζ i.1 i.2 o.1 o.2) = complexity (primeTransform ℓ (k + k) ζ) := by
  let e : (Fin k → ZMod ℓ) ≃ (Fin k → Fin ℓ) :=
    Equiv.piCongrRight fun _ => (ZMod.finEquiv ℓ).toEquiv.symm
  let pack := (e.prodCongr e).trans (Fin.appendEquiv k k)
  let swapPack := (Equiv.prodComm _ _).trans pack
  let M := primeTransform ℓ (k + k) ζ
  let R := Matrix.reindex swapPack.symm pack.symm M
  let w (p : (Fin k → ZMod ℓ) × (Fin k → ZMod ℓ)) :=
    digitPhase hζ (-(∑ d, p.1 d * p.2 d))
  have hw (p) : w p ≠ 0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne ℓ))
  have hs (a b) : M a b = M b a :=
    Finset.prod_congr rfl fun d _ => by rw [Nat.mul_comm (a d).val]
  have hmat : (Matrix.of fun o i => primeTupleKernel hζ i.1 i.2 o.1 o.2) =
      Matrix.of (fun o i => ((ℓ : K)⁻¹ ^ k * w o) * (w i * R o i)) := by
    ext o i
    rw [Matrix.of_apply, primeTupleKernel_eq_primeTransform, Matrix.of_apply]
    change _ * w i * w o * M (pack i) (swapPack o) =
      (_ * w o) * (w i * M (swapPack o) (pack i))
    rw [hs (pack i) (swapPack o)]
    ring
  rw [hmat, complexity_diagonal]
  · exact complexity_reindex _ _ _
  · exact fun o => mul_ne_zero (pow_ne_zero _ (inv_ne_zero hζ.neZero'.out)) (hw o)
  · exact hw

end FiniteFourier
end LinearAlgebra
end OAI
