import OAI.LinearAlgebra.SpectralBooks.Circuit
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # Formal partial derivatives at the generic input

The dual-number substitution sending a polynomial to its value and one formal
partial derivative extends to the rational function field. Every nonzero
polynomial has invertible constant component there. This lets us extract the two
cross products of a quotient gate simultaneously for all input coordinates.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open MvPolynomial
open scoped nonZeroDivisors BigOperators

variable {F I A B : Type*} [Field F]

private abbrev K (F I : Type*) [Field F] := FractionRing (MvPolynomial I F)

private def polynomialPerturb (i : I) :
    MvPolynomial I F →+* TrivSqZeroExt (K F I) (K F I) where
  toFun p := (algebraMap _ _ p, algebraMap _ _ (pderiv i p))
  map_zero' := TrivSqZeroExt.ext (map_zero _) (by simp)
  map_one' := TrivSqZeroExt.ext (map_one _) (by simp)
  map_add' p q := by
    apply Prod.ext (map_add _ _ _)
    change algebraMap _ _ (pderiv i (p + q)) = algebraMap _ _ (pderiv i p) + algebraMap _ _ (pderiv i q)
    simp
  map_mul' p q := by
    apply Prod.ext (map_mul _ _ _)
    change algebraMap _ _ (pderiv i (p * q)) =
      algebraMap _ _ p * algebraMap _ _ (pderiv i q) +
        algebraMap _ _ (pderiv i p) * algebraMap _ _ q
    simp only [pderiv_mul, map_add, map_mul]
    ring

private theorem polynomialPerturb_isUnit (i : I) (p : (MvPolynomial I F)⁰) :
    IsUnit (polynomialPerturb i p : TrivSqZeroExt (K F I) (K F I)) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  change IsUnit (algebraMap _ (K F I) (p : MvPolynomial I F))
  exact IsLocalization.map_units (K F I) p

private def rationalPerturb (i : I) : K F I →+* TrivSqZeroExt (K F I) (K F I) :=
  IsLocalization.lift (polynomialPerturb_isUnit i)

private theorem rationalPerturb_polynomial (i : I) (p : MvPolynomial I F) :
    rationalPerturb i (algebraMap _ _ p) = polynomialPerturb i p :=
  IsLocalization.lift_eq _ _

private theorem rationalPerturb_fst (i : I) (p : K F I) : (rationalPerturb i p).fst = p := by
  let proj := (TrivSqZeroExt.fstHom (K F I) (K F I) (K F I)).toRingHom
  have h : proj.comp (rationalPerturb i) = RingHom.id (K F I) := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial I F)
    intro q
    change (rationalPerturb i (algebraMap _ _ q)).fst = _
    rw [rationalPerturb_polynomial]
    rfl
  exact DFunLike.congr_fun h p

/-- Formal partial differentiation on the rational function field in the input entries. -/
def ratPartial (i : I) (p : FractionRing (MvPolynomial I F)) : FractionRing (MvPolynomial I F) :=
  (rationalPerturb i p).snd

@[simp] theorem ratPartial_polynomial (i : I) (p : MvPolynomial I F) :
    ratPartial i (algebraMap _ (K F I) p) = algebraMap _ _ (pderiv i p) := by
  rw [ratPartial, rationalPerturb_polynomial]
  rfl

@[simp] theorem ratPartial_zero (i : I) : ratPartial i (0 : K F I) = 0 := by
  simp [ratPartial]

@[simp] theorem ratPartial_one (i : I) : ratPartial i (1 : K F I) = 0 := by
  simp [ratPartial]

@[simp] theorem ratPartial_add (i : I) (p q : K F I) :
    ratPartial i (p + q) = ratPartial i p + ratPartial i q := by simp [ratPartial]

@[simp] theorem ratPartial_sub (i : I) (p q : K F I) :
    ratPartial i (p - q) = ratPartial i p - ratPartial i q := by simp [ratPartial]

@[simp] theorem ratPartial_mul (i : I) (p q : K F I) :
    ratPartial i (p * q) = ratPartial i p * q + p * ratPartial i q := by
  simp only [ratPartial, map_mul, TrivSqZeroExt.snd_mul, rationalPerturb_fst]
  change p * _ + _ * q = _
  exact add_comm _ _

/-- The formal mixed derivative with respect to one left and one right entry. -/
def ratMixed (p : FractionRing (MvPolynomial (A ⊕ B) F)) (x : A) (y : B) :=
  ratPartial (.inr y) (ratPartial (.inl x) p)

@[simp] theorem ratMixed_C (c : F) (x : A) (y : B) :
    ratMixed (algebraMap (MvPolynomial (A ⊕ B) F) (K F (A ⊕ B)) (C c)) x y = 0 := by
  simp [ratMixed]

@[simp] theorem ratMixed_X (s : A ⊕ B) (x : A) (y : B) :
    ratMixed (algebraMap _ (K F (A ⊕ B)) (X s : MvPolynomial (A ⊕ B) F)) x y = 0 := by
  by_cases h : s = Sum.inl x
  · subst s
    simp [ratMixed]
  · rw [ratMixed, ratPartial_polynomial, ratPartial_polynomial, pderiv_X_of_ne h]
    simp

@[simp] theorem ratMixed_add (p q : K F (A ⊕ B)) (x : A) (y : B) :
    ratMixed (p + q) x y = ratMixed p x y + ratMixed q x y := by simp [ratMixed]

@[simp] theorem ratMixed_sub (p q : K F (A ⊕ B)) (x : A) (y : B) :
    ratMixed (p - q) x y = ratMixed p x y - ratMixed q x y := by simp [ratMixed]

theorem ratMixed_mul (p q : K F (A ⊕ B)) (x : A) (y : B) :
    ratMixed (p * q) x y = q * ratMixed p x y + p * ratMixed q x y +
      ratPartial (.inl x) p * ratPartial (.inr y) q +
      ratPartial (.inl x) q * ratPartial (.inr y) p := by
  simp only [ratMixed, ratPartial_mul, ratPartial_add]
  ring

theorem ratMixed_matrixEntry {a b c : ℕ} (i : Fin a) (k : Fin c)
    (x : Fin a × Fin b) (y : Fin b × Fin c) :
    ratMixed (∑ j : Fin b, algebraMap _ _ (X (.inl (i,j)) : MvPolynomial (Arithmetic.MatrixInput a b c) F) *
      algebraMap _ _ (X (.inr (j,k)) : MvPolynomial (Arithmetic.MatrixInput a b c) F)) x y =
        matrixTensor (K F (Arithmetic.MatrixInput a b c)) b c a x y (k,i) := by
  classical
  simp_rw [← map_mul]
  rw [← map_sum, ratMixed, ratPartial_polynomial, ratPartial_polynomial]
  rcases x with ⟨u, v⟩
  rcases y with ⟨w, z⟩
  simp [pderiv_X, Pi.single_apply, apply_ite, Foundation.Tensor.matrixCoefficients, Prod.ext_iff,
    ite_and, eq_comm]
  split_ifs <;> simp_all

end

end

end SpectralBooks
end LinearAlgebra
end OAI
