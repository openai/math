import OAI.LinearAlgebra.FiniteFourier.QuadraticPeriods

/-! # Exponent automorphisms on the nonscalar factor of a prime axis

For every commutative coefficient ring the unit residues act on
`R[X]/Φₚ` by exponent multiplication. Inversion exchanges the two
quadratic periods when the prime is three modulo four.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped BigOperators

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]

theorem primeAxisCharacter_one :
    primeAxisCharacter R p 1 = AdjoinRoot.root (cyclotomic p R) := by
  change AdjoinRoot.root (cyclotomic p R) ^ (1 : ZMod p).val = _
  rw [ZMod.val_one, pow_one]

private theorem primeAxisCharacter_pow (i : ZMod p) (k : ℕ) :
    primeAxisCharacter R p i ^ k = primeAxisCharacter R p (i*k) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]

private theorem equiv_val_fin (j : Fin p) : (ZMod.finEquiv p j).val = j.val := by
  cases p with
  | zero => exact j.elim0
  | succ _ => rfl

private theorem primeAxis_eval (u : (ZMod p)ˣ) :
    (cyclotomic p R).eval₂ (algebraMap R (AdjoinRoot (cyclotomic p R))) (primeAxisCharacter R p u) = 0 := by
  conv => lhs; arg 3; rw [cyclotomic_prime R p]
  rw [eval₂_finsetSum]
  simp only [eval₂_pow, eval₂_X, primeAxisCharacter_pow]
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ x : ZMod p, primeAxisCharacter R p (u.val*x) := by
      apply Fintype.sum_equiv (ZMod.finEquiv p).toEquiv
      intro j
      congr 2
      simpa [equiv_val_fin] using ZMod.natCast_zmod_val (ZMod.finEquiv p j)
    _ = ∑ x : ZMod p, primeAxisCharacter R p x :=
      Equiv.sum_comp (Equiv.mulLeft₀ (u : ZMod p) u.ne_zero) _
    _ = 0 := primeAxisCharacter_sum R p

private noncomputable def primeAxisHom (u : (ZMod p)ˣ) :
    AdjoinRoot (cyclotomic p R) →ₐ[R] AdjoinRoot (cyclotomic p R) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (primeAxisCharacter R p u) (primeAxis_eval R p u)

private theorem primeAxisHom_char (u : (ZMod p)ˣ) (i : ZMod p) :
    primeAxisHom R p u (primeAxisCharacter R p i) = primeAxisCharacter R p (u.val*i) := by
  change primeAxisHom R p u (AdjoinRoot.root _ ^ i.val) = _
  have hroot : primeAxisHom R p u (AdjoinRoot.root (cyclotomic p R)) = primeAxisCharacter R p u :=
    AdjoinRoot.liftAlgHom_root _ (Algebra.ofId R _) _ _
  rw [map_pow, hroot, primeAxisCharacter_pow, ZMod.natCast_zmod_val]

private theorem primeAxisHom_inverse (u : (ZMod p)ˣ) :
    (primeAxisHom R p u).comp (primeAxisHom R p u⁻¹) = AlgHom.id R _ := by
  apply AdjoinRoot.algHom_ext
  rw [← primeAxisCharacter_one, AlgHom.comp_apply, primeAxisHom_char, primeAxisHom_char,
    mul_one, Units.mul_inv, AlgHom.id_apply]

/-- The unit `u` acts on the class of `X` as `X ↦ X^u`. -/
noncomputable def primeAxisAction (u : (ZMod p)ˣ) :
    AdjoinRoot (cyclotomic p R) ≃ₐ[R] AdjoinRoot (cyclotomic p R) :=
  AlgEquiv.ofAlgHom (primeAxisHom R p u) (primeAxisHom R p u⁻¹) (primeAxisHom_inverse R p u)
    (by simpa using primeAxisHom_inverse R p u⁻¹)

@[simp] theorem primeAxisAction_character (u : (ZMod p)ˣ) (i : ZMod p) :
    primeAxisAction R p u (primeAxisCharacter R p i) = primeAxisCharacter R p (u.val*i) :=
  primeAxisHom_char R p u i

/-- The automorphisms respect the multiplication of exponents. -/
noncomputable def primeAxisActionHom :
    (ZMod p)ˣ →* (AdjoinRoot (cyclotomic p R) ≃ₐ[R] AdjoinRoot (cyclotomic p R)) where
  toFun := primeAxisAction R p
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply AdjoinRoot.algHom_ext
    rw [← primeAxisCharacter_one]
    change primeAxisAction R p 1 (primeAxisCharacter R p 1) = primeAxisCharacter R p 1
    simp
  map_mul' u v := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply AdjoinRoot.algHom_ext
    rw [← primeAxisCharacter_one]
    change primeAxisAction R p (u*v) _ = primeAxisAction R p u (primeAxisAction R p v _)
    simp

theorem primeAxisAction_pow (u : (ZMod p)ˣ) (k : ℕ) :
    primeAxisAction R p u ^ k = primeAxisAction R p (u^k) :=
  ((primeAxisActionHom R p).map_pow u k).symm

/-- Inversion of the universal root interchanges the square and nonsquare periods. -/
theorem primeAxisAction_neg_period (hp : p % 4 = 3) (ε : ℤ) :
    primeAxisAction R p (-1) (quadraticPeriod (primeAxisCharacter R p) ε) =
      quadraticPeriod (primeAxisCharacter R p) (-ε) := by
  have hneg : quadraticChar (ZMod p) (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr
    (by rw [FiniteField.isSquare_neg_one_iff]; simpa using hp)
  simp only [quadraticPeriod_eq_sum, map_sum, apply_ite, map_zero, primeAxisAction_character,
    Units.val_neg, Units.val_one, neg_one_mul]
  apply Fintype.sum_equiv (Equiv.neg (ZMod p))
  intro x
  have h : quadraticChar (ZMod p) (-x) = -quadraticChar (ZMod p) x := by
    rw [← neg_one_mul x, map_mul, hneg, neg_one_mul]
  simp [h]

end FiniteFourier
end LinearAlgebra
end OAI
