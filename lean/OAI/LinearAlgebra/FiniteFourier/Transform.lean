import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Character transforms over splitting fields

The character table has characters as rows and group elements as columns.
The inverse uses the negative group element and divides by the group order.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

/-- The size of each cyclic factor divides the group exponent. -/
theorem cyclicFactor_dvd_exponent {A ι : Type*} [CommGroup A] {n : ι → ℕ}
    (e : A ≃* ((i : ι) → Multiplicative (ZMod (n i)))) (i : ι) :
    n i ∣ Monoid.exponent A := by
  classical
  have he : n i = orderOf (e.symm (Pi.mulSingle i (.ofAdd 1))) := by
    simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
      using (ZMod.addOrderOf_one (n i)).symm
  exact he ▸ Monoid.order_dvd_exponent _

/-- A multiplicative character of a group written additively. -/
abbrev Character (G K : Type*) [AddCommGroup G] [Field K] := Multiplicative G →* Kˣ

variable (G K : Type*) [AddCommGroup G] [Field K]

/-- Fourier matrix in the positive-character convention. -/
def fourierMatrix : Matrix (Character G K) G K :=
  Matrix.of fun χ g => (χ (Multiplicative.ofAdd g) : K)

variable [Fintype G]

/-- The order is invertible and the field contains a primitive root of the group exponent. -/
def Admissible : Prop :=
  (Fintype.card G : K) ≠ 0 ∧ ∃ ζ : K, IsPrimitiveRoot ζ (AddMonoid.exponent G)

noncomputable instance characterFintype : Fintype (Character G K) := Fintype.ofFinite _

/-- The inverse Fourier matrix has negative-character entries scaled by `1/|G|`. -/
def inverseFourierMatrix : Matrix G (Character G K) K :=
  Matrix.of fun g χ => (Fintype.card G : K)⁻¹ * (χ (Multiplicative.ofAdd (-g)) : K)

/-- Under the splitting hypothesis the character group has the same order as the group. -/
theorem card_character (h : Admissible G K) : Fintype.card (Character G K) = Fintype.card G := by
  let : HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative G)) :=
    ⟨h.2, rootsOfUnity.isCyclic _ _⟩
  simpa [Nat.card_eq_fintype_card] using
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative G) K

variable {G K}

theorem character_orthogonality (χ ψ : Character G K) [Decidable (χ = ψ)] :
    ∑ g : G, (χ (Multiplicative.ofAdd g) : K) * (ψ (Multiplicative.ofAdd (-g)) : K) =
      if χ = ψ then (Fintype.card G : K) else 0 := by
  classical
  let f : Multiplicative G →* K := (Units.coeHom K).comp (χ / ψ)
  have hsum := sum_hom_units f
  have heval (g : G) : f (Multiplicative.ofAdd g) =
      (χ (Multiplicative.ofAdd g) : K) * (ψ (Multiplicative.ofAdd (-g)) : K) := by
    change (↑(χ (Multiplicative.ofAdd g) / ψ (Multiplicative.ofAdd g)) : K) =
      _ * ↑(ψ (Multiplicative.ofAdd g)⁻¹)
    simp [div_eq_mul_inv]
  have hequiv : f = 1 ↔ χ = ψ := by
    constructor
    · intro hf
      apply DFunLike.ext
      intro g
      apply Units.ext
      have hval := DFunLike.congr_fun hf g
      change (↑(χ g / ψ g) : K) = 1 at hval
      exact (div_eq_one_iff_eq (Units.ne_zero (ψ g))).mp (by simpa using hval)
    · rintro rfl
      ext g
      simp [f]
  convert hsum using 1
  · rw [← Multiplicative.ofAdd.sum_comp f]
    exact Finset.sum_congr rfl (fun g _ => (heval g).symm)
  · by_cases h : χ = ψ <;> simp [h, hequiv]

variable (G K)

theorem fourier_mul_inverse_of_card_ne_zero [DecidableEq (Character G K)]
    (hN : (Fintype.card G : K) ≠ 0) :
    fourierMatrix G K * inverseFourierMatrix G K = 1 := by
  ext χ ψ
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [fourierMatrix, inverseFourierMatrix, Matrix.of_apply,
    mul_left_comm (↑(χ _) : K), ← Finset.mul_sum, character_orthogonality]
  split <;> simp_all

theorem fourier_mul_inverse [DecidableEq (Character G K)] (h : Admissible G K) :
    fourierMatrix G K * inverseFourierMatrix G K = 1 :=
  fourier_mul_inverse_of_card_ne_zero G K h.1

theorem inverse_mul_fourier [DecidableEq G] (h : Admissible G K) :
    inverseFourierMatrix G K * fourierMatrix G K = 1 := by
  classical
  exact (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (card_character G K h))).mp
    (fourier_mul_inverse G K h)

/-- Applying the character transform to the coefficient vector of a group function. -/
def transform (x : G → K) : Character G K → K := (fourierMatrix G K).mulVec x

/-- Applying the normalized negative-character transform. -/
def inverseTransform (y : Character G K → K) : G → K := (inverseFourierMatrix G K).mulVec y

theorem transform_apply (x : G → K) (χ : Character G K) :
    transform G K x χ = ∑ g, (χ (Multiplicative.ofAdd g) : K) * x g := rfl

theorem inverseTransform_apply (y : Character G K → K) (g : G) :
    inverseTransform G K y g =
      (Fintype.card G : K)⁻¹ * ∑ χ, (χ (Multiplicative.ofAdd (-g)) : K) * y χ := by
  simp [inverseTransform, inverseFourierMatrix, Matrix.mulVec, dotProduct, mul_assoc, Finset.mul_sum]

theorem inverseTransform_transform (h : Admissible G K) (x : G → K) :
    inverseTransform G K (transform G K x) = x := by
  classical
  rw [inverseTransform, transform, Matrix.mulVec_mulVec, inverse_mul_fourier _ _ h, Matrix.one_mulVec]

theorem transform_inverseTransform (h : Admissible G K) (y : Character G K → K) :
    transform G K (inverseTransform G K y) = y := by
  classical
  rw [transform, inverseTransform, Matrix.mulVec_mulVec, fourier_mul_inverse _ _ h, Matrix.one_mulVec]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
