import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.TensorSpectrum.SeparationWeights
import OAI.LinearAlgebra.MatrixExponent.Fourier
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

open OAI.LinearAlgebra.MatrixExponent OAI.LinearAlgebra.TensorSpectrum.Separation

/-!
# Charged finite separation by local Fourier maps

The source is exactly `5 * M` full copies of the shared-first-leg tensor.
The target is the full direct sum of the sector tensors, each multiplied by
a length-`M` pairing on the second and third legs.  Local variables may have
negative weights; after Fourier projection every surviving total weight is
a nonnegative square, so the resulting coefficient array is polynomial.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.Separation

variable {X Y Z : Type*}

/-- The branch labels occur only on the last two legs of the input. -/
def shared {M : ℕ} (A : Fin M → Tensor Coeff X Y Z) :
    Tensor Coeff X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then A y.1 x y.2 z.2 else 0

/-- The auxiliary pairing has one coordinate on the first leg. -/
def dotPairingX (U : Type*) [DecidableEq U] : Tensor Coeff Unit U U :=
  fun _ u v => if u = v then 1 else 0

/-- Every branch in this output has its own first-leg space. -/
def separated {M : ℕ} (A : Fin M → Tensor Coeff X Y Z) :
    Tensor Coeff (Fin M × (X × Unit)) (Fin M × (Y × Fin M))
      (Fin M × (Z × Fin M)) :=
  Tensor.directSum (fun h => Tensor.product (A h) (dotPairingX (Fin M)))

/-- The integer projected by the finite Fourier average. Labels are numbered
from zero here; translating all four labels by one leaves this phase unchanged. -/
def phase {M : ℕ} (h g u v : Fin M) : ℤ :=
  (u : ℤ) - (v : ℤ) + 2 * ((g : ℤ) - (h : ℤ))

/-- Copy a specified source coordinate with a scalar depending only on the
target coordinate and the source's direct-sum copy number. -/
def copyLocal {L : ℕ} {S T : Type*} [DecidableEq S]
    (f : T → S) (a : T → Fin L → Coeff) : T → (Fin L × S) → Coeff :=
  fun t s => if s.2 = f t then a t s.1 else 0

section CopyCalculation

variable {L : ℕ} {X' Y' Z' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- Summing the full source copies, rather than target coordinate labels, is
what produces the Fourier average. All three source copy indices must agree. -/
theorem restrict_copies (T : Tensor Coeff X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (a : X' → Fin L → Coeff) (b : Y' → Fin L → Coeff) (c : Z' → Fin L → Coeff) :
    Tensor.restrict (copyLocal fx a) (copyLocal fy b) (copyLocal fz c)
      (Tensor.directSum (fun _ : Fin L => T)) =
      fun x y z => (∑ r, a x r * b y r * c z r) * T (fx x) (fy y) (fz z) := by
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, copyLocal, Fintype.sum_prod_type,
    ite_and, ite_mul, mul_ite, ← Finset.sum_mul]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
/-- Scaling each target coordinate is itself a local linear operation. -/
theorem restrict_scaled (T : Tensor Coeff X Y Z)
    (a : X' → X → Coeff) (b : Y' → Y → Coeff) (c : Z' → Z → Coeff)
    (u : X' → Coeff) (v : Y' → Coeff) (w : Z' → Coeff) :
    Tensor.restrict (fun x i => u x * a x i)
      (fun y j => v y * b y j) (fun z k => w z * c z k) T =
      fun x y z => u x * v y * w z * Tensor.restrict a b c T x y z := by
  funext x y z
  simp only [Tensor.restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

end CopyCalculation

section Projection

variable {M : ℕ}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def fourierX (ζ : Coeff) :
    (Fin M × (X × Unit)) → (Fin (5 * M) × X) → Coeff :=
  copyLocal (fun x => x.2.1)
    (fun x r => ζ ^ ((r : ℤ) * (2 * (x.1 : ℤ))))

def fourierY (ζ : Coeff) :
    (Fin M × (Y × Fin M)) → (Fin (5 * M) × (Fin M × Y)) → Coeff :=
  copyLocal (fun y => (y.1, y.2.1))
    (fun y r => ζ ^ ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ))))

def fourierZ (ζ : Coeff) (w : Fin (5 * M) → Coeff) :
    (Fin M × (Z × Fin M)) → (Fin (5 * M) × (Fin M × Z)) → Coeff :=
  copyLocal (fun z => (z.1, z.2.1))
    (fun z r => w r *
      ζ ^ ((r : ℤ) * (-(z.2.2 : ℤ) - (z.1 : ℤ))))

def projected (A : Fin M → Tensor Coeff X Y Z) :
    Tensor Coeff (Fin M × (X × Unit)) (Fin M × (Y × Fin M))
      (Fin M × (Z × Fin M)) :=
  fun x y z => if y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
    then A y.1 x.2.1 y.2.1 z.2.1 else 0

/-- The actual independent local maps give exactly the projected tensor. -/
theorem fourier_restrict (A : Fin M → Tensor Coeff X Y Z)
    (ζ : Coeff) (w : Fin (5 * M) → Coeff) (hζ : ζ ≠ 0)
    (haverage : ∀ e : ℤ, -(3 * (M : ℤ)) < e → e < 3 * (M : ℤ) →
      (∑ r : Fin (5 * M), w r * ζ ^ ((r : ℤ) * e)) = if e = 0 then 1 else 0) :
    Tensor.restrict (fourierX ζ) (fourierY ζ) (fourierZ ζ w)
      (Tensor.directSum (fun _ : Fin (5 * M) => shared A)) = projected A := by
  classical
  rw [fourierX, fourierY, fourierZ, restrict_copies]
  funext x y z
  by_cases hyz : y.1 = z.1
  · have hphase : (∑ r : Fin (5 * M),
        ζ ^ ((r : ℤ) * (2 * (x.1 : ℤ))) *
          ζ ^ ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ))) *
          (w r *
            ζ ^ ((r : ℤ) * (-(z.2.2 : ℤ) - (z.1 : ℤ))))) =
        if phase y.1 x.1 y.2.2 z.2.2 = 0 then 1 else 0 := by
      calc
        _ = ∑ r : Fin (5 * M), w r * ζ ^ ((r : ℤ) * phase y.1 x.1 y.2.2 z.2.2) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [← hyz]
          calc
            _ = w r *
                ((ζ ^ ((r : ℤ) * (2 * (x.1 : ℤ))) *
                  ζ ^ ((r : ℤ) * ((y.2.2 : ℤ) - (y.1 : ℤ)))) *
                  ζ ^ ((r : ℤ) * (-(z.2.2 : ℤ) - (y.1 : ℤ)))) := by ring
            _ = _ := by
              rw [← zpow_add₀ hζ, ← zpow_add₀ hζ]
              congr 2
              dsimp [phase]
              ring
        _ = _ := by
          apply haverage <;> unfold phase <;> omega
    rw [hphase]
    simp [shared, projected, hyz, ite_mul]
  · simp [shared, projected, hyz]

end Projection

section Polynomial

variable {M : ℕ}

/-- The degree of a projected monomial, already known to be nonnegative. -/
def squareDegree (h g : Fin M) : ℕ :=
  squareExponent g h

/-- This is a polynomial array even though the individual local weights used
to realize its nonzero evaluations can be negative. -/
def separationPolynomial (A : Fin M → Tensor Coeff X Y Z) :
    Tensor (Polynomial Coeff) (Fin M × (X × Unit)) (Fin M × (Y × Fin M))
      (Fin M × (Z × Fin M)) :=
  fun x y z => if y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
    then Polynomial.monomial (squareDegree y.1 x.1) (A y.1 x.2.1 y.2.1 z.2.1)
    else 0

theorem squareDegree_eq_zero_iff (h g : Fin M) : squareDegree h g = 0 ↔ g = h := by
  exact squareExponent_eq_zero_iff g h

/-- The zero coefficient is the full direct sum with an auxiliary dot product. -/
theorem separationPolynomial_constant (A : Fin M → Tensor Coeff X Y Z) :
    (fun x y z => (separationPolynomial A x y z).coeff 0) = separated A := by
  funext x y z
  by_cases hxy : x.1 = y.1
  · by_cases hyz : y.1 = z.1
    · by_cases huv : y.2.2 = z.2.2
      · simp [separationPolynomial, separated, Tensor.directSum, Tensor.product,
          dotPairingX, phase, squareDegree, squareExponent, hxy, hyz, huv]
      · have hp : phase y.1 x.1 y.2.2 z.2.2 ≠ 0 := by
          intro hp
          have heq : (y.2.2 : ℤ) = (z.2.2 : ℤ) := by
            simpa [phase, hxy, sub_eq_zero] using hp
          exact huv (Fin.ext (by exact_mod_cast heq))
        have hsupport : ¬(y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0) :=
          fun h => hp h.2
        simp only [separationPolynomial, ite_eq_right hsupport]
        simp [separated, Tensor.directSum, Tensor.product, dotPairingX, hxy, hyz, huv]
    · have hxz : x.1 ≠ z.1 := by simpa [hxy] using hyz
      simp [separationPolynomial, separated, Tensor.directSum, hyz, hxz]
  · have hdegree : squareDegree y.1 x.1 ≠ 0 := by
      exact fun h => hxy ((squareDegree_eq_zero_iff y.1 x.1).mp h)
    by_cases hs : y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
    · simp only [separationPolynomial, ite_eq_left hs]
      simp [separated, Tensor.directSum, hxy,
        Polynomial.coeff_monomial, hdegree]
    · simp [separationPolynomial, hs, separated, Tensor.directSum, hxy]

theorem separationPolynomial_degree (A : Fin M → Tensor Coeff X Y Z)
    (x : Fin M × (X × Unit)) (y : Fin M × (Y × Fin M))
    (z : Fin M × (Z × Fin M)) :
    (separationPolynomial A x y z).degree ≤ ((M - 1) ^ 2 : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold separationPolynomial
  split_ifs
  · exact le_trans (Polynomial.natDegree_monomial_le _)
      (squareExponent_le x.1 y.1)
  · simp

def weightX (x : Fin M × (X × Unit)) : ℤ := (x.1 : ℤ) ^ 2

def weightY (y : Fin M × (Y × Fin M)) : ℤ :=
  (y.1 : ℤ) * (y.2.2 : ℤ) - (y.1 : ℤ) ^ 2

def weightZ (z : Fin M × (Z × Fin M)) : ℤ :=
  -(z.1 : ℤ) * (z.2.2 : ℤ)

/-- On the complete projected support, the local weights add to the actual
polynomial degree, including all zero and mismatched coefficients. -/
theorem separationPolynomial_eval (A : Fin M → Tensor Coeff X Y Z)
    (t : Coeff) (ht : t ≠ 0) :
    (fun x y z => (separationPolynomial A x y z).eval t) =
      fun x y z => t ^ weightX x * t ^ weightY y * t ^ weightZ z * projected A x y z := by
  funext x y z
  by_cases hs : y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
  · have hsum : weightX x + weightY y + weightZ z =
        ((x.1 : ℤ) - (y.1 : ℤ)) ^ 2 := by
      dsimp [weightX, weightY, weightZ]
      rw [← hs.1]
      have hp := hs.2
      dsimp [phase] at hp
      nlinarith
    have hcast : (squareDegree y.1 x.1 : ℤ) = ((x.1 : ℤ) - (y.1 : ℤ)) ^ 2 :=
      Int.toNat_of_nonneg (sq_nonneg _)
    simp only [separationPolynomial, projected, ite_eq_left hs, Polynomial.eval_monomial]
    rw [← zpow_add₀ ht, ← zpow_add₀ ht, hsum, ← hcast, zpow_natCast]
    ring
  · simp [separationPolynomial, projected, hs]

end Polynomial

section Realization

variable {M : ℕ}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Every nonzero specialization comes from exactly the charged number of
source copies by three actual local linear maps. -/
theorem separationPolynomial_specializes (hM : 0 < M)
    (A : Fin M → Tensor Coeff X Y Z) (t : Coeff) (ht : t ≠ 0) :
    (fun x y z => (separationPolynomial A x y z).eval t) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : Fin (5 * M) => shared A)) := by
  classical
  obtain ⟨ζ, w, hζ, haverage⟩ := Fourier.exists_weights hM
  refine ⟨(fun x i => t ^ weightX x * fourierX ζ x i),
    (fun y j => t ^ weightY y * fourierY ζ y j),
    (fun z k => t ^ weightZ z * fourierZ ζ w z k), ?_⟩
  rw [restrict_scaled, fourier_restrict A ζ w hζ haverage]
  exact separationPolynomial_eval A t ht

/-- The complete finite construction, without a rank or character premise.
The nonzero-evaluation witnesses are restrictions of the full source direct
sum; the constant tensor is itself a full direct sum of products. -/
theorem finite_charged_separation (hM : 0 < M)
    (A : Fin M → Tensor Coeff X Y Z) :
    ∃ P : Tensor (Polynomial Coeff) (Fin M × (X × Unit))
        (Fin M × (Y × Fin M)) (Fin M × (Z × Fin M)),
      (∀ x y z, (P x y z).coeff 0 = separated A x y z) ∧
      (∀ x y z, (P x y z).degree ≤ ((M - 1) ^ 2 : ℕ)) ∧
      (∀ t : Coeff, t ≠ 0 → (fun x y z => (P x y z).eval t) ∈
        LocalTensor.orbit (Tensor.directSum (fun _ : Fin (5 * M) => shared A))) := by
  refine ⟨separationPolynomial A, ?_, separationPolynomial_degree A,
    separationPolynomial_specializes hM A⟩
  intro x y z
  exact congrFun (congrFun (congrFun (separationPolynomial_constant A) x) y) z

end Realization

end OAI.LinearAlgebra.MatrixExponent.Upper.Separation
