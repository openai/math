import Mathlib

/-! # Square and rectangular matrix multiplication exponents over every field -/

namespace OAI

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

inductive Gate (F Input Register : Type*) where
  | constant : F → Gate F Input Register
  | input : Input → Gate F Input Register
  | add : Register → Register → Gate F Input Register
  | sub : Register → Register → Gate F Input Register
  | mul : Register → Register → Gate F Input Register

namespace Gate

variable {F Input Register : Type*}

def cost : Gate F Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

end Gate

inductive Program (F Input : Type*) : ℕ → Type _ where
  | nil : Program F Input 0
  | step {r : ℕ} : Program F Input r → Gate F Input (Fin r) → Program F Input (r + 1)

namespace Program

variable {F Input : Type*}

def cost : {r : ℕ} → Program F Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

end Program

abbrev MatrixInput (a b c : ℕ) := (Fin a × Fin b) ⊕ (Fin b × Fin c)

structure MatrixAlgorithm (F : Type*) (a b c : ℕ) where
  registers : ℕ
  program : Program F (MatrixInput a b c) registers
  output : Fin a → Fin c → Fin registers

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

def cost (P : MatrixAlgorithm F a b c) : ℕ := P.program.cost

end MatrixAlgorithm

end MatrixMultiplication.Arithmetic

end

namespace LinearAlgebra.SpectralBooks

open OAI.MatrixMultiplication.Arithmetic MvPolynomial
open scoped BigOperators
noncomputable section

section

variable {F I R : Type*} [CommRing F]

/-- The polynomial produced at one gate from the polynomials in its registers. -/
def gatePolynomial (g : Gate F I R) (v : R → MvPolynomial I F) : MvPolynomial I F :=
  g.casesOn (fun c => C c) (fun i => X i)
    (fun i j => v i + v j) (fun i j => v i - v j) (fun i j => v i * v j)

/-- Formal polynomial in each register of a straight-line program. -/
def registerPolynomial : {r : ℕ} → Program F I r → Fin r → MvPolynomial I F
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (gatePolynomial g (registerPolynomial p)) (registerPolynomial p)

/-- Formal correctness in the paper, including over a finite ground field. -/
def FormalCorrect {a b c : ℕ} (P : MatrixAlgorithm F a b c) : Prop :=
  ∀ i k, registerPolynomial P.program (P.output i k) =
    ∑ j : Fin b, X (Sum.inl (i, j)) * X (Sum.inr (j, k))

end

/-- The integer wire dimension at scale `N` and weight `w`. -/
def wireDimension (N : ℕ) (w : ℝ) : ℕ := ⌈(N : ℝ) ^ w⌉₊

/-- Admissible exponents for the rounded rectangular formats, with positive slack. -/
def FormalAdmissibleExponent (F : Type*) [Field F] (w12 w23 w31 τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    ∃ P : MatrixAlgorithm F (wireDimension N w31) (wireDimension N w12) (wireDimension N w23),
      FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (N : ℝ) ^ (τ + ε)

/-- The arithmetic exponent in base size `N` at three prescribed wire weights. -/
def formalOmega (F : Type*) [Field F] (w12 w23 w31 : ℝ) : ℝ :=
  sInf {τ : ℝ | FormalAdmissibleExponent F w12 w23 w31 τ}

/-- The square matrix multiplication exponent over every field. -/
theorem square_exponent (F : Type*) [Field F] : formalOmega F 1 1 1 = (9 : ℝ) / 4 := by
  sorry

/-- The supremum of the weights in `[0, 1]` at which the cost exponent is two. -/
def dualExponent (ω : ℝ → ℝ) : ℝ :=
  sSup {t : ℝ | t ∈ Set.Icc 0 1 ∧ ω t = 2}

/-- The dual exponent for formal arithmetic matrix multiplication at weights `(1,1,t)`. -/
def formalAlpha (F : Type*) [Field F] : ℝ := dualExponent (formalOmega F 1 1)

/-- The dual matrix multiplication exponent over every field. -/
theorem dual_exponent (F : Type*) [Field F] : formalAlpha F = (1 : ℝ) / 2 := by
  sorry

/-- The exact rectangular exponent with the nonnegative parts of the weights sorted
in descending order. On coordinate planes the correction term is zero. -/
theorem rectangular_exponent (F : Type*) [Field F] (a b c : ℝ) :
    formalOmega F a b c =
      let A := max a 0
      let B := max b 0
      let C := max c 0
      let x := max A (max B C)
      let z := min A (min B C)
      let y := A + B + C - x - z
      x + y + (max ((x + y) * z - x * y) 0) ^ 2 / (4 * x * y * z) := by
  sorry

end
end LinearAlgebra.SpectralBooks
end OAI
