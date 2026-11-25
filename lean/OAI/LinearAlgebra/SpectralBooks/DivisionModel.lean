import OAI.LinearAlgebra.SpectralBooks.FormalCircuit
import Mathlib.RingTheory.Localization.FractionRing

/-! # Straight-line programs with division

A program computes rational functions in independent matrix entries. A division gate is
valid exactly when its divisor is a nonzero rational function. Thus formal correctness
is meaningful over both finite and infinite fields.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial
open scoped BigOperators

/-- Straight-line programs over the field of rational functions in the inputs. -/
inductive RationalProgram (F I : Type*) : ℕ → Type _ where
  | nil : RationalProgram F I 0
  | step {r : ℕ} (p : RationalProgram F I r) (g : Gate F I (Fin r)) :
      RationalProgram F I (r + 1)
  | quot {r : ℕ} (p : RationalProgram F I r) (i j : Fin r) : RationalProgram F I (r + 1)

namespace RationalProgram

variable {F I R : Type*} {r : ℕ}

/-- Total number of scalar arithmetic operations. -/
def cost : {r : ℕ} → RationalProgram F I r → ℕ
  | _, .nil => 0
  | _, .step p g => p.cost + g.cost
  | _, .quot p _ _ => p.cost + 1

/-- Number of multiplications and divisions. -/
def productQuotientCount : {r : ℕ} → RationalProgram F I r → ℕ
  | _, .nil => 0
  | _, .step p (.mul _ _) => p.productQuotientCount + 1
  | _, .step p _ => p.productQuotientCount
  | _, .quot p _ _ => p.productQuotientCount + 1

theorem productQuotientCount_le_cost (p : RationalProgram F I r) :
    p.productQuotientCount ≤ p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => cases g <;> simp [productQuotientCount, cost, Gate.cost] <;> omega
  | quot p i j ih => exact Nat.succ_le_succ ih

/-- Regard a division-free program as a rational program with the same registers. -/
def ofDivisionFree : {r : ℕ} → Program F I r → RationalProgram F I r
  | _, .nil => .nil
  | _, .step p g => .step (ofDivisionFree p) g

@[simp] theorem cost_ofDivisionFree (p : Program F I r) : (ofDivisionFree p).cost = p.cost := by
  induction p <;> simp_all [ofDivisionFree, cost, Program.cost]

noncomputable section

variable [Field F]

/-- Interpret the ordinary gates in the rational function field. -/
def gateValue (g : Gate F I R) (v : R → FractionRing (MvPolynomial I F)) :
    FractionRing (MvPolynomial I F) :=
  g.casesOn (fun c => algebraMap _ _ (C c : MvPolynomial I F)) (fun i => algebraMap _ _ (X i : MvPolynomial I F))
    (fun i j => v i + v j) (fun i j => v i - v j) (fun i j => v i * v j)

/-- The rational function recorded at a register. Register zero holds the latest gate. -/
def value : {r : ℕ} → RationalProgram F I r → Fin r → FractionRing (MvPolynomial I F)
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (gateValue g p.value) p.value
  | _, .quot p i j => Fin.cases (p.value i / p.value j) p.value

/-- Every denominator occurring during the computation is generically nonzero. -/
def Valid : {r : ℕ} → RationalProgram F I r → Prop
  | _, .nil => True
  | _, .step p _ => p.Valid
  | _, .quot p _ j => p.Valid ∧ p.value j ≠ 0

@[simp] theorem valid_ofDivisionFree (p : Program F I r) : (ofDivisionFree p).Valid := by
  induction p <;> simp_all [ofDivisionFree, Valid]

@[simp] theorem value_ofDivisionFree (p : Program F I r) (i : Fin r) :
    (ofDivisionFree p).value i = algebraMap _ _ (registerPolynomial p i) := by
  induction p with
  | nil => exact i.elim0
  | step p g ih =>
    refine Fin.cases ?_ ih i
    cases g <;> simp [ofDivisionFree, value, gateValue, gatePolynomial, ih]

end
end RationalProgram

/-- A rectangular matrix multiplication algorithm with division gates. -/
structure RationalMatrixAlgorithm (F : Type*) (a b c : ℕ) where
  registers : ℕ
  program : RationalProgram F (MatrixInput a b c) registers
  output : Fin a → Fin c → Fin registers

namespace RationalMatrixAlgorithm

variable {F : Type*} {a b c : ℕ}

def cost (P : RationalMatrixAlgorithm F a b c) : ℕ := P.program.cost

/-- Embed a division-free matrix multiplication algorithm in the division model. -/
def ofDivisionFree (P : MatrixAlgorithm F a b c) : RationalMatrixAlgorithm F a b c :=
  ⟨P.registers, RationalProgram.ofDivisionFree P.program, P.output⟩

@[simp] theorem cost_ofDivisionFree (P : MatrixAlgorithm F a b c) :
    (ofDivisionFree P).cost = P.cost := RationalProgram.cost_ofDivisionFree P.program

variable [Field F]

/-- Validity of the divisions and the formal identities for all output coordinates. -/
def Correct (P : RationalMatrixAlgorithm F a b c) : Prop :=
  P.program.Valid ∧ ∀ i k, P.program.value (P.output i k) = algebraMap _ _
    (∑ j : Fin b, X (Sum.inl (i, j)) * X (Sum.inr (j, k)) : MvPolynomial (MatrixInput a b c) F)

theorem correct_ofDivisionFree {P : MatrixAlgorithm F a b c} (h : FormalCorrect P) :
    (ofDivisionFree P).Correct :=
  ⟨RationalProgram.valid_ofDivisionFree _, fun i k =>
    (RationalProgram.value_ofDivisionFree _ _).trans (congrArg _ (h i k))⟩

/-- Entrywise matrix multiplication supplies a correct division-model algorithm at cubic cost. -/
theorem exists_correct_cost_eq_naive (F : Type*) [Field F] (a b c : ℕ) :
    ∃ P : RationalMatrixAlgorithm F a b c, P.Correct ∧ P.cost = 2 * a * b * c :=
  ⟨_, correct_ofDivisionFree (formalCorrect_naiveAlgorithm F a b c), by simp⟩

end RationalMatrixAlgorithm

end SpectralBooks
end LinearAlgebra
end OAI
