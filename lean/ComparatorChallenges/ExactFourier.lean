import Mathlib

namespace OAI

/-!
Scalar circuits for exact discrete Fourier transforms.
No bounds on predetermined complex coefficients, reuse, storage, or conditioning.
-/

namespace ExactFourier

/-- One charged scalar gate, referencing only available values. -/
inductive Gate (w : ℕ) where
  | add (i j : Fin w)
  | sub (i j : Fin w)
  | scale (c : ℂ) (i : Fin w)

def Gate.eval {w : ℕ} (v : Fin w → ℂ) : Gate w → ℂ
  | .add i j => v i + v j
  | .sub i j => v i - v j
  | .scale c i => c * v i

/-- A topologically ordered scalar DAG; available values are never consumed. -/
inductive Program (n : ℕ) : ℕ → Type where
  | nil : Program n 0
  | step {k : ℕ} (p : Program n k) (g : Gate (n + 1 + k)) : Program n (k + 1)

def Program.eval {n : ℕ} : {k : ℕ} → Program n k → (Fin n → ℂ) →
    (Fin (n + 1 + k) → ℂ)
  | 0, .nil, x => Fin.snoc x 0
  | _ + 1, .step p g, x =>
      let v := p.eval x
      Fin.snoc v (g.eval v)

/-- Outputs name available values, so permutations and arbitrary fanout are uncharged. -/
structure Circuit (n : ℕ) where
  size : ℕ
  program : Program n size
  outputs : Fin n → Fin (n + 1 + size)

def Circuit.eval {n : ℕ} (C : Circuit n) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => C.program.eval x (C.outputs i)

noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
noncomputable def fourierMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => zeta n ^ (j.val * k.val)

def Circuit.Computes {n : ℕ} (C : Circuit n) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x, C.eval x = A.mulVec x

/-- The precise quantified formulation of source theorem `thm:main`. -/
def MainStatement : Prop :=
  ∀ c : ℝ, 0 < c → ∀ N₀ : ℕ, 2 ≤ N₀ → ∃ n : ℕ, N₀ ≤ n ∧
    ∃ C : Circuit n, C.Computes (fourierMatrix n) ∧
      (C.size : ℝ) < c * (n : ℝ) * Real.logb 2 (n : ℝ)

theorem main_theorem : MainStatement := by
  sorry

end ExactFourier

namespace LinearAlgebra.FiniteFourier

/-- A binary linear gate over two previously available wires. -/
structure BinaryGate (K W : Type*) where
  left : W
  right : W
  leftCoeff : K
  rightCoeff : K

def BinaryGate.eval {K W : Type*} [Semiring K] (g : BinaryGate K W) (v : W → K) : K :=
  g.leftCoeff * v g.left + g.rightCoeff * v g.right

/-- Outputs may select and scale a wire, or output zero. -/
inductive Readout (K W : Type*) where
  | zero
  | scaled (coeff : K) (wire : W)

def Readout.eval {K W : Type*} [Semiring K] (z : Readout K W) (v : W → K) : K :=
  match z with
  | .zero => 0
  | .scaled c w => c * v w

/-- A straight-line program of precisely the displayed number of binary gates. -/
inductive Program (K I : Type*) : ℕ → Type _ where
  | nil : Program K I 0
  | step {r : ℕ} (p : Program K I r) (g : BinaryGate K (I ⊕ Fin r)) : Program K I (r + 1)

namespace Program

variable {K I : Type*} [Semiring K]

/-- Evaluation of the stored registers, with the newest value in register zero. -/
def value : {r : ℕ} → Program K I r → (I → K) → Fin r → K
  | _, .nil, _ => Fin.elim0
  | _, .step p g, x => Fin.cases (g.eval (Sum.elim x (p.value x))) (p.value x)

end Program

/-- A program together with its readouts. -/
structure Circuit (K I O : Type*) (s : ℕ) where
  program : Program K I s
  output : O → Readout K (I ⊕ Fin s)

namespace Circuit

variable {K I O : Type*} [Semiring K] {s : ℕ}

def eval (p : Circuit K I O s) (x : I → K) (o : O) : K :=
  (p.output o).eval (Sum.elim x (p.program.value x))

noncomputable def matrix (p : Circuit K I O s) : Matrix O I K := by
  classical
  exact fun o i => p.eval (Pi.single i 1) o

end Circuit

/-- Exact realization with at most the given number of gates. -/
def RealizableAtMost {K I O : Type*} [Semiring K] (M : Matrix O I K) (S : ℕ) : Prop :=
  ∃ s ≤ S, ∃ p : Circuit K I O s, p.matrix = M

section
variable {K I O : Type*} [Semiring K]

/-- Least number of binary linear gates needed to apply a matrix. -/
noncomputable def complexity [Fintype I] [Fintype O] (M : Matrix O I K) : ℕ :=
  sInf {n | RealizableAtMost M n}
end

section FeedbackModel

open Matrix
noncomputable section

/-- A binary linear system with feedback, with inputs indexed by `I`, outputs
indexed by `O` and `s` simultaneous state equations. -/
structure Feedback (K I O : Type*) (s : ℕ) where
  equation : Fin s → BinaryGate K (I ⊕ Fin s)
  output : O → Readout K (I ⊕ Fin s)

namespace Feedback

variable {K I O : Type*} [Field K] {s : ℕ}

/-- The coefficient row of a binary equation, adding the coefficients when
both incoming wires have the same source. -/
def gateRow {W : Type*} (g : BinaryGate K W) : W → K := by
  classical
  exact Pi.single g.left g.leftCoeff + Pi.single g.right g.rightCoeff

/-- Zero or one weighted source at an output. -/
def readRow {W : Type*} (g : Readout K W) : W → K := by
  classical
  exact g.casesOn 0 (fun c w => Pi.single w c)

variable (F : Feedback K I O s)

/-- The coefficient of state `j` in the equation for state `i`. -/
def stateMatrix : Matrix (Fin s) (Fin s) K := fun i j => gateRow (F.equation i) (.inr j)

/-- The coefficient of input `j` in the equation for state `i`. -/
def inputMatrix : Matrix (Fin s) I K := fun i j => gateRow (F.equation i) (.inl j)

/-- State-to-output readout. -/
def readState : Matrix O (Fin s) K := fun o j => readRow (F.output o) (.inr j)

/-- Direct input-to-output readout. -/
def readInput : Matrix O I K := fun o j => readRow (F.output o) (.inl j)

/-- Unique solvability in determinant form. -/
def Regular : Prop := (1 - F.stateMatrix).det ≠ 0

/-- The input-output matrix at delay one. Its circuit semantics is used on
regular systems. -/
def matrix : Matrix O I K :=
  F.readInput + F.readState * (1 - F.stateMatrix)⁻¹ * F.inputMatrix

/-- Realizability by this particular regular feedback system. -/
def Realizes (M : Matrix O I K) : Prop := F.Regular ∧ F.matrix = M

end Feedback
end
end FeedbackModel

section Border
variable {K L I O : Type*} [Field K] [Field L] {s : ℕ}

/-- Matrices of regular feedback systems with at most the prescribed number of states. -/
def FeedbackAtMost (M : Matrix O I K) (S : ℕ) : Prop :=
  ∃ s ≤ S, ∃ F : Feedback K I O s, F.Realizes M

/-- Membership of the scalar-extended matrix in the Zariski closure of regular
binary feedback systems with at most `S` states. -/
def GeometricBorderAtMost (M : Matrix O I K) (S : ℕ) : Prop :=
  ∀ p : MvPolynomial (O × I) (AlgebraicClosure K),
    (∀ A : Matrix O I (AlgebraicClosure K), FeedbackAtMost A S →
      MvPolynomial.eval (fun ij => A ij.1 ij.2) p = 0) →
    MvPolynomial.eval (fun ij => algebraMap K (AlgebraicClosure K) (M ij.1 ij.2)) p = 0

end Border

section Transform
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

attribute [local instance 10000] instIsDomain in
noncomputable instance characterFintype : Fintype (Character G K) := Fintype.ofFinite _

/-- The inverse Fourier matrix has negative-character entries scaled by `1/|G|`. -/
def inverseFourierMatrix : Matrix G (Character G K) K :=
  Matrix.of fun g χ => (Fintype.card G : K)⁻¹ * (χ (Multiplicative.ofAdd (-g)) : K)

end Transform

universe u v

/-- Theorem 1.1, including the geometric-border feedback systems in each
direction. Every order and every group and admissible field use the same
lower constant, and the upper constant depends only on the positive slack. -/
def FourierComplexityTheorem : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (G : Type u) (K : Type v) [AddCommGroup G] [Fintype G] [Field K],
      Admissible G K → 2 ≤ Fintype.card G →
      let N : ℝ := Fintype.card G
      let lower := c * N * Real.sqrt (Real.logb (2 : ℕ) N)
      let upper := C * N * (1 + Real.logb (2 : ℕ) N) ^ ((1 : ℝ) / (2 : ℕ) + ε)
      (lower ≤ complexity (fourierMatrix G K) ∧ (complexity (fourierMatrix G K) : ℝ) ≤ upper) ∧
      (lower ≤ complexity (inverseFourierMatrix G K) ∧
        (complexity (inverseFourierMatrix G K) : ℝ) ≤ upper) ∧
      ∀ S : ℕ, (GeometricBorderAtMost (fourierMatrix G K) S ∨
        GeometricBorderAtMost (inverseFourierMatrix G K) S) → lower ≤ S

theorem fourierComplexity : FourierComplexityTheorem.{u,v} := by
  sorry

noncomputable section

/-- One order-`n` transform over a common splitting field, in arbitrary coordinates. -/
structure FourierBlock (K : Type v) [Field K] (n : ℕ) where
  G : Type u
  [group : AddCommGroup G]
  [finiteGroup : Fintype G]
  admissible : Admissible G K
  points : Fin n ≃ G
  frequencies : Fin n ≃ Character G K
  inverse : Bool

attribute [instance] FourierBlock.group FourierBlock.finiteGroup

variable {K : Type v} [Field K] {n J : ℕ}

/-- The selected forward or normalized inverse transform in the given coordinates. -/
def FourierBlock.matrix (B : FourierBlock K n) : Matrix (Fin n) (Fin n) K :=
  if B.inverse then
    Matrix.reindex B.points.symm B.frequencies.symm (inverseFourierMatrix B.G K)
  else
    Matrix.reindex B.frequencies.symm B.points.symm (fourierMatrix B.G K)

/-- The direct sum of the selected transforms. Circuit gates may mix all batch indices. -/
def batchMatrix (B : Fin J → FourierBlock K n) : Matrix (Fin n × Fin J) (Fin n × Fin J) K :=
  Matrix.blockDiagonal (fun j => (B j).matrix)

/-- Number of nonzero entries of the whole transfer, including cross-block entries. -/
def matrixEntryCount {I O F : Type*} [Fintype I] [Fintype O] [Zero F] (Z : Matrix O I F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun ij : O × I => Z ij.1 ij.2 ≠ 0)).card

/-- Joint Zariski closure of a feedback transfer plus a rank error and an entrywise
sparse error. Both errors act on the whole matrix, including across batch indices. -/
def JointErrorBorderAtMost {I O : Type*} [Fintype I] [Fintype O]
    (M : Matrix O I K) (S : ℕ) (rankBudget supportBudget : ℝ) : Prop := by
  classical
  exact ∀ p : MvPolynomial (O × I) (AlgebraicClosure K),
    (∀ A B Z : Matrix O I (AlgebraicClosure K), FeedbackAtMost A S →
      (B.rank : ℝ) ≤ rankBudget →
      (matrixEntryCount Z : ℝ) ≤ supportBudget →
      MvPolynomial.eval (fun ij => (A + B + Z) ij.1 ij.2) p = 0) →
    MvPolynomial.eval (fun ij => algebraMap K (AlgebraicClosure K) (M ij.1 ij.2)) p = 0

end

/-- The joint robust statement with exact acyclic upper and lower estimates. -/
def BatchedFourierComplexityTheorem : Prop :=
  ∃ c β η : ℝ, 0 < c ∧ 0 < β ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ∃ C > (0 : ℝ),
    ∀ {J n : ℕ} (K : Type v) [Field K] (B : Fin J → FourierBlock.{u,v} K n),
      1 ≤ J → 2 ≤ n →
      let h : ℝ := J * (n : ℝ)
      let l := Real.sqrt (Real.logb (2 : ℕ) n)
      let T := batchMatrix B
      (c * h * l ≤ complexity T ∧
        (complexity T : ℝ) ≤
          C * h * (1 + Real.logb (2 : ℕ) n) ^ ((1 : ℝ) / (2 : ℕ) + ε)) ∧
      ∀ S : ℕ, JointErrorBorderAtMost T S (β * h) (η * h * (↑(2 : ℕ) : ℝ) ^ (l / (8 : ℕ))) →
        c * h * l ≤ S

/-- Theorem 1.1. The same positive lower constant and error fractions work
for all admissible fields, group orders, batch sizes and transform directions. -/
theorem batchedFourierComplexity : BatchedFourierComplexityTheorem.{u,v} := by
  sorry

end LinearAlgebra.FiniteFourier

end OAI
