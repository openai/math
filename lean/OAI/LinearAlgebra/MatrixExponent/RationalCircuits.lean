import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Formal arithmetic complexity of square matrix multiplication

A straight-line computation records the set of available wire values. All
inputs and field constants are initially available. One step adds the value
of one binary gate, with unrestricted reuse. The division rule tests the
denominator in the rational function field, even in positive characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent

abbrev Pos (n : ℕ) := Fin n × Fin n
abbrev Var (n : ℕ) := Pos n ⊕ Pos n
abbrev Rat (F : Type*) [Field F] (n : ℕ) := FractionRing (MvPolynomial (Var n) F)

def input (F : Type*) [Field F] {n : ℕ} (i : Var n) : Rat F n :=
  algebraMap (MvPolynomial (Var n) F) (Rat F n) (MvPolynomial.X i)

def initial (F : Type*) [Field F] (n : ℕ) : Set (Rat F n) :=
  Set.range (algebraMap F (Rat F n)) ∪ Set.range (input F)

def output (F : Type*) [Field F] {n : ℕ} (p : Pos n) : Rat F n :=
  ∑ k : Fin n, input F (.inl (p.1, k)) * input F (.inr (k, p.2))

inductive Build {K : Type*} [Field K] (S : Set K) : ℕ → Set K → Prop
  | nil : Build S 0 S
  | add {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x + y) T)
  | sub {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x - y) T)
  | mul {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x * y) T)
  | div {m T x y} : Build S m T → x ∈ T → y ∈ T → y ≠ 0 → Build S (m + 1) (insert (x / y) T)

def Computes (F : Type*) [Field F] (n m : ℕ) : Prop :=
  ∃ T, Build (initial F n) m T ∧ ∀ p : Pos n, output F p ∈ T

def Admissible (F : Type*) [Field F] (s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, Computes F n m ∧ (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)

def omega (F : Type*) [Field F] : ℝ := sInf {s | Admissible F s}

/-- Coefficient equations for a rank decomposition. The last index is an
output position (row of the left input, column of the right input). -/
def RankLE (F : Type*) [Field F] (n r : ℕ) : Prop :=
  ∃ a b c : Fin r → Pos n → F, ∀ x y z : Pos n,
    ∑ i : Fin r, a i x * b i y * c i z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0

end OAI.LinearAlgebra.MatrixExponent
