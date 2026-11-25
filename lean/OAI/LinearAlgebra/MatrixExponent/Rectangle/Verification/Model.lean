import OAI.LinearAlgebra.MatrixExponent.Integral.Model
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Public seeds and division-free arithmetic verification

Each seed chooses a straight-line program followed by scalar equality
tests. Its cost counts all binary arithmetic instructions and all tests.
This is a subclass of the equality-test trees in Section 8.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Filter Finset
open scoped Classical

abbrev Index (n : ℕ) := Fin 3 × Rectangle.Pos n n
abbrev Poly (F : Type*) [Field F] (n : ℕ) := MvPolynomial (Index n) F

def inputs (F : Type*) [Field F] (n : ℕ) : Set (Poly F n) :=
  Set.range MvPolynomial.C ∪ Set.range MvPolynomial.X

variable {F : Type*} [Field F] {n : ℕ}

def Correct (x : Index n → F) : Prop :=
  ∀ i j : Fin n, ∑ k, x (0, i, k) * x (1, k, j) = x (2, i, j)

structure Test (F : Type*) [Field F] (n : ℕ) where
  count : ℕ
  left : Fin count → Poly F n
  right : Fin count → Poly F n

def Test.accept (T : Test F n) (x : Index n → F) : Prop :=
  ∀ i, MvPolynomial.eval x (T.left i) = MvPolynomial.eval x (T.right i)

def Test.cost (T : Test F n) (c : ℝ) : Prop :=
  ∃ (m : ℕ) (V : Set (Poly F n)), Integral.Build (inputs F n) m V ∧
    (∀ i, T.left i ∈ V ∧ T.right i ∈ V) ∧ (m : ℝ) + T.count ≤ c

def Uniform (F : Type*) [Field F] (n : ℕ) (s c p : ℝ) : Prop :=
  ∃ (L : ℕ) (A : Fin L → Test F n), 0 < L ∧ (L : ℝ) ≤ s ∧ (∀ i, (A i).cost c) ∧
    (∀ x, Correct x → ∀ i, (A i).accept x) ∧
    ∀ x, ¬ Correct x → (#{i | (A i).accept x} : ℝ) ≤ p * L

def Support (F : Type*) [Field F] (ρ v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ p > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Uniform F n ((n : ℝ) ^ (ρ + ε)) ((n : ℝ) ^ (v + ε)) p

def Entropy (F : Type*) [Field F] (η v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (L : ℕ) (A : Fin L → Test F n) (w : Fin L → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ -(∑ i, w i * Real.log (w i)) ≤ (η + ε) * Real.log n ∧
      (∀ i, (A i).cost ((n : ℝ) ^ (v + ε))) ∧
      ∀ x, (∑ i, if (A i).accept x ↔ Correct x then w i else 0) ≥ 2 / 3

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
