import OAI.LinearAlgebra.MatrixExponent.RationalCircuits

/-!
# The arithmetic exponent for rectangular products

The side lengths are ordered as rows, columns, inner dimension. The
straight-line circuit rules are shared with the square model.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

abbrev Pos (i j : ℕ) := Fin i × Fin j
abbrev Var (i j k : ℕ) := Pos i k ⊕ Pos k j
abbrev Rat (F : Type*) [Field F] (i j k : ℕ) := FractionRing (MvPolynomial (Var i j k) F)

def input (F : Type*) [Field F] {i j k : ℕ} (x : Var i j k) : Rat F i j k :=
  algebraMap (MvPolynomial (Var i j k) F) (Rat F i j k) (MvPolynomial.X x)

def initial (F : Type*) [Field F] (i j k : ℕ) : Set (Rat F i j k) :=
  Set.range (algebraMap F (Rat F i j k)) ∪ Set.range (input F)

def output (F : Type*) [Field F] {i j k : ℕ} (p : Pos i j) : Rat F i j k :=
  ∑ l : Fin k, input F (.inl (p.1, l)) * input F (.inr (l, p.2))

def Computes (F : Type*) [Field F] (i j k m : ℕ) : Prop :=
  ∃ T, Build (initial F i j k) m T ∧ ∀ p : Pos i j, output F p ∈ T

def side (n : ℕ) (a : ℝ) : ℕ := ⌈(n : ℝ) ^ a⌉₊

def Admissible (F : Type*) [Field F] (a b c s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, Computes F (side n a) (side n b) (side n c) m ∧
      (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)

def exponent (F : Type*) [Field F] (a b c : ℝ) : ℝ := sInf {s | Admissible F a b c s}

def dual (F : Type*) [Field F] (a b : ℝ) : ℝ :=
  sSup {c ∈ Set.Icc 0 (min a b) | exponent F a b c = a + b}

def RankLE (F : Type*) [Field F] (i j k r : ℕ) : Prop :=
  ∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F),
    ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0

/-- The benchmark on the cone where the last coordinate is smallest. -/
def benchmark (a b c : ℝ) : ℝ :=
  a + b + (max ((a + b) * c - a * b) 0) ^ 2 / (4 * a * b * c)

/-- Evaluate the benchmark with a smallest side placed last. Division by
zero in the real-valued formula returns zero on a coordinate plane. -/
def U (a b c : ℝ) : ℝ :=
  if c ≤ min a b then benchmark a b c
  else if a ≤ b then benchmark b c a
  else benchmark c a b

/-- The part of the rectangular rigidity dichotomy used in Corollary 1.2.
An active shape is one where the benchmark exceeds every pair sum. -/
def Rigidity (F : Type*) [Field F] : Prop :=
  (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → exponent F a b c = U a b c) ∨
  (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
    max (a + b) (max (a + c) (b + c)) < U a b c → exponent F a b c < U a b c)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
