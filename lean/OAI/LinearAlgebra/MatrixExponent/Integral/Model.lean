import OAI.LinearAlgebra.MatrixExponent.Rectangle.Model

/-! Division-free circuits computing formal polynomial identities over a ring. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Integral

abbrev Pos := Rectangle.Pos
abbrev Var := Rectangle.Var
abbrev Poly (F : Type*) [CommRing F] (i j k : ℕ) := MvPolynomial (Var i j k) F
abbrev side := Rectangle.side

abbrev input (F : Type*) [CommRing F] {i j k : ℕ} (x : Var i j k) : Poly F i j k :=
  MvPolynomial.X x

inductive Build {K : Type*} [CommRing K] (S : Set K) : ℕ → Set K → Prop
  | nil : Build S 0 S
  | add {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x + y) T)
  | sub {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x - y) T)
  | mul {m T x y} : Build S m T → x ∈ T → y ∈ T → Build S (m + 1) (insert (x * y) T)

def initial (F : Type*) [CommRing F] (i j k : ℕ) : Set (Poly F i j k) :=
  Set.range (algebraMap F (Poly F i j k)) ∪ Set.range (input F)

def output (F : Type*) [CommRing F] {i j k : ℕ} (p : Pos i j) : Poly F i j k :=
  ∑ l : Fin k, input F (.inl (p.1, l)) * input F (.inr (l, p.2))

def Computes (F : Type*) [CommRing F] (i j k m : ℕ) : Prop :=
  ∃ T, Build (initial F i j k) m T ∧ ∀ p : Pos i j, output F p ∈ T

def Admissible (F : Type*) [CommRing F] (a b c s : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, Computes F (side n a) (side n b) (side n c) m ∧
      (m : ℝ) ≤ C * (n : ℝ) ^ (s + ε)

def exponent (F : Type*) [CommRing F] (a b c : ℝ) : ℝ := sInf {s | Admissible F a b c s}

def Rank (F : Type*) [CommRing F] (i j k r : ℕ) : Prop :=
  ∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F),
    ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0

end OAI.LinearAlgebra.MatrixExponent.Integral
