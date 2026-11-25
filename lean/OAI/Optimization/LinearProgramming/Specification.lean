import OAI.Optimization.LinearProgramming.RAM.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Finset.Card

/-! Input and result layouts for Theorem 1.1, Corollary 1.2 and Theorem 8.1. -/
namespace OAI
namespace Optimization
namespace LinearProgramming

variable {K : Type*}

open RAM Matrix

/-- The scalar input tape contains `A` by rows followed by `b`. Dimensions occupy address
registers zero and one. All other registers initially contain zero. -/
def lpInput {m d : Nat} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) : List K :=
  (List.ofFn fun i => List.ofFn (A i)).flatten ++ List.ofFn b

def readVector (s : State K) (offset n : Nat) : Fin n → K := fun i => s.data (offset + i.val)

def Feasible [Field K] [LinearOrder K] {m d : Nat} (A : Matrix (Fin m) (Fin d) K)
    (b : Fin m → K) (x : Fin d → K) : Prop := A *ᵥ x ≤ b

def Certificate [Field K] [LinearOrder K] {m d : Nat} (A : Matrix (Fin m) (Fin d) K)
    (b y : Fin m → K) : Prop :=
  0 ≤ y ∧ A.transpose *ᵥ y = 0 ∧ b ⬝ᵥ y < 0 ∧
    (Finset.univ.filter fun i => y i ≠ 0).card ≤ A.rank + 1

/-- Tag 0 returns a primal point. Tag 1 returns a sparse Farkas multiplier. -/
def FeasibilityOutput [Field K] [LinearOrder K] {m d : Nat} (A : Matrix (Fin m) (Fin d) K)
    (b : Fin m → K) (s : State K) : Prop :=
  (s.output = some 0 ∧ Feasible A b (readVector s 0 d)) ∨
  (s.output = some 1 ∧ Certificate A b (readVector s 0 m))

/-- The ordered-field theorem normalizes the certificate to `bᵀ y = -1`. -/
def NormalizedFeasibilityOutput [Field K] [LinearOrder K] {m d : Nat}
    (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (s : State K) : Prop :=
  (s.output = some 0 ∧ Feasible A b (readVector s 0 d)) ∨
  (s.output = some 1 ∧ Certificate A b (readVector s 0 m) ∧ b ⬝ᵥ readVector s 0 m = -1)

/-- Tag 0 returns a sparse infeasibility certificate, tag 1 a primal point, dual
multiplier and common objective, and tag 2 a feasible base point and normalized ray. -/
def OptimizationOutput {m d : Nat} (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (c : Fin d → ℚ) (s : State ℚ) : Prop :=
  let x := readVector s 0 d
  let y := readVector s d m
  let value := s.data (d + m)
  let v := readVector s d d
  (s.output = some 0 ∧ Certificate A b (readVector s 0 m)) ∨
  (s.output = some 1 ∧ Feasible A b x ∧ 0 ≤ y ∧ A.transpose *ᵥ y = c ∧
    c ⬝ᵥ x = value ∧ b ⬝ᵥ y = value ∧ ∀ z, Feasible A b z → c ⬝ᵥ z ≤ value) ∨
  (s.output = some 2 ∧ Feasible A b x ∧ A *ᵥ v ≤ 0 ∧ c ⬝ᵥ v = 1)

/-- The four constants and program precede both dimensions and all input values. -/
def StronglyPolynomialFeasibility : Prop :=
  ∃ (p : Program) (c e bC bE : Nat), ∀ (m d : Nat), 0 < m → 0 < d →
    ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ),
    ∃ (k : Nat) (t : Fin (k + 1) → State ℚ),
      Trace p (start [m, d] (lpInput A b)) k t ∧ k ≤ polyBound c e (m + d) ∧
      (∀ i, scalarBound (polyBound bC bE (totalBits (lpInput A b))) (t i)) ∧
      FeasibilityOutput A b (t (Fin.last k))

/-- The same program operates on all rational optimization instances. The separate
reduction in §2 bounds the number of feasibility calls. -/
def StronglyPolynomialOptimization : Prop :=
  ∃ (p : Program) (c e bC bE : Nat), ∀ (m d : Nat), 0 < m → 0 < d →
    ∀ (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (obj : Fin d → ℚ),
    let input := lpInput A b ++ List.ofFn obj
    ∃ (k : Nat) (t : Fin (k + 1) → State ℚ),
      Trace p (start [m, d] input) k t ∧ k ≤ polyBound c e (m + d) ∧
      (∀ i, scalarBound (polyBound bC bE (totalBits input)) (t i)) ∧
      OptimizationOutput A b obj (t (Fin.last k))

universe u
/-- One finite rational-constant program is selected before the input field. -/
def StronglyPolynomialOrderedFieldFeasibility : Prop :=
  ∃ (p : Program) (c e : Nat), ∀ (K : Type u) [Field K] [LinearOrder K] [IsStrictOrderedRing K],
    ∀ (m d : Nat), 0 < m → 0 < d → ∀ (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K),
    ∃ (k : Nat) (t : Fin (k + 1) → State K),
      Trace p (start [m, d] (lpInput A b)) k t ∧ k ≤ polyBound c e (m + d) ∧
      NormalizedFeasibilityOutput A b (t (Fin.last k))

end LinearProgramming
end Optimization
end OAI
