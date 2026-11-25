import Mathlib

/-! Strongly polynomial rational linear programming on a finite scalar/address RAM. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

variable {K : Type*}

inductive Instr where
  | const (dst : Nat) (q : ℚ)
  | copy (dst src : Nat)
  | add (dst left right : Nat)
  | sub (dst left right : Nat)
  | mul (dst left right : Nat)
  | div (dst left right : Nat)
  | load (dst addr : Nat)
  | store (addr src : Nat)
  | addrConst (dst n : Nat)
  | addrCopy (dst src : Nat)
  | incr (dst src : Nat)
  | decr (dst src : Nat)
  | addrLoad (dst addr : Nat)
  | addrStore (addr src : Nat)
  | branchLT (left right yes no : Nat)
  | branchAddrLT (left right yes no : Nat)
  | jump (target : Nat)
  | halt (tag : Nat)

abbrev Program := List Instr

structure State (K : Type*) where
  pc : Nat
  data : Nat → K
  index : Nat → Nat
  output : Option Nat

def start [Zero K] (dims : List Nat) (input : List K) : State K where
  pc := 0
  data i := input[i]?.getD 0
  index i := dims[i]?.getD 0
  output := none

def State.putData (s : State K) (dst : Nat) (x : K) : State K :=
  { s with pc := s.pc + 1, data := Function.update s.data dst x }

def State.putIndex (s : State K) (dst x : Nat) : State K :=
  { s with pc := s.pc + 1, index := Function.update s.index dst x }

/-- The instruction dispatcher. Jump destinations and direct register numbers occur in the
fixed program. Indirect addresses come solely from the address bank. -/
def execInstr [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (i : Instr) (s : State K) : Option (State K) :=
  match i with
  | .const d q => some (s.putData d (q : K))
  | .copy d a => some (s.putData d (s.data a))
  | .add d a b => some (s.putData d (s.data a + s.data b))
  | .sub d a b => some (s.putData d (s.data a - s.data b))
  | .mul d a b => some (s.putData d (s.data a * s.data b))
  | .div d a b => if s.data b = 0 then none else some (s.putData d (s.data a / s.data b))
  | .load d a => some (s.putData d (s.data (s.index a)))
  | .store a d => some (s.putData (s.index a) (s.data d))
  | .addrConst d n => some (s.putIndex d n)
  | .addrCopy d a => some (s.putIndex d (s.index a))
  | .incr d a => some (s.putIndex d (s.index a + 1))
  | .decr d a => some (s.putIndex d (s.index a - 1))
  | .addrLoad d a => some (s.putIndex d (s.index (s.index a)))
  | .addrStore a d => some (s.putIndex (s.index a) (s.index d))
  | .branchLT a b yes no => some { s with pc := if s.data a < s.data b then yes else no }
  | .branchAddrLT a b yes no => some { s with pc := if s.index a < s.index b then yes else no }
  | .jump target => some { s with pc := target }
  | .halt tag => some { s with output := some tag }

/-- A halted machine, an invalid instruction address and a zero divisor have no successor. -/
def step [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : Program) (s : State K) : Option (State K) :=
  match s.output, p[s.pc]? with
  | none, some i => execInstr i s
  | _, _ => none

/-- All states, including the initial and final register files, of exactly `k` instructions. -/
def Trace [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : Program) (s : State K) (k : Nat) (t : Fin (k + 1) → State K) : Prop :=
  t 0 = s ∧ ∀ i : Fin k, step p (t i.castSucc) = some (t i.succ)

/-- A polynomial envelope for an integer input size. -/
def polyBound (c e n : Nat) : Nat := c * (n + 1) ^ e

/-- One sign bit, one or more numerator bits and one or more denominator bits,
on the canonical reduced rational representation. -/
def ratBits (q : ℚ) : Nat := 3 + q.num.natAbs.log2 + q.den.log2

def totalBits (xs : List ℚ) : Nat := (xs.map ratBits).sum

def scalarBound (B : Nat) (s : State ℚ) : Prop := ∀ j, ratBits (s.data j) ≤ B

end RAM
end LinearProgramming
end Optimization
end OAI

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

/-- A dimension-polynomial run with a feasible point or sparse Farkas multiplier. -/
theorem strongly_polynomial_feasibility : StronglyPolynomialFeasibility := by sorry

/-- A dimension-polynomial run certifying infeasibility, an optimum, or unboundedness. -/
theorem strongly_polynomial_optimization : StronglyPolynomialOptimization := by sorry

end LinearProgramming
end Optimization
end OAI
