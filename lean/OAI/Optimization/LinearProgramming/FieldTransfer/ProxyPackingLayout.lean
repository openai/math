import OAI.Optimization.LinearProgramming.RAM.Array

/-! Layout and loop invariant for the compacted list of symbolic logarithm operands. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace ProxyPacking

open RAM

structure Layout where
  n : Nat
  magnitudes : Nat
  flags : Nat
  coefficients : Nat
  bases : Nat
  exponents : Nat

/-- Two half-open scalar-register intervals are disjoint. -/
def Apart (a n b m : Nat) : Prop := a+n ≤ b ∨ b+m ≤ a

theorem Apart.ne {a n b m i j : Nat} (h : Apart a n b m) (hi : i < n) (hj : j < m) :
    a+i ≠ b+j := by rcases h with h | h <;> omega

structure Layout.Valid (l : Layout) : Prop where
  magHigh : 128 ≤ l.magnitudes
  flagsHigh : 128 ≤ l.flags
  rowHigh : 128 ≤ l.coefficients
  baseHigh : 128 ≤ l.bases
  expHigh : 128 ≤ l.exponents
  outputsApart : Apart l.bases (l.n+1) l.exponents (l.n+1)
  magBase : Apart l.magnitudes l.n l.bases (l.n+1)
  magExp : Apart l.magnitudes l.n l.exponents (l.n+1)
  rowBase : Apart l.coefficients l.n l.bases (l.n+1)
  rowExp : Apart l.coefficients l.n l.exponents (l.n+1)

variable {K : Type*} [Field K]

/-- The ascending selected input rows, preceded by the base-two constant. -/
def operandPrefix (pick : Nat → Bool) (mag : Nat → K) (a : Nat → ℤ)
    (offset : ℤ) (D j : Nat) : List (K × ℤ) :=
  (2,offset) :: ((List.range j).filter pick).map fun i => (mag i,(D:ℤ)*a i)

theorem operandPrefix_succ (pick : Nat → Bool) (mag : Nat → K) (a : Nat → ℤ)
    (offset : ℤ) (D j : Nat) :
    operandPrefix pick mag a offset D (j+1) = operandPrefix pick mag a offset D j ++
      (if pick j then [(mag j,(D:ℤ)*a j)] else []) := by
  cases h : pick j <;> simp [operandPrefix,List.range_succ,h]

theorem operandPrefix_length (pick : Nat → Bool) (mag : Nat → K) (a : Nat → ℤ)
    (offset : ℤ) (D j : Nat) : (operandPrefix pick mag a offset D j).length ≤ j+1 := by
  induction j with
  | zero => simp [operandPrefix]
  | succ j ih =>
    rw [operandPrefix_succ]
    cases pick j <;> simp <;> omega

/-- The stable cache and the current query row. Scalar 45 holds the offset produced by
the numerical subroutine. Logical address 86 points to the actual common denominator. -/
structure Inputs (l : Layout) (m : Memory K) (pick : Nat → Bool) (mag : Nat → K)
    (a : Nat → ℤ) (offset : ℤ) (D : Nat) : Prop where
  zero : m.index 62=0
  row : m.index 67=l.coefficients
  bases : m.index 68=l.bases
  exponents : m.index 69=l.exponents
  magnitudes : m.index 80=l.magnitudes
  flags : m.index 82=l.flags
  size : m.index 83=l.n
  scale : m.data (m.index 86)=(D:K)
  constant : m.data 45=(offset:K)
  magnitude : ∀ j < l.n, m.data (l.magnitudes+j)=mag j
  coefficient : ∀ j < l.n, m.data (l.coefficients+j)=(a j:K)
  selected : ∀ j < l.n, m.index (l.flags+j)=(pick j).toNat

def Contains (l : Layout) (m : Memory K) (ps : List (K × ℤ)) : Prop :=
  ∀ i, ∀ hi : i < ps.length,
    m.data (l.bases+i) = ps[i].1 ∧ m.data (l.exponents+i) = (ps[i].2:K)

/-- All mutable data needed by subsequent loop iterations, together with caller frames. -/
structure Stage (l : Layout) (orig : Memory K) (P : K → Prop) (D : Nat)
    (ps : List (K × ℤ)) (j : Nat) (s : Memory K) : Prop where
  safe : s.AllData P
  iter : s.index 70=j
  magCursor : s.index 71=l.magnitudes+j
  flagCursor : s.index 72=l.flags+j
  rowCursor : s.index 73=l.coefficients+j
  baseCursor : s.index 74=l.bases+ps.length
  expCursor : s.index 75=l.exponents+ps.length
  count : s.index 50=ps.length
  scale : s.data 23=(D:K)
  contents : Contains l s ps
  dataFrame : ∀ i, (i < 20 ∨ 23 < i) → (∀ k < ps.length, i ≠ l.bases+k) →
    (∀ k < ps.length, i ≠ l.exponents+k) → s.data i=orig.data i
  indexFrame : ∀ i, (i < 50 ∨ 52 < i) → (i < 70 ∨ 75 < i) → s.index i=orig.index i

end ProxyPacking
end FieldTransfer
end LinearProgramming
end Optimization
end OAI
