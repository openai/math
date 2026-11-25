import OAI.Optimization.LinearProgramming.RAM.Array

/-! Workspace for the signed-power serialization and its protected cells. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

structure SymbolicPairAreas where
  bases : ℕ
  exponents : ℕ
  scalarTape : ℕ
  digits : ℕ
  tokenStart : ℕ

def symbolicTokenBudget (N w : ℕ) := N*(w+2)

def symbolicEncodeSteps (N w : ℕ) :=
  3+((w*(16*w+32)+37)*N+12*(N*(w+2))+7*N+51)

structure SymbolicPairAreas.Valid (b : SymbolicPairAreas) (N w : ℕ) : Prop where
  basesHigh : 128 ≤ b.bases
  exponentsHigh : 128 ≤ b.exponents
  scalarHigh : 128 ≤ b.scalarTape
  digitsHigh : 128 ≤ b.digits
  tokenRoom : 128+2*symbolicTokenBudget N w+8 ≤ b.tokenStart
  expDigits : b.exponents+N ≤ b.digits ∨ b.digits+w ≤ b.exponents
  baseDigits : b.bases+N ≤ b.digits ∨ b.digits+w ≤ b.bases
  baseTape : b.bases+N ≤ b.scalarTape ∨ b.scalarTape+4+N ≤ b.bases

/-- The output outside the digit, scalar and address buffers is preserved.
Only the explicitly listed low control registers may also have changed. -/
structure SymbolicSerializeFrame (b : SymbolicPairAreas) (N w : ℕ) (m t : Memory ℚ) : Prop where
  data : ∀ i, 6 ≤ i → i ≠ 40 → i ≠ 41 → (i < b.digits ∨ b.digits + w ≤ i) →
    (i < b.scalarTape ∨ b.scalarTape + (N+4) ≤ i) → t.data i = m.data i
  index : ∀ i, 43 ≤ i → i ≠ 52 → i ≠ 54 → i ≠ 55 → i ≠ 56 → i ≠ 57 → i ≠ 58 → i ≠ 59 →
    (i < b.tokenStart - (2*symbolicTokenBudget N w+8) ∨ b.tokenStart + symbolicTokenBudget N w ≤ i) →
    t.index i = m.index i

end Compression
end LinearProgramming
end Optimization
end OAI
