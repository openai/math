import OAI.Computability.NearSquareRoot.PrecisionRulers
import OAI.Computability.NearSquareRoot.PrecisionButterflyLayer
import OAI.Computability.NearSquareRoot.PrecisionButterflyPrepare

/-! # Generating the complete odd-bit normalization header

The subroutine reads just the unary address width. It expands the two width
rulers, computes the dyadic reciprocal square root by integer arithmetic, and
returns the fractional ruler together with the signed complex coefficient.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ButterflyTask

open IntegerMultiplication Code FixedPoint

/-- A polynomial-time function on an encoded unary ruler. -/
def makeHeader (l : Tally) : Grid.Orb :=
  (affineTally 70 1 l, invSqrtRecordWord (affineTally 70 1 l, affineTally 96 4 l, [false,true]))

theorem makeHeader_poly : Poly makeHeader := by
  have h₁ := (easyAffine 70 1).poly
  have h₂ := (easyAffine 96 4).poly
  exact h₁.pair ((h₁.pair (h₂.pair (IntegerMultiplication.Code.Poly.const (X := Tally) [false,true]))).compose invSqrtRecordWord_poly)

theorem makeHeader_eq (k : ℕ) : makeHeader (tally k) = header id butterflyCoefficient k := by
  simp only [makeHeader, affine_tally, header, id_eq, fractionBits, componentBits]
  have hwidth : (tally (70*k+1)).length+1 ≤ (tally (96*k+4)).length := by
    simp only [tally_length]; omega
  rw [invSqrtRecordWord_spec _ _ _ hwidth, tally_length, tally_length]
  rfl

/-- One input-independent command for scalar setup, charged to a polynomial
in the address width including the cost of emitting the header. -/
theorem buildHeader : ∃ d : ℕ, Task (fun k : ℕ => (k+1)^d)
    (fun k => send (tally k)) (fun k => send (header id butterflyCoefficient k)) := by
  obtain ⟨steps, ⟨d, C, h⟩, run⟩ := makeHeader_poly
  refine ⟨d, ?_⟩
  have cmd := run.on tally
  simp only [makeHeader_eq] at cmd
  apply cmd.bound (C*2^d+1)
  intro k
  have bound := h (tally k)
  rw [size_tally, tally_length] at bound
  have he : (2*k+1+1)^d = 2^d * (k+1)^d := by rw [← mul_pow]; congr 1
  rw [he, ← Nat.mul_assoc] at bound
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

end ButterflyTask

end NearSquareRoot
end Computability
end OAI
