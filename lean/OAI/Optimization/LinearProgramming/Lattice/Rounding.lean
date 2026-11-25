import OAI.Optimization.LinearProgramming.Lattice.Dirichlet
import OAI.Optimization.LinearProgramming.Lattice.Projection
import OAI.Optimization.LinearProgramming.Lattice.Induction

/-! Bounded integer representatives for all short homogeneous comparisons, including ties. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open SignType WithLp

/-- Bound for one direction obtained by simultaneous approximation at precision
`1 / (4 p M)`. It is uniform in the input vector. -/
def directionBound (p M : ℕ) : ℕ := (4 * p * M) ^ p + 1

/-- The radix used to pack at most `p` bounded comparison directions. -/
def comparisonRadix (p M : ℕ) : ℕ := 2 * M * directionBound p M + 2

/-- The sign profile of every integer form of one-norm at most `M` has an integer
representative whose coordinates have at most `p * log₂(comparisonRadix p M) + 1`
bits. In particular, the size is independent of the real vector. -/
theorem exists_bounded_sign_representative {p M : ℕ} (hp : 0 < p) (hM : 0 < M)
    (v : Fin p → ℝ) :
    ∃ z : Fin p → ℤ, (∀ i, |z i| < (comparisonRadix p M : ℤ) ^ p) ∧
      ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
        sign (dotProduct a z) = sign (dotProduct (realCoordinates a) v) := by
  classical
  let Q := 4 * p * M
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have step (S : Submodule ℝ (EuclideanSpace ℝ (Fin p))) (hv : toLp 2 v ∉ S) :
      ∃ z : Fin p → ℤ, (∀ i, |z i| ≤ (directionBound p M : ℤ)) ∧
        toLp 2 (fun i => (z i : ℝ)) ∉ S ∧
        ∀ a : Fin p → ℤ, (∑ i, |a i|) ≤ (M : ℤ) →
          (∀ y ∈ S, dotProduct (fun i => (a i : ℝ)) y.ofLp = 0) →
          dotProduct a z ≠ 0 →
            sign (dotProduct a z) = sign (dotProduct (fun i => (a i : ℝ)) v) := by
    obtain ⟨q, hq, hqle, z, happrox⟩ := simultaneous_dirichlet hQ (roundingDirection S v)
    have he : ∀ i, |(q : ℝ) * roundingDirection S v i - z i| ≤ 1 / (4 * (p : ℝ) * M) := by
      simpa [Q] using happrox
    refine ⟨z, ?_, roundingProjectionStep S v hv hp hM q hq z he⟩
    intro i
    have hunit : 1 / (Q : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < Q), one_mul]
      exact_mod_cast hQ
    have hsmall : |(z i : ℝ)| ≤ (q : ℝ) + 1 := by
      calc
        |(z i : ℝ)| = |(q : ℝ) * roundingDirection S v i - ((q : ℝ) * roundingDirection S v i - z i)| := by ring_nf
        _ ≤ |(q : ℝ) * roundingDirection S v i| + |(q : ℝ) * roundingDirection S v i - z i| := abs_sub ..
        _ ≤ (q : ℝ) + 1 := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
          exact add_le_add (mul_le_of_le_one_right (by positivity) (abs_roundingDirection_le_one S v i))
            ((happrox i).trans hunit)
    have hzq : |z i| ≤ (q : ℤ) + 1 := by exact_mod_cast hsmall
    exact hzq.trans (by exact_mod_cast Nat.add_le_add_right hqle 1)
  obtain ⟨zs, hlen, hz, hsign⟩ :=
    exists_comparison_directions v M (directionBound p M) step
  let B : ℤ := comparisonRadix p M
  have hD : 0 ≤ (directionBound p M : ℤ) := by positivity
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hprod : (directionBound p M : ℤ) ≤ M * directionBound p M := by
    simpa using mul_le_mul_of_nonneg_right hM' hD
  have hBC : B = 2 * M * directionBound p M + 2 := by simp [B, comparisonRadix]
  have hB : 1 ≤ B := by nlinarith
  refine ⟨radixVector B zs, ?_, ?_⟩
  · intro i
    have hb : ∀ z ∈ zs, ∀ j, |z j| < B := fun z hm j => (hz z hm j).trans_lt (by nlinarith)
    exact (abs_radixVector_lt (by omega) zs hb i).trans_le (pow_le_pow_right₀ hB hlen)
  · intro a ha
    rw [sign_dotProduct_radixVector (by omega) hD (by nlinarith) zs hz a ha]
    exact hsign a ha

end Lattice
end LinearProgramming
end Optimization
end OAI
