import OAI.Optimization.LinearProgramming.Compression.Commit
import OAI.Optimization.LinearProgramming.Lattice.Precision

/-! A single size cap for the existential and computed commitments in each epoch. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- The finite-existence proof and the rational approximation routine use different
radices. This cap is valid for both. -/
def fiberCommitCap (d M : ℕ) : ℕ :=
  max (commitHeight d M) (2^(Lattice.radixWidth (d+1) M * (d+1)))

theorem commitHeight_le_fiberCommitCap (d M : ℕ) : commitHeight d M ≤ fiberCommitCap d M :=
  le_max_left _ _

theorem computed_lt_fiberCommitCap {d M a : ℕ}
    (ha : a.size ≤ Lattice.radixWidth (d+1) M * (d+1)) : a < fiberCommitCap d M :=
  (Nat.size_le.mp ha).trans_le (le_max_right _ _)

/-- Polynomial exponent when the sign-form budget M is at most 2^m. -/
def fiberCommitCapFormula {R : Type*} [CommSemiring R] (d m : R) : R :=
  ((m+1) + (4*(d+2) + (m+1) + 6) * (d+2) + 3) * (d+1)

/-- Both radix bounds have polynomial bit length in dimension and bit length of M. -/
theorem fiberCommitCap_le_two_pow (d M m : ℕ) (hM : M ≤ 2^m) :
    fiberCommitCap d M ≤ 2^(fiberCommitCapFormula d m) := by
  have hsize : M.size ≤ m+1 := Nat.size_le.mpr (hM.trans_lt
    (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self m)))
  have hlog : M.log2 ≤ m := by
    by_cases h : M = 0
    · simp [h]
    · exact Nat.le_of_lt_succ ((Nat.log2_lt h).mpr (hM.trans_lt
        (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self m))))
  apply max_le
  · apply (commitHeight d M).lt_log2_self.le.trans
    apply Nat.pow_le_pow_right (by decide)
    calc
      _ ≤ ((d+M.log2+4)*(d+1)+M.log2+4)*(d+1)+1 :=
        Nat.add_le_add_right (commitHeight_log2_le d M) 1
      _ ≤ ((d+m+4)*(d+1)+m+4)*(d+1)+1 := by gcongr
      _ ≤ fiberCommitCapFormula d m := by unfold fiberCommitCapFormula; ring_nf; omega
  · apply Nat.pow_le_pow_right (by decide)
    let exponent (v : ℕ) := (v + (4*((d+1)+1) + v + 6) * ((d+1)+1) + 3) * (d+1)
    have mono : Monotone exponent := by
      intro a b hab
      dsimp [exponent]
      gcongr
    exact mono hsize

end Compression
end LinearProgramming
end Optimization
end OAI
