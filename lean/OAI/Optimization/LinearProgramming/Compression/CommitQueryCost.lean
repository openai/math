import OAI.Optimization.LinearProgramming.Compression.CommitProgram
import OAI.Optimization.LinearProgramming.Lattice.OracleQuerySize

/-! ## Sizes of the affine comparisons issued by an actual commitment

The last entry of a homogeneous query is the affine constant. The estimate
holds for a dimension-wide cutoff greater than the local requirement.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.Lattice

/-- Given a per-coefficient size bound, count all d+1 terms including the affine
constant. Any larger global cutoff still bounds the cleared comparison. -/
theorem affine_l1_of_width {d w k fuel : ℕ} (hFuel : k + (d+1) + w ≤ fuel)
    (row : Fin (d+1) → ℤ) (hw : ∀ j, (row j).natAbs.size ≤ w) :
    let A : ℤ := ((d+1 : ℕ) : ℤ) * 2^w
    (|row (Fin.last d)| + ∑ j : Fin d, |row j.castSucc| ≤ A) ∧ (2 : ℤ)^k * A ≤ 2^fuel := by
  have bound (j : Fin (d+1)) : |row j| ≤ (2 : ℤ)^w := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast (Nat.size_le.mp (hw j)).le
  constructor
  · rw [add_comm, ← Fin.sum_univ_castSucc (fun j : Fin (d+1) => |row j|)]
    simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ : Fin (d+1) => (2 : ℤ)^w)
      (fun i _ => bound i)
  · have hd : ((d+1 : ℕ) : ℤ) ≤ (2 : ℤ)^(d+1) := by exact_mod_cast (d+1).lt_two_pow_self.le
    calc
      _ = (2 : ℤ)^k * ((d+1 : ℕ) : ℤ) * 2^w := by ring
      _ ≤ (2 : ℤ)^k * 2^(d+1) * 2^w := by gcongr
      _ = (2 : ℤ)^(k+(d+1)+w) := by rw [← pow_add, ← pow_add]
      _ ≤ _ := pow_le_pow_right₀ (by decide) hFuel

/-- Size of a member of the adaptive homogeneous query history, regarded as an
affine query. This includes both the concrete exhaustive selector and an LLL selector. -/
theorem roundingProgramWith_affine_l1 {d M k fuel : ℕ} (hM : 0 < M)
    (select : (Fin (d+1) → ℚ) → ℕ × (Fin (d+1) → ℤ))
    (hsel : ∀ u, 0 < (select u).1 ∧ (select u).1 ≤ searchDenominator (d+1) M ^ ((d+1)+1) ∧
      ∀ i, |((select u).1 : ℚ) * u i - (select u).2 i| ≤ 1 / (8 * ((d+1 : ℕ) : ℚ) * M))
    (x : Fin d → ℝ) (oracle : (Fin (d+1) → ℤ) → Bool)
    (ho : ∀ a, oracle a = true ↔ 0 ≤ formValue a (Fin.snoc x (1 : ℝ)))
    (row : Fin (d+1) → ℤ) (hr : row ∈ SignQueries.history oracle (roundingProgramWith M select))
    (hFuel : k+(d+1)+queryCoefficientWidth (d+1) M ≤ fuel) :
    let A : ℤ := ((d+1 : ℕ) : ℤ) * 2^queryCoefficientWidth (d+1) M
    (|row (Fin.last d)| + ∑ j : Fin d, |row j.castSucc| ≤ A) ∧ (2 : ℤ)^k * A ≤ 2^fuel :=
  affine_l1_of_width hFuel row (roundingProgramWith_query_size (Nat.succ_pos d) hM
    select hsel (Fin.snoc x 1) oracle ho hr)

/-- The same history bound applies directly to a strict-negative affine oracle,
as used to compute the rational commitment. -/
theorem computeCommitWith_query_l1 {d M k fuel : ℕ} (x : Fin d → ℝ) (hM : 0 < M)
    (select : (Fin (d+1) → ℚ) → ℕ × (Fin (d+1) → ℤ))
    (hsel : ∀ u, 0 < (select u).1 ∧ (select u).1 ≤ searchDenominator (d+1) M ^ ((d+1)+1) ∧
      ∀ i, |((select u).1 : ℚ) * u i - (select u).2 i| ≤ 1 / (8 * ((d+1 : ℕ) : ℚ) * M))
    (negative : (Fin d → ℤ) → ℤ → Bool)
    (ho : ∀ a c, negative a c = true ↔ requestForm x a + c < 0)
    (row : Fin (d+1) → ℤ) (hr : row ∈
      SignQueries.history (affineCommitReply negative) (roundingProgramWith M select))
    (hFuel : k+(d+1)+queryCoefficientWidth (d+1) M ≤ fuel) :
    let A : ℤ := ((d+1 : ℕ) : ℤ) * 2^queryCoefficientWidth (d+1) M
    (|row (Fin.last d)| + ∑ j : Fin d, |row j.castSucc| ≤ A) ∧ (2 : ℤ)^k * A ≤ 2^fuel :=
  roundingProgramWith_affine_l1 hM select hsel x (affineCommitReply negative)
    (affineCommitReply_correct x negative ho) row hr hFuel

end Compression
end LinearProgramming
end Optimization
end OAI
