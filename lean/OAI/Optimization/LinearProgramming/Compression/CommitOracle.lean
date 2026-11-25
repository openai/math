import OAI.Optimization.LinearProgramming.Compression.Commit
import OAI.Optimization.LinearProgramming.Compression.ProxyOracle
import OAI.Optimization.LinearProgramming.Lattice.Oracle

/-! Committing to a generator vector with exact rational sign tests on only the listed generators.
The query count here counts the calls of the interactive rounding procedure. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators
open SignType

/-- The logarithmic proxy assigned to each entry of the current finite generator list. -/
noncomputable def generatorProxy {d : ℕ} (fuel k : ℕ) (magnitude : Fin d → ℚ) (i : Fin d) : ℝ :=
  logProxyValue k (magnitude i) (logProxyNumerator fuel k (magnitude i))

/-- A homogeneous dot product on `(proxy,1)` is one affine sign test on the list of generators. -/
def generatorSign {d : ℕ} (fuel k : ℕ) (magnitude : Fin d → ℚ) (a : Fin (d+1) → ℤ) : SignType :=
  match logProxySign fuel k (a (Fin.last d)) (fun i ↦ a i.castSucc) magnitude with
  | .lt => -1
  | .eq => 0
  | .gt => 1

theorem generatorSign_correct {d : ℕ} (fuel k : ℕ) (magnitude : Fin d → ℚ)
    (hm : ∀ i, 0 < magnitude i) (a : Fin (d+1) → ℤ) :
    generatorSign fuel k magnitude a =
      sign (dotProduct (Lattice.realCoordinates a) (Fin.snoc (generatorProxy fuel k magnitude) 1)) := by
  let w : ℝ := a (Fin.last d) + ∑ i : Fin d, (a i.castSucc : ℝ) * generatorProxy fuel k magnitude i
  have hw : dotProduct (Lattice.realCoordinates a) (Fin.snoc (generatorProxy fuel k magnitude) 1) = w := by
    simp [w, dotProduct, Lattice.realCoordinates, Fin.sum_univ_castSucc, add_comm]
  rw [hw]
  unfold generatorSign
  rw [logProxySign_correct fuel k _ _ magnitude hm]
  change (match (if w < 0 then Ordering.lt else if 0 < w then .gt else .eq) with
    | .lt => (-1 : SignType) | .eq => 0 | .gt => 1) = sign w
  rcases lt_trichotomy w 0 with h | h | h
  · simp [h, sign_neg h]
  · simp [h]
  · simp [h, h.not_gt, sign_pos h]

/-- The integer direction used for a commitment; all algorithmic input scalars are rational. -/
def generatorCommitVector {d : ℕ} (fuel k M : ℕ) (magnitude : Fin d → ℚ) : Fin (d+1) → ℤ :=
  Lattice.SignQueries.run (fun c ↦ decide (0 ≤ generatorSign fuel k magnitude c))
    (Lattice.oracleRoundingProgram (d+1) M)

/-- The normalized committed prices computed from the homogeneous direction. -/
def generatorCommit {d : ℕ} (fuel k M : ℕ) (magnitude : Fin d → ℚ) : Fin d → ℚ :=
  normalizeCommit (generatorCommitVector fuel k M magnitude)

/-- The concrete sign-only computation has positive final coordinate, preserves ties and all
bounded affine comparisons, and uses a bounded number of generator sign queries. -/
theorem generatorCommit_correct {d : ℕ} (fuel k M : ℕ) (hM : 0 < M) (magnitude : Fin d → ℚ)
    (hm : ∀ i, 0 < magnitude i) :
    let γ := generatorCommit fuel k M magnitude
    let X := 2^(Lattice.radixWidth (d+1) M * (d+1))
    (Lattice.SignQueries.cost (fun c ↦ decide (0 ≤ generatorSign fuel k magnitude c))
      (Lattice.oracleRoundingProgram (d+1) M) ≤
        (d+1)*(2*(d+1)+1+(d+1)*Lattice.searchPrecision (d+1) M)) ∧
    0 < generatorCommitVector fuel k M magnitude (Fin.last d) ∧
    (∀ i, (γ i).num.natAbs < X ∧ (γ i).den < X) ∧
    (∀ (a : Fin d → ℤ) (c : ℤ), (∑ i, |a i|) + |c| ≤ (M : ℤ) →
      sign (requestForm (fun i ↦ (γ i : ℝ)) a + c) =
        sign (requestForm (generatorProxy fuel k magnitude) a + c)) ∧
    RequestSigns (generatorProxy fuel k magnitude) (fun i ↦ (γ i : ℝ)) M := by
  obtain ⟨calls, hs, hz⟩ := Lattice.oracleRoundingProgram_correct (Nat.succ_pos d) hM _
    (generatorSign fuel k magnitude) (generatorSign_correct fuel k magnitude hm)
  exact ⟨calls, normalizeCommit_spec_of_height _ hM (generatorCommitVector fuel k M magnitude)
    (fun i ↦ Nat.size_le.mp (hs i)) hz⟩

end Compression
end LinearProgramming
end Optimization
end OAI
