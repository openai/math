import OAI.Computability.BorderVNP.ParseBatchVerifierCountArithmetic
import OAI.Computability.BorderVNP.ParseBatchVerifierCountRanks

/-! # Recovering occurrence counts from all sorted marker ranks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchCounts

/-- When the ranks are the true positions of the sorted end markers, their arithmetic
equations determine the histogram uniquely, including keys with no occurrences. -/
theorem rankEquations_markerRank_iff {U : Type*} [Fintype U] {k : ℕ}
    (label : U → Fin k) (count : Fin k → ℕ) :
    RankEquations (markerRank label) count ↔ count = useCount label := by
  cases k with
  | zero =>
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ i => i.elim0⟩
  | succ k =>
    rw [rankEquations_succ_iff]
    simp only [markerRank_zero, markerRank_succ, Nat.add_left_cancel_iff]
    constructor
    · rintro ⟨h₀, hs⟩
      funext i
      exact Fin.cases h₀.symm (fun j => (hs j).symm) i
    · rintro rfl
      exact ⟨rfl, fun _ => rfl⟩

end ParseBatchCounts

end BorderVNP
end Computability
end OAI
