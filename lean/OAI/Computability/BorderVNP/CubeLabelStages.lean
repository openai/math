import OAI.Computability.BorderVNP.CubeMeanExact

/-! # Forward stages of the public sparse-label minimizer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open Cube Cube.MeanChoice Finset

/-- The cells already visited by the native ascending loop. -/
def cellsBefore (n k : ℕ) : Finset (Fin n) := univ.filter fun c => c.val < k

/-- The numeric labels after the first `k` cells have been pinned. -/
def stage {n : ℕ} {I : Type*} [Fintype I] (rows : I → Traffic (Fin n)) (z : ℕ) : ℕ → Fin n → Fin (z+1)
  | 0 => fun _ => 0
  | k+1 => let x := stage rows z k
           if h : k < n then Function.update x ⟨k,h⟩ (firstMinimum (scoreNat rows (cellsBefore n k) x ⟨k,h⟩))
           else x

/-- Extending the assigned prefix inserts exactly its next cell. -/
theorem cellsBefore_succ {n k : ℕ} (h : k < n) : cellsBefore n (k+1) = insert ⟨k,h⟩ (cellsBefore n k) := by
  ext c
  simp [cellsBefore,Fin.ext_iff]; omega

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
