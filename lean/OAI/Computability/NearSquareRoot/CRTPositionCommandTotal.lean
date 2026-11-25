import OAI.Computability.NearSquareRoot.CRTPositionCommand
import OAI.Computability.NearSquareRoot.CRTPositionFourCommandTotal
import OAI.Computability.NearSquareRoot.CRTPositionFourCommandCutoffRaw
import OAI.Computability.NearSquareRoot.FixedCandidateBoxCutoff

/-! # Correctness of every candidate position permutation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Adic IntegerMultiplication.Loom PositionRows
noncomputable section

theorem position_raw_from_cutoff {core : Cmd} (group : RowCommand.RawGroupedRuns core)
    (K a b : ℕ) (cut : ∀ k, K < k → payloadBits a k+payloadBits b k ≤ k/2-2)
    {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
    (pos : ∀ i, 0 < (u i).count) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead) :
    SomeTime (positionCmd K a b core) (fun i => .fork (send (Reflections.table (p i)))
      (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  let data := cloth (fun i => line 2 (k i)) u f
  let out := cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))
  apply cutoff_raw K k p data out
  · exact large_raw_runs group a b (fun i : {i // K<k i} => k i.1) (fun i => u i.1)
      (fun i => pos i.1) (fun i => p i.1) (fun i => f i.1) (fun i => cut _ i.2)
  · let run := small_cloth_runs K (fun i : {i // k i ≤ K} => k i.1) (fun i => (u i.1).count)
      (fun i => u i.1) (fun i => p i.1) (fun i => f i.1) (fun i => i.2) (fun i => pos i.1)
      (fun _ => le_rfl)
    exact ⟨_,run.withoutSpace⟩

/-- The primitive-recursive cutoff makes every guessed pair of reserve
degrees geometrically valid. Only the fast clock depends on those degrees. -/
theorem position_raw_runs {core : Cmd} (group : RowCommand.RawGroupedRuns core) (a b : ℕ)
    {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
    (pos : ∀ i, 0 < (u i).count) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead) :
    ∃ t, EffectiveTask.Runs (positionCmd (FixedCandidate.boxCutoff a b) a b core) t
      (fun i => .fork (send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) :=
  position_raw_from_cutoff group _ a b (fun _ h => FixedCandidate.position_reserves_of_cutoff h.le)
    k u pos p f

end
end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
