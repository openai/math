import OAI.Hierarchy.TaggedWirePathCore
import OAI.Hierarchy.TaggedWireHistogramBranches

namespace OAI
/-! # Completing a chronological prefix with explicit histograms -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical
variable {X : Type} {W q d : ℕ} {C : Chart W q d}

/-- Use the first letter once for every copy. A zero-copy row also has a
canonical histogram when its alphabet is empty. -/
def firstBallChoices {n : ℕ} (letters copies : Fin n → ℕ)
    (positive : ∀ i, 0 < copies i → 0 < letters i) : BallChoices letters copies :=
  fun i => histogram (fun j : Fin (copies i) => (⟨0, positive i (Nat.zero_lt_of_lt j.isLt)⟩ : Fin (letters i)))

theorem HistogramFormat.continuation (D : HistogramFormat C X) (events : List Event) (start : X)
    (positive : ∀ {a : Attempt} {tail : List Event} {x : X},
      Prefix D.slot events start (.attempt a :: tail) x → ∀ i, 0 < D.copies a x i → 0 < D.letters a x i)
    {tail : List Event} {x : X} (reached : Prefix D.slot events start tail x) :
    Nonempty (Path D.slot tail x) := by
  apply Prefix.nonempty_path D.slot events start _ reached
  intro e rest state hist
  cases e with
  | attempt a => exact ⟨firstBallChoices _ _ (positive hist)⟩
  | feed b => exact ⟨()⟩

end Hierarchy.WireTelescope.CalendarTape
end

end OAI
