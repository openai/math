import OAI.Optimization.LinearProgramming.PriceGame.Campaign

/-! # The outer price-game campaign as a streaming vote count

Only the number of positive anchor votes is needed at termination. The identity
with the adaptive trial strategy holds for every actual returned round, including
rounds arising from inconsistent oracle replies.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control


variable {N : ℕ}

def vote (anchor : Fin N) (out : RoundResult N) : ℕ :=
  if 0 < out.prices anchor then 1 else 0

def votes {T : ℕ} (anchor : Fin N) (out : Fin T → RoundResult N) : ℕ :=
  ∑ t, vote anchor (out t)

theorem votes_cons {T : ℕ} (anchor : Fin N) (a : RoundResult N) (out : Fin T → RoundResult N) :
    votes anchor (Fin.cons a out) = vote anchor a + votes anchor out := by
  simp [votes, Fin.sum_univ_succ]

theorem majority_votes {T : ℕ} (anchor : Fin N) (out : Fin T → RoundResult N) :
    priceMajority (fun t => (out t).prices anchor) = decide (T < 2 * votes anchor out) := by
  simp [priceMajority, votes, vote]

/-- Streaming execution of the outer loop. The recursive trial computation and inputs
are identical to those in the campaign; the outer loop keeps a natural vote counter. -/
def stream (candidates : List (Probe N) → List (Expert N)) (trial : Population N → Computation N (RoundResult N))
    (anchor : Fin N) (total : ℕ) : (left : ℕ) → Population N → ℕ → Computation N Bool
  | 0, _, positive => .pure (decide (total < 2*positive))
  | left+1, p, positive => (trial p).bind fun round =>
    stream candidates trial anchor total left (p.advance candidates round) (positive + vote anchor round)

theorem stream_eq_trials (candidates : List (Probe N) → List (Expert N))
    (trial : Population N → Computation N (RoundResult N)) (anchor : Fin N)
    (total left : ℕ) (p : Population N) (positive : ℕ) :
    stream candidates trial anchor total left p positive =
    (trialLoop candidates trial left p).map fun rounds => decide (total < 2*(positive + votes anchor rounds)) := by
  induction left generalizing p positive with
  | zero => simp [stream, trialLoop, Computation.map, votes]
  | succ left ih =>
    simp only [stream, trialLoop, Computation.map, Computation.bind_assoc, Computation.bind_pure]
    apply congrArg (Computation.bind (trial p))
    funext round
    rw [ih]
    unfold Computation.map
    apply congrArg (Computation.bind _)
    funext tail
    simp only [votes_cons, Nat.add_assoc]

theorem stream_eq_strategy (R T : ℕ) (anchor : Fin N) (markets : Campaign.AvailableMarkets N) :
    (stream (Learning.Pool.batch N R) (Campaign.runRound R markets) anchor T T
      (.start (Learning.Pool.batch N R)) 0).toTree = Campaign.strategy R T anchor markets := by
  unfold Campaign.strategy trialStrategy
  rw [stream_eq_trials]
  simp [majority_votes]

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
