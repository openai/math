import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignData
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignVotes

/-! # A first-order outer campaign driver

The suspended state stores the roster, weight and history arrays plus three integer
counters. A returned round is consumed exactly once. The outer loop preserves the
adaptive strategy for every trace of the recursive round computation.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

/-- The portion of the suspended state updated between rounds. -/
structure CampaignState where
  population : PackedPopulation
  seen : List PackedProbe
  positiveVotes : ℕ
deriving DecidableEq, Repr, Inhabited

/-- Public inputs, remaining iterations and the data-only state. -/
structure CampaignCursor where
  dimension : ℕ
  range : ℕ
  anchor : ℕ
  total : ℕ
  left : ℕ
  state : CampaignState
deriving DecidableEq, Repr, Inhabited

inductive CampaignBoundary where
  | needRound (population : PackedPopulation) (resume : CampaignCursor)
  | halt (positive : Bool)
deriving DecidableEq, Repr, Inhabited

def startCampaign (N R anchor trials : ℕ) : CampaignCursor :=
  ⟨N,R,anchor,trials,trials,⟨initialPopulation N R,[],0⟩⟩

/-- Control examines only whether all scheduled trials have returned. -/
def campaignBoundary (c : CampaignCursor) : CampaignBoundary :=
  if c.left = 0 then .halt (decide (c.total < 2*c.state.positiveVotes))
  else .needRound c.state.population c

def acceptRound (N R anchor : ℕ) (s : CampaignState) (round : PackedRound) : CampaignState :=
  let next := advancePacked N R s.population s.seen round
  ⟨next.1,next.2,s.positiveVotes + (if 0 < round.prices[anchor]?.getD 0 then 1 else 0)⟩

/-- Resume a suspended outer loop using the cached scores and the newly observed quotes. -/
def finishRound (c : CampaignCursor) (round : PackedRound) : CampaignCursor :=
  {c with left := c.left-1, state := acceptRound c.dimension c.range c.anchor c.state round}

def stateOf {N : ℕ} (p : Population N) (positive : ℕ) : CampaignState :=
  ⟨packPopulation p,p.probes.map packProbe,positive⟩

theorem acceptRound_eq {N : ℕ} (R : ℕ) (a : Fin N) (p : Population N) (positive : ℕ)
    (out : RoundResult N) :
    acceptRound N R a.val (stateOf p positive) (packRound p.experts.length out) =
      stateOf (p.advance (Learning.Pool.batch N R) out) (positive + vote a out) := by
  simp only [acceptRound, stateOf]
  rw [advancePacked_eq]
  simp [packRound, vote, a.isLt]

theorem startCampaign_state (N R a T : ℕ) :
    (startCampaign N R a T).state = stateOf (Population.start (Learning.Pool.batch N R)) 0 := by
  simp [startCampaign, stateOf, initialPopulation_eq, Population.start]

private def driveRounds {N : ℕ} (R anchor total : ℕ)
    (trial : PackedPopulation → Computation N PackedRound) : ℕ → CampaignState → Computation N Bool
  | 0, s => .pure (decide (total < 2*s.positiveVotes))
  | n+1, s => (trial s.population).bind fun out =>
    driveRounds R anchor total trial n (acceptRound N R anchor s out)

/-- Interpretation with the recursive trial as the only external computation.
No continuation or semantic function is stored in the suspended cursor. -/
def driveCampaign (c : CampaignCursor) (trial : PackedPopulation → Computation c.dimension PackedRound) :
    Computation c.dimension Bool :=
  driveRounds c.range c.anchor c.total trial c.left c.state

/-- One semantic step is exactly a halt, or one call followed by its data-only resume state. -/
theorem driveCampaign_eq (c : CampaignCursor) (trial : PackedPopulation → Computation c.dimension PackedRound) :
    driveCampaign c trial =
      if c.left = 0 then .pure (decide (c.total < 2*c.state.positiveVotes))
      else (trial c.state.population).bind fun out => driveCampaign (finishRound c out) trial := by
  rcases c with ⟨N,R,a,T,(_ | n),state⟩ <;> simp [driveCampaign, driveRounds, finishRound]

private theorem driveRounds_eq_stream {N : ℕ} (R total : ℕ) (a : Fin N)
    (trial : PackedPopulation → Computation N PackedRound)
    (typed : Population N → Computation N (RoundResult N))
    (actual : ∀ p, trial (packPopulation p) = (typed p).map (packRound p.experts.length))
    (left : ℕ) (p : Population N) (positive : ℕ) :
    driveRounds R a.val total trial left (stateOf p positive) =
      stream (Learning.Pool.batch N R) typed a total left p positive := by
  induction left generalizing p positive with
  | zero => rfl
  | succ n ih =>
    simp only [driveRounds, stream, stateOf, actual, Computation.map, Computation.bind_assoc,
      Computation.bind_pure]
    apply congrArg (Computation.bind (typed p))
    funext round
    exact (congrArg (driveRounds R a.val total trial n) (acceptRound_eq R a p positive round)).trans
      (ih _ _)

/-- Replacing a trial by the same computation on packed arrays preserves the exact
adaptive tree of the original campaign, including arbitrary inconsistent oracle replies. -/
theorem driveCampaign_eq_strategy {N : ℕ} (R T : ℕ) (a : Fin N) (markets : Campaign.AvailableMarkets N)
    (trial : PackedPopulation → Computation N PackedRound)
    (actual : ∀ p, trial (packPopulation p) =
      (Campaign.runRound R markets p).map (packRound p.experts.length)) :
    (driveCampaign (startCampaign N R a.val T) trial).toTree = Campaign.strategy R T a markets := by
  change (driveRounds R a.val T trial T (startCampaign N R a.val T).state).toTree = _
  rw [startCampaign_state, driveRounds_eq_stream R T a trial (Campaign.runRound R markets) actual,
    stream_eq_strategy]

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
