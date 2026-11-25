import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaign
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialMachine

/-! # The combined data-only campaign and recursive trial program counter -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

/-- A root round in progress retains both the suspended outer loop and the explicit
recursive stack. No continuations or user functions occur in this datatype. -/
inductive PC where
  | campaign (outer : CampaignCursor)
  | trial (outer : CampaignCursor) (inner : Trial.MachineState)

inductive Action where
  | proceed (s : PC)
  | ask (query : PackedQuery) (ifFalse ifTrue : PC)
  | halt (positive : Bool)

def rootInput (c : CampaignCursor) : Trial.NodeInput := ⟨0,[],c.state.population.weights⟩

def kernel (c : CampaignCursor) :=
  Trial.packetKernel feedbackPrefix c.dimension c.range Moment.probes c.state.population.experts

/-- The only external nonhalting instruction requests one designated price label. -/
def step : PC → Action
  | .campaign c =>
    match campaignBoundary c with
    | .halt b => .halt b
    | .needRound _ resume =>
      .proceed (.trial resume (Trial.initial (States.Mass.depth resume.dimension) (rootInput resume)))
  | .trial c s =>
    match Trial.stepPacket c.dimension c.range Moment.probes c.state.population.experts s with
    | .proceed t => .proceed (.trial c t)
    | .ask q f t => .ask q (.trial c f) (.trial c t)
    | .halt out => .proceed (.campaign (finishRound c out))

/-- Observable boundary of a finite segment of internal control instructions. -/
inductive Boundary where
  | query (q : PackedQuery) (ifFalse ifTrue : PC)
  | halt (positive : Bool)

def poll : ℕ → PC → Option Boundary
  | 0, _ => none
  | n+1, s => match step s with
    | .proceed t => poll n t
    | .ask q f t => some (.query q f t)
    | .halt b => some (.halt b)

inductive Steps : PC → List (PackedQuery × Bool) → ℕ → PC → Prop where
  | refl (s) : Steps s [] 0 s
  | silent {s t u tr n} (h : step s = .proceed t) (rest : Steps t tr n u) :
      Steps s tr (n+1) u
  | answer {s f t u tr n q} (b : Bool) (h : step s = .ask q f t)
      (rest : Steps (if b then t else f) tr n u) : Steps s ((q,b)::tr) (n+1) u

theorem Steps.trans {p q r tr tr' n n'} (a : Steps p tr n q) (b : Steps q tr' n' r) :
    Steps p (tr ++ tr') (n+n') r := by
  induction a with
  | refl => simpa using b
  | silent h _ ih => simpa [Nat.succ_add] using Steps.silent h (ih b)
  | answer bit h _ ih => simpa [Nat.succ_add] using Steps.answer bit h (ih b)

theorem Steps.of_trial (c : CampaignCursor) {p q tr n}
    (s : Trial.Steps (kernel c) (2*Moment.probes) p tr n q) :
    Steps (.trial c p) tr n (.trial c q) := by
  induction s with
  | refl => exact .refl _
  | silent h _ ih =>
    apply Steps.silent _ ih
    change (match Trial.step (kernel c) (2*Moment.probes) _ with
      | .proceed t => Action.proceed (.trial c t)
      | .ask q f t => .ask q (.trial c f) (.trial c t)
      | .halt out => .proceed (.campaign (finishRound c out))) = _
    rw [h]
  | answer b h _ ih =>
    apply Steps.answer b
    · change (match Trial.step (kernel c) (2*Moment.probes) _ with
        | .proceed t => Action.proceed (.trial c t)
        | .ask q f t => .ask q (.trial c f) (.trial c t)
        | .halt out => .proceed (.campaign (finishRound c out))) = _
      rw [h]
    · cases b <;> exact ih

/-- The two extra internal instructions enter the recursive trial and then consume
its completed packed round. All external queries are exactly the child transcript. -/
theorem one_round {c : CampaignCursor} (hc : 0 < c.left) {tr round}
    (eval : Trial.Evaluates (kernel c) (2*Moment.probes)
      (.node (States.Mass.depth c.dimension) (rootInput c)) tr round) :
    Steps (.campaign c) tr (Trial.nodeTicks (2*Moment.probes) (States.Mass.depth c.dimension) + tr.length + 2)
      (.campaign (finishRound c round)) := by
  obtain ⟨endState, inside, done⟩ := eval.halts
  have enter : step (.campaign c) = .proceed (.trial c
      (Trial.initial (States.Mass.depth c.dimension) (rootInput c))) := by
    simp [step, campaignBoundary, Nat.ne_of_gt hc]
  have finish : step (.trial c endState) = .proceed (.campaign (finishRound c round)) := by
    change (match Trial.step (kernel c) (2*Moment.probes) endState with
      | .proceed t => Action.proceed (.trial c t)
      | .ask q f t => .ask q (.trial c f) (.trial c t)
      | .halt out => .proceed (.campaign (finishRound c out))) = _
    rw [done]
  have ret := Steps.silent finish (Steps.refl _)
  simpa using Steps.silent enter ((Steps.of_trial c inside).trans ret)

/-- A whole campaign branch is a chronological sequence of genuine trial branches.
This semantic proof object never enters the runtime state. -/
inductive Complete : CampaignCursor → List (PackedQuery × Bool) → CampaignCursor → Prop where
  | finish (c : CampaignCursor) (h : c.left = 0) : Complete c [] c
  | round {c last out before after} (h : 0 < c.left)
      (trial : Trial.Evaluates (kernel c) (2*Moment.probes)
        (.node (States.Mass.depth c.dimension) (rootInput c)) before out)
      (later : Complete (finishRound c out) after last) : Complete c (before++after) last

theorem Complete.steps {c last tr} (run : Complete c tr last) :
    Steps (.campaign c) tr (c.left*(Trial.nodeTicks (2*Moment.probes) (States.Mass.depth c.dimension) + 2)
      + tr.length) (.campaign last) := by
  induction run with
  | finish c h => simpa [h] using Steps.refl (.campaign c)
  | @round c last out before after hc trial later ih =>
    have both := (one_round hc trial).trans ih
    have cut : c.left = (c.left-1)+1 := by omega
    convert both using 1
    simp only [finishRound, List.length_append]
    nth_rw 1 [cut]
    rw [Nat.succ_mul]
    omega

theorem Complete.final {c last tr} (h : Complete c tr last) :
    step (.campaign last) = .halt (decide (last.total < 2 * last.state.positiveVotes)) := by
  induction h with
  | finish c hc => simp [step,campaignBoundary,hc]
  | round _ _ _ ih => exact ih

def visibleFirst (tr : List (PackedQuery × Bool)) (bit : Bool) (event : Boundary) : Prop :=
  match tr with
  | [] => event = .halt bit
  | (q,_) :: _ => ∃ f g, event = .query q f g

/-- Once a closed execution has been established, the public step budget suffices to
reach its first real query or its actual final bit, without a spurious fuel failure. -/
theorem Steps.first_boundary {s t tr ticks} (run : Steps s tr ticks t) {bit : Bool}
    (done : step t = .halt bit) :
    ∃ event, poll (ticks+1) s = some event ∧ visibleFirst tr bit event := by
  induction run with
  | refl s => exact ⟨_,by simp [poll,done],rfl⟩
  | silent h _ ih =>
    obtain ⟨event,he,agree⟩ := ih done
    exact ⟨event,by simpa [poll,h] using he,agree⟩
  | @answer s f t u tr n q b h rest ih => exact ⟨.query q f t,by simp [poll,h],f,t,rfl⟩

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
