import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignFields
import OAI.Optimization.LinearProgramming.PriceGame.ControlWireCombined
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! Finite Boolean-stack program for the campaign/trial phase join. Stored continuations
are ordinary data, including both branches of a genuine price query. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Join

open ExactQuantumFactoring.BitStackProgram Procedure
open Wire

abbrev InnerAction := Trial.Action Trial.NodeInput Trial.Prepared PackedRound Trial.Completed PackedQuery
abbrev TrialGlobals := ℕ × (ℕ × List PackedExpert)
abbrev InputContext := ℕ × CampaignCursor
abbrev InnerReply := PackedQuery × (Trial.MachineState × Trial.MachineState)
abbrev OuterReply := PackedQuery × (Driver.PC × Driver.PC)

def globalsCode : TrialGlobals → List Bool := prodCode unaryCode (prodCode Nat.bits (listCode packedExpertCode))
def ctxCode : InputContext → List Bool := prodCode unaryCode campaignCursorCode
def innerReplyCode : InnerReply → List Bool := prodCode packedQueryCode (prodCode stateCode stateCode)
def outerReplyCode : OuterReply → List Bool := prodCode packedQueryCode (prodCode combinedCode combinedCode)

def innerView : InnerAction → (Trial.MachineState ⊕ (InnerReply ⊕ PackedRound))
  | .proceed s => .inl s
  | .ask q f t => .inr (.inl (q,f,t))
  | .halt out => .inr (.inr out)

def innerActionCode (a : InnerAction) : List Bool :=
  sumCode stateCode (sumCode innerReplyCode packedRoundCode) (innerView a)

def actionCode : Driver.Action → List Bool
  | .proceed s => false :: combinedCode s
  | .ask q f t => true :: false :: outerReplyCode (q,f,t)
  | .halt b => true :: true :: boolCode b

private noncomputable def leftValue {A B : Type} (ea : A → List Bool) (eb : B → List Bool) (d : A) :
    Procedure (sumCode ea eb) ea (Sum.elim id (fun _ => d)) := casesSum (identity ea) (constant eb ea d)
private noncomputable def rightValue {A B : Type} (ea : A → List Bool) (eb : B → List Bool) (d : B) :
    Procedure (sumCode ea eb) eb (Sum.elim (fun _ => d) id) := casesSum (constant ea eb d) (identity eb)
private noncomputable def tag {A B : Type} (ea : A → List Bool) (eb : B → List Bool) :
    Procedure (sumCode ea eb) boolCode (Sum.elim (fun _ => true) (fun _ => false)) :=
  casesSum (constant ea boolCode true) (constant eb boolCode false)

/-- Case analysis retains a separate public parameter in either branch. -/
noncomputable def contextCases {A B C D : Type} {ea : A → List Bool} {eb : B → List Bool}
    {ec : C → List Bool} {ed : D → List Bool} {f : C × A → D} {g : C × B → D}
    (da : A) (db : B) (p : Procedure (prodCode ec ea) ed f) (q : Procedure (prodCode ec eb) ed g) :
    Procedure (prodCode ec (sumCode ea eb)) ed (fun v =>
      match v.2 with | .inl a => f (v.1,a) | .inr b => g (v.1,b)) := by
  let c := first ec (sumCode ea eb)
  let t := second ec (sumCode ea eb)
  let yes := p.comp (c.pair ((leftValue ea eb da).comp t))
  let no := q.comp (c.pair ((rightValue ea eb db).comp t))
  exact (conditional ((tag ea eb).comp t) yes no).congrFun (by
    rintro ⟨c,a|b⟩ <;> rfl)

private noncomputable def trialPCP : Procedure (prodCode campaignCursorCode stateCode) combinedCode
    (fun v => Driver.PC.trial v.1 v.2) :=
  (prepend (prodCode campaignCursorCode stateCode) [true]).result (by intro _; rfl)
private noncomputable def campaignPCP : Procedure campaignCursorCode combinedCode Driver.PC.campaign :=
  (prepend campaignCursorCode [false]).result (by intro _; rfl)
private noncomputable def proceedP : Procedure combinedCode actionCode Driver.Action.proceed :=
  (prepend combinedCode [false]).result (by intro _; rfl)
private noncomputable def haltP : Procedure boolCode actionCode Driver.Action.halt :=
  (prepend boolCode [true,true]).result (by intro _; rfl)
private noncomputable def askP : Procedure outerReplyCode actionCode (fun v => Driver.Action.ask v.1 v.2.1 v.2.2) :=
  (prepend outerReplyCode [true,false]).result (by intro _; rfl)

/-- Convert a local trial action into a campaign control action. -/
def attach (finish : ℕ × (CampaignCursor × PackedRound) → CampaignCursor)
    (ctx : InputContext) : InnerAction → Driver.Action
  | .proceed s => .proceed (.trial ctx.2 s)
  | .ask q f t => .ask q (.trial ctx.2 f) (.trial ctx.2 t)
  | .halt out => .proceed (.campaign (finish (ctx.1,ctx.2,out)))

private def trialDefault : Trial.MachineState := Trial.initial 0 ⟨0,[],[]⟩
private def replyDefault : InnerReply := (default,trialDefault,trialDefault)

noncomputable def attachP {finish : ℕ × (CampaignCursor × PackedRound) → CampaignCursor}
    (endRound : Procedure (prodCode unaryCode (prodCode campaignCursorCode packedRoundCode))
      campaignCursorCode finish) :
    Procedure (prodCode ctxCode innerActionCode) actionCode (fun z => attach finish z.1 z.2) := by
  let c0 := (second unaryCode campaignCursorCode).comp (first ctxCode stateCode)
  let begin := proceedP.comp (trialPCP.comp (c0.pair (second ctxCode stateCode)))

  let c1 := (second unaryCode campaignCursorCode).comp (first ctxCode innerReplyCode)
  let r := second ctxCode innerReplyCode
  let q := (first packedQueryCode (prodCode stateCode stateCode)).comp r
  let ft := (second packedQueryCode (prodCode stateCode stateCode)).comp r
  let f := trialPCP.comp (c1.pair ((first stateCode stateCode).comp ft))
  let t := trialPCP.comp (c1.pair ((second stateCode stateCode).comp ft))
  let query := askP.comp (q.pair (f.pair t))

  let ctx := first ctxCode packedRoundCode
  let n := (first unaryCode campaignCursorCode).comp ctx
  let c2 := (second unaryCode campaignCursorCode).comp ctx
  let out := second ctxCode packedRoundCode
  let done := proceedP.comp (campaignPCP.comp (endRound.comp (n.pair (c2.pair out))))
  let tail := contextCases replyDefault (default : PackedRound) query done
  let choose := contextCases trialDefault (Sum.inr (default : PackedRound)) begin tail
  let view := fun z : InputContext × InnerAction => (z.1,innerView z.2)
  exact (choose.precompose view).congrFun (by rintro ⟨ctx,a⟩; cases a <;> rfl)

/-- Compute the source recursion depth from a binary dimension. At zero it is one. -/
noncomputable def depthP : Procedure Nat.bits Nat.bits States.Mass.depth := by
  let nbits := unaryToBits.comp (length.precompose Nat.bits)
  exact (conditional binaryZero (constant Nat.bits Nat.bits 1) nbits).congrFun (by
    intro n
    change (if decide (n = 0) then 1 else n.bits.length) = n.log2 + 1
    by_cases hz : n = 0
    · subst n; decide
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false, Nat.size_eq_bits_len]
      apply le_antisymm (Nat.size_le.mpr Nat.lt_log2_self)
      exact (Nat.log2_lt hz).mpr (Nat.lt_size_self n))

/-- The campaign entry pushes an empty trial stack with root weights in roster order. -/
noncomputable def beginTrialP :
    Procedure campaignCursorCode stateCode
      (fun c => Trial.initial (States.Mass.depth c.dimension) (Driver.rootInput c)) := by
  let weights := weightsP.comp (statePopulationP.comp stateP)
  let hcode := listCode (listCode ratCode)
  let raw := (constant campaignCursorCode Nat.bits 0).pair
    ((constant campaignCursorCode hcode []).pair weights)
  let root : Procedure campaignCursorCode nodeInputCode Driver.rootInput := raw.result (by intro _; rfl)
  let k := depthP.comp dimensionP
  let enter := (prepend (prodCode Nat.bits nodeInputCode) [false,false]).comp (k.pair root)
  let s := enter.pair (constant campaignCursorCode (listCode frameCode) [])
  exact s.result (by intro _; rfl)

private noncomputable def campaignStepP : Procedure campaignCursorCode actionCode
    (fun c => if c.left = 0 then .halt (decide (c.total < 2*c.state.positiveVotes)) else
      .proceed (.trial c (Trial.initial (States.Mass.depth c.dimension) (Driver.rootInput c)))) := by
  let h := (first boolCode boolCode).comp boundaryBitsP
  let vote := (second boolCode boolCode).comp boundaryBitsP
  let start := proceedP.comp (trialPCP.comp ((identity campaignCursorCode).pair beginTrialP))
  exact (conditional h (haltP.comp vote) start).congrFun (by intro c; simp [Function.comp_def])

abbrev InnerStep := TrialGlobals × Trial.MachineState → InnerAction
abbrev Finish := ℕ × (CampaignCursor × PackedRound) → CampaignCursor

/-- Total first-order phase dispatcher. `pad` is the explicit unary dimension budget;
bounded numeric primitives have defined behavior on malformed unreachable PCs. -/
def boundedStep (inner : InnerStep) (finish : Finish) (x : ℕ × Driver.PC) : Driver.Action :=
  match x.2 with
  | .campaign c => if c.left = 0 then .halt (decide (c.total < 2*c.state.positiveVotes)) else
      .proceed (.trial c (Trial.initial (States.Mass.depth c.dimension) (Driver.rootInput c)))
  | .trial c s => attach finish (x.1,c) (inner ((x.1,c.range,c.state.population.experts),s))

private def pcView : Driver.PC → CampaignCursor ⊕ (CampaignCursor × Trial.MachineState)
  | .campaign c => .inl c
  | .trial c s => .inr (c,s)

noncomputable def boundedStepP {inner : InnerStep} {finish : Finish}
    (innerP : Procedure (prodCode globalsCode stateCode) innerActionCode inner)
    (endRound : Procedure (prodCode unaryCode (prodCode campaignCursorCode packedRoundCode))
      campaignCursorCode finish) :
    Procedure (prodCode unaryCode combinedCode) actionCode (boundedStep inner finish) := by
  let cBranch := campaignStepP.comp (second unaryCode campaignCursorCode)
  let ts := prodCode campaignCursorCode stateCode
  let pad := first unaryCode ts
  let t := second unaryCode ts
  let c := (first campaignCursorCode stateCode).comp t
  let s := (second campaignCursorCode stateCode).comp t
  let range := rangeP.comp c
  let roster := rosterP.comp (statePopulationP.comp (stateP.comp c))
  let args := (pad.pair (range.pair roster)).pair s
  let trial := (attachP endRound).comp ((pad.pair c).pair (innerP.comp args))
  let join := contextCases (default : CampaignCursor) ((default : CampaignCursor),trialDefault) cBranch trial
  let raw := join.precompose (fun z : ℕ × Driver.PC => (z.1,pcView z.2))
  apply (raw.congrEncoding (ec := prodCode unaryCode combinedCode) (ed := actionCode)
    (by rintro ⟨n,pc⟩; cases pc <;> rfl) (by intro a; rfl)).congrFun
  rintro ⟨n,pc⟩; cases pc <;> rfl

/-- Its proof obligations concern only the numeric primitives taken on this path. -/
theorem boundedStep_refines (inner : InnerStep) (finish : Finish) (n : ℕ) (pc : Driver.PC)
    (hn : ∀ c s, pc = .trial c s →
      inner ((n,c.range,c.state.population.experts),s) =
      Trial.stepPacket c.dimension c.range Moment.probes c.state.population.experts s)
    (hf : ∀ c s out, pc = .trial c s →
      Trial.stepPacket c.dimension c.range Moment.probes c.state.population.experts s = .halt out →
      finish (n,c,out) = finishRound c out) :
    boundedStep inner finish (n,pc) = Driver.step pc := by
  cases pc with
  | campaign c => simp [boundedStep, Driver.step, campaignBoundary]; split <;> rfl
  | trial c s =>
    simp only [boundedStep, Driver.step, hn _ _ rfl]
    cases h : Trial.stepPacket c.dimension c.range Moment.probes c.state.population.experts s with
    | proceed t => rfl
    | ask q f t => rfl
    | halt out => simp [attach, hf _ _ _ rfl h]

end Join
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
