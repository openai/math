import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSourceGuarded

/-! A local-to-global equivalence criterion for total, polynomially bounded phase
implementations on the reachable numeric packets of the actual trial. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States.Mass Moment TrialExecution

variable {N ne r R : ℕ} {experts : Fin ne → Expert N}
abbrev ConcreteKernel := Kernel NodeInput Prepared PackedRound Completed PackedQuery

structure LiveKernelRefinement (r R : ℕ) (experts : Fin ne → Expert N) (alt : ConcreteKernel) where
  leaf : ∀ c : SourceNode N ne, c.level ≤ depth N → alt.leaf c.input = (fixedKernel R r experts).leaf c.input
  prepare : ∀ {k j} (c : SourceNode N ne), c.level+(k+1) ≤ depth N → j < 2*r →
    ∀ p : SeenPrefix r R experts c k j, alt.prepare c.input (c.rows p.calls.val) = c.prepared R experts p.calls.val
  descend : ∀ i prep, alt.childInput i prep = (fixedKernel R r experts).childInput i prep
  assemble : ∀ {k} (c : SourceNode N ne) (p : SeenPrefix r R experts c k (2*r)),
    alt.assemble c.input (c.rows p.calls.val) = (fixedKernel R r experts).assemble c.input (c.rows p.calls.val)
  finish : ∀ {k j} (c : SourceNode N ne) (p : SeenPrefix r R experts c k j)
    {tr ch}, Emits ((c.next experts p.calls.val).exec r R experts k) tr ch → ∀ tape,
      alt.finish c.input (c.rows p.calls.val) (c.prepared R experts p.calls.val) (codeOutput ch.val) tape =
      (fixedKernel R r experts).finish c.input (c.rows p.calls.val) (c.prepared R experts p.calls.val) (codeOutput ch.val) tape

def CounterAgrees (alt ref : ConcreteKernel) (calls : ℕ) (pc : PC NodeInput Prepared PackedRound Completed) : Prop :=
  ∀ stack, step alt calls ⟨pc,stack⟩ = step ref calls ⟨pc,stack⟩

theorem counterAgrees_returned (a b : ConcreteKernel) (n : ℕ) (o : PackedRound) :
    CounterAgrees a b n (.returned o) := by intro s; cases s <;> rfl

def LiveKernelRefinement.marks {alt : ConcreteKernel} (h : LiveKernelRefinement r R experts alt) :
    SourceMarks r R experts (CounterAgrees alt (fixedKernel R r experts) (2*r)) (fun _ => True) where
  NodeGood := fun k c => c.level+k ≤ depth N
  enter := by
    intro k c depthBound stack
    cases k with
    | zero =>
      change Action.proceed ⟨.returned (alt.leaf c.input),stack⟩ = _
      rw [h.leaf c (by omega)]
      rfl
    | succ => rfl
  leaf := fun _ => counterAgrees_returned alt (fixedKernel R r experts) (2*r) _
  schedule := by
    intro k c j hdepth hj pref stack
    generalize hrem : 2*r-j = rem
    cases rem with
    | zero =>
      have heq : j=2*r := by omega
      subst j
      change Action.proceed ⟨.returned (alt.assemble c.input (c.rows pref.calls.val)),stack⟩ = _
      rw [h.assemble c pref]
      rfl
    | succ rem =>
      have strict : j < 2*r := by omega
      change (let p := alt.prepare c.input (c.rows pref.calls.val)
        Action.proceed ⟨.enter k (alt.childInput c.input p),⟨k,rem,c.input,c.rows pref.calls.val,p⟩ :: stack⟩) = _
      rw [h.prepare c hdepth strict pref]
      dsimp only
      rw [h.descend c.input (c.prepared R experts pref.calls.val)]
      rfl
  frame := fun _ _ _ => True.intro
  child := by
    intro k c j hdepth hj p
    change c.level+1+k ≤ depth N
    omega
  feedback := by
    intro k c j hdepth hj p tr ch received tape stack
    simp only [step,SourceNode.frame,h.finish c p received tape]
  assembled := fun _ _ => counterAgrees_returned alt (fixedKernel R r experts) (2*r) _

theorem LiveKernelRefinement.guarded {alt : ConcreteKernel} (h : LiveKernelRefinement probes R experts alt)
    (w : Weights ne) (hw : ∀ i, 0 ≤ w i) {tr out}
    (emits : Emits (run R experts (marketSolverAtCommonWeightUnit experts) w hw) tr out) :
    let ref := packetKernel feedbackPrefix N R probes (List.ofFn (fun e => packExpert (experts e)))
    ∃ stop, GuardedSteps (fun s => step alt (2*probes) s = step ref (2*probes) s) ref (2*probes)
      (initial (depth N) (codeInput (N:=N) 0 (fun _ _ => 0) w)) tr
      (nodeTicks (2*probes) (depth N)+tr.length) stop ∧ step ref (2*probes) stop = .halt (codeOutput out.val) := by
  have good : h.marks.NodeGood (depth N) (SourceNode.initial N w hw) := by
    change 0+depth N ≤ depth N
    simp
  obtain ⟨stop,steps,hout⟩ := h.marks.rootGuarded w hw good emits
  refine ⟨stop,steps.weaken ?_,hout⟩
  intro s ok
  have eq := ok.1 s.stack
  simpa only [packetKernel,List.length_ofFn] using eq

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
