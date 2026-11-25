import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSourceMarks
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialMarkedSchedule

/-! Compile local facts about real source packets into an invariant of every
word-level instruction of the physical recursive stack, on all reply histories. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States.Mass Moment TrialExecution

variable {N ne r R : ℕ} {experts : Fin ne → Expert N}
    {pcOK : PC NodeInput Prepared PackedRound Completed → Prop}
    {frameOK : Frame NodeInput Prepared Completed → Prop}

theorem SourceMarks.marked (m : SourceMarks r R experts pcOK frameOK) (k : ℕ) :
    ∀ (c : SourceNode N ne), m.NodeGood k c → ∀ {tr out}, Emits (c.exec r R experts k) tr out →
      MarkedEvaluates pcOK frameOK (fixedKernel R r experts) (2*r)
        (.node k c.input) tr (codeOutput out.val) := by
  induction k with
  | zero =>
    intro c good tr out e
    cases e
    rw [← leafPacket_spec r R c.level c.history c.weights]
    exact .leaf c.input (m.enter good) (m.leaf good)
  | succ k ih =>
    intro c good tr out e
    change Emits ((c.schedule r R experts k (2*r)).map (assemble experts c.history c.weights)) tr out at e
    obtain ⟨xs,hs,rfl⟩ := e.map_inv
    apply MarkedEvaluates.node (m.enter good)
    rw [← assemblePacket_spec experts c.history c.weights xs]
    let ops := fixedKernel R r experts
    let v := fun (j : ℕ) (ys : Fin j → Call N ne r c.level) (a : Call N ne r c.level) =>
      StepOK experts c.weights ys a
    let act := c.stepAt r R experts k
    let s := scheduleTrace_of_emits v act (2*r) hs
    have localStep (j rem : ℕ) (full : j+rem+1 = 2*r) (ys : Schedule v j) (pre : List (PackedQuery × Bool))
        (seen : Emits (runSchedule v act j) pre ys) (a : {a // v j ys.val a}) (t : List (PackedQuery × Bool))
        (one : Emits (act j ys.val) t a) :
        MarkedRefinesStep pcOK frameOK ops (2*r) k rem c.input (c.rows ys.val) t (codeCall a.val) := by
      let p : SeenPrefix r R experts c k j := ⟨ys,pre,seen⟩
      have hj : j < 2*r := by omega
      have hrem : 2*r-(j+1) = rem := by omega
      have hstep : 2*r-j = rem+1 := by omega
      obtain ⟨left,mid,ch,rfl,child,feedback⟩ := c.split R experts k ys.val one
      refine ⟨left,mid,codeOutput ch.val,rfl,?_,?_,?_,?_,feedback⟩
      · simpa only [hstep] using m.schedule good hj.le p
      · simpa only [hrem,p,SourceNode.frame,SourceNode.prepared,ops] using m.frame good hj p
      · simpa only [hrem,p,SourceNode.frame,SourceNode.prepared,ops] using m.feedback good hj p child
      · change MarkedEvaluates pcOK frameOK (fixedKernel R r experts) (2*r)
          (.node k ((fixedKernel R r experts).childInput c.input (c.prepared R experts ys.val))) left
          (codeOutput ch.val)
        rw [c.childInput_eq R experts ys.val]
        exact ih (c.next experts ys.val) (m.child good hj p) child
    let p : SeenPrefix r R experts c k (2*r) := ⟨xs,tr,hs⟩
    have sOK := m.schedule good (Nat.le_refl (2*r)) p
    have done : MarkedEvaluates pcOK frameOK ops (2*r) (.rounds k 0 c.input (c.rows xs.val)) []
        (ops.assemble c.input (c.rows xs.val)) :=
      .done _ _ _ (by simpa only [Nat.sub_self] using sOK) (m.assembled good p)
    have total := s.prependMarked pcOK frameOK ops (2*r) k c.input codeCall localStep
      (rem:=0) (by omega) done
    simpa only [Nat.add_zero,List.append_nil,ops,SourceNode.input,SourceNode.rows,fixedKernel,packetKernelSized]
      using total

/-- Principal typed interface for carrying packet invariants through the actual raw
trial stack, including all intermediate pushes, commits, replies and the halt. -/
theorem SourceMarks.rootGuarded {experts : Fin ne → Expert N}
    (m : SourceMarks probes R experts pcOK frameOK) (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    (rootOK : m.NodeGood (depth N) (SourceNode.initial N w hw)) {tr out}
    (e : Emits (run R experts (marketSolverAtCommonWeightUnit experts) w hw) tr out) :
    let roster := List.ofFn fun e => packExpert (experts e)
    let ops := packetKernel feedbackPrefix N R probes roster
    let guard := fun s : MachineState => pcOK s.pc ∧ ∀ f ∈ s.stack, frameOK f
    ∃ stop, GuardedSteps guard ops (2*probes)
      (initial (depth N) (codeInput (N:=N) 0 (fun _ _ => 0) w)) tr
      (nodeTicks (2*probes) (depth N) + tr.length) stop ∧
      step ops (2*probes) stop = .halt (codeOutput out.val) := by
  simp only [packetKernel,List.length_ofFn]
  have mrun := m.marked (depth N) (SourceNode.initial N w hw) rootOK e
  exact ⟨⟨.returned (codeOutput out.val),[]⟩,mrun.guardedSteps [] (by simp),rfl⟩

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
