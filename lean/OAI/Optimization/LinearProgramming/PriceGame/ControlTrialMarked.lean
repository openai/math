import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialGuarded

/-! Attach data invariants to the recursive call semantics and preserve them at every
intermediate first-order program counter, including the reply replay phases. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

universe u
variable {I P R C Q : Type u}

inductive MarkedEvaluates (pcOK : PC I P R C → Prop) (frameOK : Frame I P C → Prop)
    (ops : Kernel I P R C Q) (calls : ℕ) : Work I C → List (Q × Bool) → R → Prop where
  | leaf (i : I) (start : pcOK (.enter 0 i)) (stop : pcOK (.returned (ops.leaf i))) :
      MarkedEvaluates pcOK frameOK ops calls (.node 0 i) [] (ops.leaf i)
  | node {k i tr out} (start : pcOK (.enter (k+1) i))
      (scheduled : MarkedEvaluates pcOK frameOK ops calls (.rounds k calls i []) tr out) :
      MarkedEvaluates pcOK frameOK ops calls (.node (k+1) i) tr out
  | done (k : ℕ) (i : I) (xs : List C) (start : pcOK (.schedule k 0 i xs))
      (stop : pcOK (.returned (ops.assemble i xs))) :
      MarkedEvaluates pcOK frameOK ops calls (.rounds k 0 i xs) [] (ops.assemble i xs)
  | call {k rem i xs left middle right out row result} (start : pcOK (.schedule k (rem+1) i xs))
      (saved : frameOK ⟨k,rem,i,xs,ops.prepare i xs⟩)
      (waiting : ∀ tape, pcOK (.feedback ⟨k,rem,i,xs,ops.prepare i xs⟩ out tape))
      (child : MarkedEvaluates pcOK frameOK ops calls
        (.node k (ops.childInput i (ops.prepare i xs))) left out)
      (feedback : Scan (ops.finish i xs (ops.prepare i xs) out) [] middle row)
      (rest : MarkedEvaluates pcOK frameOK ops calls (.rounds k rem i (xs++[row])) right result) :
      MarkedEvaluates pcOK frameOK ops calls (.rounds k (rem+1) i xs) (left++middle++right) result

variable {pcOK : PC I P R C → Prop} {frameOK : Frame I P C → Prop}
    {ops : Kernel I P R C Q} {calls : ℕ} {w : Work I C} {tr : List (Q × Bool)} {out : R}

theorem MarkedEvaluates.start (h : MarkedEvaluates pcOK frameOK ops calls w tr out) : pcOK w.pc := by
  cases h with
  | leaf _ first _ => exact first
  | node first _ => exact first
  | done _ _ _ first _ => exact first
  | call first _ _ _ _ _ => exact first

theorem MarkedEvaluates.stop (h : MarkedEvaluates pcOK frameOK ops calls w tr out) :
    pcOK (.returned out) := by
  induction h with
  | leaf _ _ last => exact last
  | node _ _ ih => exact ih
  | done _ _ _ _ last => exact last
  | call _ _ _ _ _ _ _ ih => exact ih

theorem MarkedEvaluates.forget (h : MarkedEvaluates pcOK frameOK ops calls w tr out) :
    Evaluates ops calls w tr out := by
  induction h with
  | leaf i _ _ => exact .leaf i
  | node _ _ ih => exact .node ih
  | done k i xs _ _ => exact .done k i xs
  | call _ _ _ _ scan _ child rest => exact .call child scan rest

private abbrev Whole (pcOK : PC I P R C → Prop) (frameOK : Frame I P C → Prop)
    (s : State I P R C) := pcOK s.pc ∧ ∀ f ∈ s.stack, frameOK f

private theorem Scan.markedSteps (calls : ℕ) (f : Frame I P C) (out : R)
    (stack : List (Frame I P C)) {t tr c}
    (scan : Scan (ops.finish f.input f.prefix f.prepared out) t tr c)
    (hst : ∀ x ∈ stack, frameOK x) (wait : ∀ tape, pcOK (.feedback f out tape))
    (done : pcOK (.schedule f.childFuel f.remaining f.input (f.prefix++[c]))) :
    GuardedSteps (Whole pcOK frameOK) ops calls ⟨.feedback f out t,stack⟩ tr (tr.length+1)
      ⟨.schedule f.childFuel f.remaining f.input (f.prefix++[c]),stack⟩ := by
  induction scan with
  | @done t c hc =>
    exact .silent ⟨wait t,hst⟩ (by simp [step,hc]) (.refl _ ⟨done,hst⟩)
  | @ask t q tr c a hq _ ih =>
    have hstep : step ops calls ⟨.feedback f out t,stack⟩ = .ask q
        ⟨.feedback f out (t++[false]),stack⟩ ⟨.feedback f out (t++[true]),stack⟩ := by
      simp [step,hq]
    cases a <;> exact .answer _ ⟨wait t,hst⟩ hstep (ih done)

/-- The schedule marks cover every state of the actual stack execution, and the
number of small steps and the complete chronological oracle transcript are preserved. -/
theorem MarkedEvaluates.guardedSteps (eval : MarkedEvaluates pcOK frameOK ops calls w tr out)
    (stack : List (Frame I P C)) (hst : ∀ f ∈ stack, frameOK f) :
    GuardedSteps (fun s => pcOK s.pc ∧ ∀ f ∈ s.stack, frameOK f) ops calls
      ⟨w.pc,stack⟩ tr (w.ticks calls + tr.length) ⟨.returned out,stack⟩ := by
  induction eval generalizing stack with
  | leaf i first last => exact .silent ⟨first,hst⟩ rfl (.refl _ ⟨last,hst⟩)
  | done k i xs first last =>
    have hs : step ops calls ⟨.schedule k 0 i xs,stack⟩ =
        .proceed ⟨.returned (ops.assemble i xs),stack⟩ := rfl
    have run := GuardedSteps.silent (guard := Whole pcOK frameOK) ⟨first,hst⟩ hs
      (.refl _ ⟨last,hst⟩)
    simpa only [Work.pc, Work.ticks, Nat.zero_mul, Nat.add_zero, List.length_nil] using run
  | @node k i tr out first scheduled ih =>
    have total := GuardedSteps.silent (guard := Whole pcOK frameOK) ⟨first,hst⟩
      (show step ops calls ⟨.enter (k+1) i,stack⟩ = .proceed ⟨.schedule k calls i [],stack⟩ from rfl)
      (ih stack hst)
    convert total using 1
    all_goals simp only [Work.pc,Work.ticks,nodeTicks]
    all_goals omega
  | @call k rem i xs left middle right out row result first saved waiting child feedback rest ihChild ihRest =>
    let f : Frame I P C := ⟨k,rem,i,xs,ops.prepare i xs⟩
    have stackSafe : ∀ g ∈ f :: stack, frameOK g := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact saved
      · exact hst _ hg
    have feedbackSteps := feedback.markedSteps (ops := ops) calls f out stack hst waiting rest.start
    have ret := GuardedSteps.silent (guard := Whole pcOK frameOK) ⟨child.stop,stackSafe⟩
      (show step ops calls ⟨.returned out,f::stack⟩ = .proceed ⟨.feedback f out [],stack⟩ from rfl)
      feedbackSteps
    have seq := ((ihChild (f::stack) stackSafe).trans ret).trans (ihRest stack hst)
    have start := GuardedSteps.silent (guard := Whole pcOK frameOK) ⟨first,hst⟩
      (show step ops calls ⟨.schedule k (rem+1) i xs,stack⟩ =
        .proceed ⟨.enter k (ops.childInput i (ops.prepare i xs)),f::stack⟩ from rfl) seq
    convert start using 1
    all_goals simp only [Work.pc,Work.ticks,List.length_append,Nat.add_mul,Nat.one_mul]
    all_goals omega

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
