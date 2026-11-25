import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSourceMarks
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignScoreGuard
import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareWeightsMachine

/-! The physical score-shift clip is inactive on every actual cached prefix. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States.Mass Moment TrialExecution Finset

variable {N ne r R : ℕ} {experts : Fin ne → Expert N}

theorem SeenPrefix.callHeight {c : SourceNode N ne} {k j : ℕ} (p : SeenPrefix r R experts c k j)
    (i : Fin j) : (p.calls.val i).child.trace.height ≤ k := by
  have h := runSchedule_all (fun (j : ℕ) (xs : Fin j → Call N ne r c.level) a => StepOK experts c.weights xs a)
    (c.stepAt r R experts k) (fun a => a.child.trace.height ≤ k) j (by
      intro j hj xs
      apply executeStep_all_child_height
      intro y dw hdw
      exact execute_all_trace_height r R experts (marketSolverAtCommonWeightUnit experts) k _
        (c.extend y dw hdw).path (c.extend y dw hdw).history dw hdw)
  exact p.observed.of_allOutputs h i

theorem SeenPrefix.score {c : SourceNode N ne} {k j : ℕ} (p : SeenPrefix r R experts c k j)
    (hN : 0 < N) (hk : k ≤ depth N) (a : Fin j) (e : Fin ne) :
    atD (codeCall (p.calls.val a)).child.scores e.val ≤ (2*N)^274 := by
  let ch : Certified (N:=N) (r:=r) (l:=c.level+1) (incomingDeep experts c.weights («prefix» p.calls.val a)) :=
    ⟨(p.calls.val a).child,(p.calls.property a).admissible⟩
  have ht : ch.val.trace.height ≤ Nat.log 2 N+1 := by
    simpa only [ch,depth,Nat.log2_eq_log_two] using (p.callHeight a).trans hk
  have hs := certified_score_le_public _ ch hN ht e
  simpa only [codeCall,codeOutput,atD_vector,ch] using hs

theorem SeenPrefix.scoreTotal {c : SourceNode N ne} {k j : ℕ} (p : SeenPrefix r R experts c k j)
    (hN : 0 < N) (hk : k ≤ depth N) (e : Fin ne) :
    Native.scoreTotal (c.rows p.calls.val) e.val ≤ j * (2*N)^274 := by
  simp only [Native.scoreTotal,SourceNode.rows,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  calc
    _ ≤ ∑ _a : Fin j, (2*N)^274 := sum_le_sum (fun a _ => p.score hN hk a e)
    _ = _ := by simp

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
