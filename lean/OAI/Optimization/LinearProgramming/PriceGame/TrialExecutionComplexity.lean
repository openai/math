import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionSize
import OAI.Optimization.LinearProgramming.PriceGame.LearningPolynomial
import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryArithmetic

/-! Bounds for all branches of the executable recursive trial, including inconsistent replies. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

universe u v

namespace Computation

variable {N R : ℕ} {anchor : Fin N} {α : Type u} {β : Type v}

theorem AllOutputs.reaches {P : α → Prop} {p : Computation N α} {a : α} (hp : AllOutputs P p)
    (hidden : Hidden N R anchor) (hr : Reaches hidden p a) : P a := by
  induction hr with
  | pure => cases hp with | pure h => exact h
  | ask _ _ ih => cases hp with | ask h => exact ih (h _)

end Computation

namespace TrialExecution

open States.Mass Moment Finset
variable {N ne r l : ℕ}

/-- The true recursive query bound, before specializing the branch factor. -/
theorem queryBound_le (N r k l : ℕ) :
    queryBound N r k l ≤ N * 2^l * (6*r+1)^k :=
  queryRec_le _ _ _ (fun _ => rfl) (fun _ _ => le_rfl) _ _

private theorem queryBound_at_base (N r d k : ℕ) (hb : (6*r+1)^d ≤ (2*(N+1))^k) :
    queryBound N r d 0 ≤ (2*(N+1))^(k+1) := by
  calc
    _ ≤ N * (6*r+1)^d := by simpa only [pow_zero, mul_one] using queryBound_le N r d 0
    _ ≤ (2*(N+1)) * (2*(N+1))^k := Nat.mul_le_mul (by omega) hb
    _ = _ := (pow_succ' _ k).symm

theorem queryBound_polynomial (N : ℕ) :
    queryBound N probes (depth N) 0 ≤ (2*(N+1))^605 :=
  (queryBound_at_base N probes (depth N) 604 (probeBranchPow_le N)).trans_eq
    (congrArg (fun k : ℕ => (2*(N+1))^k) (show 604+1 = 605 from rfl))

theorem run_height_polynomial (R : ℕ) (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    (run R experts solve w hw).height ≤ (2*(N+1))^605 :=
  (run_height_le ..).trans (queryBound_polynomial N)

private theorem length_flatten_le {α : Type*} (L : List (List α)) (K : ℕ)
    (h : ∀ x ∈ L, x.length ≤ K) : L.flatten.length ≤ L.length*K := by
  induction L with
  | nil => simp
  | cons a xs ih =>
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (h _ (List.mem_cons_self ..))
      (ih (fun x hx => h _ (List.mem_cons_of_mem _ hx)))

theorem nodeLog_length_le (history : History N) (xs : Fin (2*r) → Call N ne r l) (K : ℕ)
    (h : ∀ i, (xs i).child.log.length ≤ K) : (nodeLog history xs).length ≤ 2*r*(K+1) := by
  unfold nodeLog
  apply le_trans (length_flatten_le _ (K+1) ?_)
  · simp
  · intro list hl
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    split
    · exact Nat.succ_le_succ (h i)
    · exact (h i).trans (Nat.le_succ K)

theorem executeStep_childLog_le (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw)) (K : ℕ)
    (hc : ∀ y dw hdw, Computation.AllOutputs (fun ch => ch.val.log.length ≤ K) (child y dw hdw))
    (j : ℕ) (xs : Fin j → Call N ne r l) :
    Computation.AllOutputs (fun c => c.val.child.log.length ≤ K)
      (executeStep experts solve w hw history path child j xs) := by
  unfold executeStep
  dsimp only
  split
  · apply (hc _ _ _).bind
    intro ch hch
    apply Computation.AllOutputs.map_of_forall
    exact fun _ => hch
  · apply (hc _ _ _).map
    exact fun _ hch => hch

theorem execute_log_length (r R : ℕ) (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (fuel l : ℕ) (path : States.Path (Fin N) (Vertex N l)) (history : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    Computation.AllOutputs (fun out => out.val.log.length ≤ probeLogBound r fuel)
      (execute r R experts solve fuel l path history w hw) := by
  induction fuel generalizing l history w with
  | zero => exact .pure le_rfl
  | succ k ih =>
    let child := fun (y : Prices N l) (dw : Weights ne) (hdw : ∀ e, 0 ≤ dw e) =>
      execute r R experts solve k (l+1) (.extend path y (vertexDecidableEq N l)) (history.push l y) dw hdw
    let p := fun (j : ℕ) (xs : Fin j → Call N ne r l) (c : Call N ne r l) => StepOK experts w xs c
    let step := executeStep experts solve w hw history path child
    change Computation.AllOutputs _ ((runSchedule p step (2*r)).map (assemble experts history w))
    apply (runSchedule_all p step (fun c => c.child.log.length ≤ probeLogBound r k) (2*r) ?_).map
    · intro s hs
      exact nodeLog_length_le history s.val _ hs
    · intro j _ xs
      apply executeStep_childLog_le
      intro y dw hdw
      exact ih (l+1) _ (history.push l y) dw hdw

theorem execute_result_log_length (r R : ℕ) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (fuel l : ℕ) (path : States.Path (Fin N) (Vertex N l))
    (history : History N) (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    (reply : List (Query N × Bool) → Query N → Bool) (transcript : List (Query N × Bool)) :
    ((execute r R experts solve fuel l path history w hw).run reply transcript).val.log.length ≤
      probeLogBound r fuel :=
  Computation.AllOutputs.run (P := fun o : Certified (N:=N) (r:=r) (l:=l) w =>
    o.val.log.length ≤ probeLogBound r fuel)
    (execute_log_length r R experts solve fuel l path history w hw) reply transcript

theorem run_log_length_polynomial (R : ℕ) (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    (reply : List (Query N × Bool) → Query N → Bool) (h : List (Query N × Bool)) :
    ((run R experts solve w hw).run reply h).val.log.length ≤ (2*(N+1))^604 := by
  unfold run
  exact Nat.le_trans (execute_result_log_length probes R experts solve (depth N) 0 .root
    (fun _ _ => 0) w hw reply h) (probeLogBound_polynomial N)

theorem run_reaches_log_length {R H : ℕ} {anchor : Fin N} (hidden : Hidden N H anchor)
    (experts : Fin ne → Expert N) (solve : MarketSolver experts) (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    (out : Certified (N:=N) (r:=probes) (l:=0) w) (hr : Computation.Reaches hidden (run R experts solve w hw) out) :
    out.val.log.length ≤ (2*(N+1))^604 :=
  ((execute_log_length probes R experts solve (depth N) 0 .root (fun _ _ => 0) w hw).reaches hidden hr).trans
    (probeLogBound_polynomial N)

theorem probeLogBound_le_probeBudget (N : ℕ) (hN : 0 < N) :
    probeLogBound probes (depth N) ≤ Learning.Pool.probeBudget N := by
  have heq : probes = Complexity.probes := rfl
  rw [heq]
  change probeLogBound Complexity.probes (depth N) ≤ Complexity.probes * (2*N)^602
  have hpr : 1 ≤ Complexity.probes := heq ▸ probes_pos
  have hlast (x : ℕ) : x ≤ Complexity.probes*x := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right x hpr
  exact (probeLogBound_le_nodeCount Complexity.probes (depth N)).trans
    ((Complexity.trial_nodes_le N hN).trans (hlast _))

theorem run_reaches_probeBudget {R H : ℕ} {anchor : Fin N} (hidden : Hidden N H anchor)
    (experts : Fin ne → Expert N) (solve : MarketSolver experts) (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    (out : Certified (N:=N) (r:=probes) (l:=0) w) (hr : Computation.Reaches hidden (run R experts solve w hw) out) :
    out.val.log.length ≤ Learning.Pool.probeBudget N :=
  ((execute_log_length probes R experts solve (depth N) 0 .root (fun _ _ => 0) w hw).reaches hidden hr).trans
    (probeLogBound_le_probeBudget N (Nat.zero_lt_of_lt anchor.isLt))

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
