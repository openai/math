import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialRefinement

/-! A proof-only description of a genuine recursive trial node and its certified
chronological call prefixes. These witnesses never enter the compiled machine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States States.Mass Moment TrialExecution

structure SourceNode (N ne : ℕ) where
  level : ℕ
  history : History N
  path : Path (Fin N) (Vertex N level)
  weights : Weights ne
  nonneg : ∀ e, 0 ≤ weights e
  zeroTail : ∀ d, level ≤ d → ∀ i, history d i = 0
  canonical : path = pathFromRows N (packHistory level history) level

namespace SourceNode

variable {N ne : ℕ}

def initial (N : ℕ) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) : SourceNode N ne :=
  ⟨0,(fun _ _ => 0),.root,w,hw,(fun _ _ _ => rfl),rfl⟩

def input (c : SourceNode N ne) := codeInput c.level c.history c.weights

def extend (c : SourceNode N ne) (y : Prices N c.level) (dw : Weights ne) (nn : ∀ e, 0 ≤ dw e) :
    SourceNode N ne :=
  ⟨c.level+1,c.history.push c.level y,.extend c.path y (vertexDecidableEq N c.level),dw,nn,
    history_push_zero_tail _ _ c.zeroTail, by rw [c.canonical,pathFromRows_push]⟩

def exec (c : SourceNode N ne) (r R : ℕ) (experts : Fin ne → Expert N) (k : ℕ) :=
  execute r R experts (marketSolverAtCommonWeightUnit experts) k c.level c.path c.history c.weights c.nonneg

def stepAt (c : SourceNode N ne) (r R : ℕ) (experts : Fin ne → Expert N) (k j : ℕ)
    (xs : Fin j → Call N ne r c.level) :=
  executeStep experts (marketSolverAtCommonWeightUnit experts) c.weights c.nonneg c.history c.path
    (fun y dw nn => (c.extend y dw nn).exec r R experts k) j xs

def schedule (c : SourceNode N ne) (r R : ℕ) (experts : Fin ne → Expert N) (k j : ℕ) :=
  runSchedule (fun _ xs a => StepOK experts c.weights xs a) (c.stepAt r R experts k) j

def rows {r j : ℕ} (c : SourceNode N ne) (xs : Fin j → Call N ne r c.level) :=
  List.ofFn (fun i => codeCall (xs i))

def selectedPrice {r j : ℕ} (c : SourceNode N ne) (experts : Fin ne → Expert N)
    (xs : Fin j → Call N ne r c.level) : Prices N c.level :=
  if hj : j < r then
    (marketSolverAtCommonWeightUnit experts c.level c.history (incomingLocal experts c.weights xs)
      (incomingLocal_nonneg experts c.weights c.nonneg xs)).prices
  else fun i => median fun t : Fin r =>
    (xs ⟨t.val, lt_of_lt_of_le t.isLt (Nat.le_of_not_gt hj)⟩).data.baseline i

def next {r j : ℕ} (c : SourceNode N ne) (experts : Fin ne → Expert N)
    (xs : Fin j → Call N ne r c.level) : SourceNode N ne :=
  c.extend (c.selectedPrice experts xs) (incomingDeep experts c.weights xs) (incomingDeep_nonneg _ _ c.nonneg xs)

def prepared {r j : ℕ} (c : SourceNode N ne) (R : ℕ) (experts : Fin ne → Expert N)
    (xs : Fin j → Call N ne r c.level) : Prepared :=
  (fixedKernel R r experts).prepare c.input (c.rows xs)

def frame {r j : ℕ} (c : SourceNode N ne) (R : ℕ) (experts : Fin ne → Expert N)
    (k rem : ℕ) (xs : Fin j → Call N ne r c.level) : Frame NodeInput Prepared Completed :=
  ⟨k,rem,c.input,c.rows xs,c.prepared R experts xs⟩

theorem childInput_eq {r j : ℕ} (c : SourceNode N ne) (R : ℕ) (experts : Fin ne → Expert N)
    (xs : Fin j → Call N ne r c.level) :
    (fixedKernel R r experts).childInput c.input (c.prepared R experts xs) = (c.next experts xs).input := by
  change descend _ (preparePacketSized _ _ _ _ _ _) = codeInput _ _ _
  simp only [input,rows]
  by_cases hj : j < r
  · rw [prepare_probe_spec experts c.weights c.nonneg c.history c.zeroTail xs hj,descend_probe]
    simp only [next,extend,selectedPrice,dite_eq_left hj]
  · rw [prepare_final_spec experts c.weights c.history xs (Nat.le_of_not_gt hj),descend_final]
    simp only [next,extend,selectedPrice,dite_eq_right hj]

/-- Decompose a real adaptive call into the exact child's trace and its exact
feedback prefix. The returned data remains the certified reference child. -/
theorem split {r j : ℕ} (c : SourceNode N ne) (R : ℕ) (experts : Fin ne → Expert N)
    (k : ℕ) (xs : Fin j → Call N ne r c.level) {tr rc}
    (e : Emits (c.stepAt r R experts k j xs) tr rc) :
    ∃ left middle ch, tr = left++middle ∧ Emits ((c.next experts xs).exec r R experts k) left ch ∧
      Scan ((fixedKernel R r experts).finish c.input (c.rows xs) (c.prepared R experts xs) (codeOutput ch.val))
        [] middle (codeCall rc.val) := by
  by_cases hj : j < r
  · simp only [stepAt,executeStep,dite_eq_left hj] at e
    obtain ⟨left,ch,middle,rfl,hc,hf⟩ := e.bind_inv
    obtain ⟨z,hz,rfl⟩ := hf.map_inv
    let a := marketSolverAtCommonWeightUnit experts c.level c.history (incomingLocal experts c.weights xs)
      (incomingLocal_nonneg experts c.weights c.nonneg xs)
    refine ⟨left,middle,ch,rfl,?_,?_⟩
    · change Emits (execute r R experts (marketSolverAtCommonWeightUnit experts) k (c.level+1)
        (.extend c.path (c.selectedPrice experts xs) (vertexDecidableEq N c.level))
        (c.history.push c.level (c.selectedPrice experts xs)) (incomingDeep experts c.weights xs)
        (incomingDeep_nonneg _ _ c.nonneg xs)) left ch
      rw [show c.selectedPrice experts xs = a.prices by simp only [selectedPrice,dite_eq_left hj,a]]
      exact hc
    · change Scan (completeSized feedbackPrefix N ne (List.ofFn fun i => packExpert (experts i))
        c.input (c.rows xs) (preparePacketSized N r ne _ _ _) (codeOutput ch.val)) [] _ _
      simp only [input,rows]
      rw [prepare_probe_spec experts c.weights c.nonneg c.history c.zeroTail xs hj]
      exact finish_scan_probe experts c.weights c.history c.path c.canonical xs hj a ch hz
  · simp only [stepAt,executeStep,dite_eq_right hj] at e
    obtain ⟨ch,hc,rfl⟩ := e.map_inv
    let y : Prices N c.level := fun i => median fun t : Fin r =>
      (xs ⟨t.val, lt_of_lt_of_le t.isLt (Nat.le_of_not_gt hj)⟩).data.baseline i
    refine ⟨tr,[],ch,(List.append_nil _).symm,?_,?_⟩
    · change Emits (execute r R experts (marketSolverAtCommonWeightUnit experts) k (c.level+1)
        (.extend c.path (c.selectedPrice experts xs) (vertexDecidableEq N c.level))
        (c.history.push c.level (c.selectedPrice experts xs)) (incomingDeep experts c.weights xs)
        (incomingDeep_nonneg _ _ c.nonneg xs)) tr ch
      rw [show c.selectedPrice experts xs = y by simp only [selectedPrice,dite_eq_right hj,y]]
      exact hc
    · change Scan (completeSized feedbackPrefix N ne (List.ofFn fun i => packExpert (experts i))
        c.input (c.rows xs) (preparePacketSized N r ne _ _ _) (codeOutput ch.val)) [] _ _
      simp only [input,rows]
      rw [prepare_final_spec experts c.weights c.history xs (Nat.le_of_not_gt hj)]
      exact finish_scan_final experts c.weights c.history xs (Nat.le_of_not_gt hj) y ch

theorem prepared_baseline {r j : ℕ} (c : SourceNode N ne) (R : ℕ) (experts : Fin ne → Expert N)
    (xs : Fin j → Call N ne r c.level) :
    (c.prepared R experts xs).baseline = packTable N c.level (c.selectedPrice experts xs) := by
  change (preparePacketSized N r ne _ _ _).baseline = _
  simp only [input,rows]
  by_cases hj : j < r
  · rw [prepare_probe_spec experts c.weights c.nonneg c.history c.zeroTail xs hj]
    simp only [codeProbe,selectedPrice,dite_eq_left hj]
  · rw [prepare_final_spec experts c.weights c.history xs (Nat.le_of_not_gt hj)]
    simp only [codeFinal,selectedPrice,dite_eq_right hj]

end SourceNode
end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
