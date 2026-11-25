import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialScan
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSchedule
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialAssemble

/-! The concrete first-order control machine implements the actual recursive price trial. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States States.Mass Moment TrialExecution

variable {N ne r l j : ℕ}

abbrev fixedKernel (R r : ℕ) (experts : Fin ne → Expert N) :=
  packetKernelSized feedbackPrefix N R r ne (List.ofFn (fun e => packExpert (experts e)))

/-- The only input needed from packed-market verification is the equality of the
actual prepared packets. This contains no hypothesis about control, queries or outputs. -/
structure PreparationMatches (r : ℕ) (experts : Fin ne → Expert N) : Prop where
  probe : ∀ {l j : ℕ} (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N),
    (∀ d, l ≤ d → ∀ i, history d i = 0) → ∀ (xs : Fin j → Call N ne r l) (_ : j < r),
    preparePacketSized N r ne (List.ofFn fun e => packExpert (experts e)) (codeInput l history w)
      (List.ofFn fun a => codeCall (xs a)) =
    codeProbe (marketSolverAtCommonWeightUnit experts l history (incomingLocal experts w xs)
      (incomingLocal_nonneg experts w hw xs)) (incomingDeep experts w xs)
  final : ∀ {l j : ℕ} (w : Weights ne) (history : History N) (xs : Fin j → Call N ne r l) (hj : r ≤ j),
    preparePacketSized N r ne (List.ofFn fun e => packExpert (experts e)) (codeInput l history w)
      (List.ofFn fun a => codeCall (xs a)) =
    codeFinal (fun i => median fun t : Fin r => (xs ⟨t.val,lt_of_lt_of_le t.isLt hj⟩).data.baseline i)
      (incomingDeep experts w xs)

/-- Refinement of a *single* scheduled probe or final call using the actual
market clearer, cached weights, and the packed single-coordinate feedback scanner. -/
theorem executeStep_refines_of_prepare (R fuel : ℕ) (experts : Fin ne → Expert N)
    (matching : PreparationMatches r experts) (w : Weights ne)
    (hw : ∀ e, 0 ≤ w e) (history : History N) (path : Path (Fin N) (Vertex N l))
    (zeroTail : ∀ d, l ≤ d → ∀ i, history d i = 0)
    (hpath : path = pathFromRows N (packHistory l history) l)
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N:=N) (r:=r) (l:=l+1) dw))
    (childRef : ∀ y dw hn tr ch, Emits (child y dw hn) tr ch →
      Evaluates (fixedKernel R r experts) (2*r) (.node fuel (codeInput (l+1) (history.push l y) dw))
        tr (codeOutput ch.val))
    (xs : Fin j → Call N ne r l) {tr c}
    (e : Emits (executeStep experts (marketSolverAtCommonWeightUnit experts) w hw history path child j xs) tr c) :
    RefinesStep (fixedKernel R r experts) (2*r) fuel (codeInput l history w)
      (List.ofFn fun a => codeCall (xs a)) tr (codeCall c.val) := by
  by_cases hj : j < r
  · simp only [executeStep, dite_eq_left hj] at e
    obtain ⟨left,ch,middle,rfl,hc,hfeedback⟩ := e.bind_inv
    obtain ⟨z,hz,rfl⟩ := hfeedback.map_inv
    let A := marketSolverAtCommonWeightUnit experts l history (incomingLocal experts w xs)
      (incomingLocal_nonneg experts w hw xs)
    have prep := matching.probe w hw history zeroTail xs hj
    refine ⟨left,middle,codeOutput ch.val,rfl,?_,?_⟩
    · change Evaluates _ _ (.node _ (descend _ (preparePacketSized _ _ _ _ _ _))) _ _
      rw [prep, descend_probe]
      exact childRef A.prices _ _ _ ch hc
    · change Scan (completeSized feedbackPrefix N ne (List.ofFn (fun a => packExpert (experts a)))
        (codeInput l history w) (List.ofFn (fun a => codeCall (xs a)))
        (preparePacketSized N r ne _ _ _) (codeOutput ch.val)) [] _ _
      rw [prep]
      exact finish_scan_probe experts w history path hpath xs hj A ch hz
  · simp only [executeStep, dite_eq_right hj] at e
    obtain ⟨ch,hc,rfl⟩ := e.map_inv
    let y : Prices N l := fun i => median fun a : Fin r =>
      (xs ⟨a.val, lt_of_lt_of_le a.isLt (Nat.le_of_not_gt hj)⟩).data.baseline i
    have prep := matching.final w history xs (Nat.le_of_not_gt hj)
    refine ⟨tr,[],codeOutput ch.val,(List.append_nil _).symm,?_,?_⟩
    · change Evaluates _ _ (.node _ (descend _ (preparePacketSized _ _ _ _ _ _))) _ _
      rw [prep, descend_final]
      exact childRef y _ _ _ ch hc
    · change Scan (completeSized feedbackPrefix N ne (List.ofFn (fun a => packExpert (experts a)))
        (codeInput l history w) (List.ofFn (fun a => codeCall (xs a)))
        (preparePacketSized N r ne _ _ _) (codeOutput ch.val)) [] _ _
      rw [prep]
      exact finish_scan_final experts w history xs (Nat.le_of_not_gt hj) y ch

/-- For every word-level transcript, including inconsistent oracle labels, the
same public questions appear in exactly the same order and the raw return packet
contains the same prices, cached scores, and observation log as the structured trial. -/
theorem execute_common_refines_of_prepare (r R : ℕ) (experts : Fin ne → Expert N)
    (matching : PreparationMatches r experts) (fuel : ℕ) :
    ∀ {l : ℕ} (path : Path (Fin N) (Vertex N l)) (history : History N)
      (w : Weights ne) (hw : ∀ e, 0 ≤ w e),
      (∀ d, l ≤ d → ∀ i, history d i = 0) →
      path = pathFromRows N (packHistory l history) l →
      ∀ {tr out}, Emits (execute r R experts (marketSolverAtCommonWeightUnit experts)
        fuel l path history w hw) tr out →
      Evaluates (fixedKernel R r experts) (2*r) (.node fuel (codeInput l history w)) tr (codeOutput out.val) := by
  induction fuel with
  | zero =>
    intro l path history w hw hz hp tr out e
    cases e
    rw [← leafPacket_spec r R l history w]
    exact .leaf _
  | succ fuel ih =>
    intro l path history w hw hz hp tr out e
    rw [execute] at e
    obtain ⟨run,hs,rfl⟩ := e.map_inv
    apply Evaluates.node
    rw [← assemblePacket_spec experts history w run]
    apply runSchedule_evaluates (fixedKernel R r experts) (2*r) fuel (codeInput l history w) codeCall _ hs
    intro j xs c script hstep
    apply executeStep_refines_of_prepare R fuel experts matching w hw history path hz hp _ _ xs hstep
    intro y dw nn t ch hc
    exact ih (l := l+1) (.extend path y (vertexDecidableEq N l)) (history.push l y) dw nn
      (history_push_zero_tail history y hz) (by rw [hp, pathFromRows_push]) hc

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
