import OAI.Optimization.LinearProgramming.PriceGame.TrialExecution
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionAssembleFacts
import OAI.Optimization.LinearProgramming.PriceGame.Complexity

/-! Resource bounds for the actual recursive driver on arbitrary history-dependent replies. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

universe u v

namespace Computation

variable {N : ℕ} {A : Type u} {B : Type v}

/-- A structural invariant on every possible output, covering either
Boolean reply at each occurrence of a query. -/
inductive AllOutputs (P : A → Prop) : Computation N A → Prop
  | pure {a : A} : P a → AllOutputs P (.pure a)
  | ask {q : Query N} {next : Bool → Computation N A} :
      (∀ b, AllOutputs P (next b)) → AllOutputs P (.ask q next)

theorem AllOutputs.bind {P : A → Prop} {Q : B → Prop} {p : Computation N A}
    (h : AllOutputs P p) (f : A → Computation N B)
    (hf : ∀ a, P a → AllOutputs Q (f a)) : AllOutputs Q (p.bind f) := by
  induction h with
  | pure ha => exact hf _ ha
  | ask _ ih => exact .ask ih

theorem AllOutputs.map {P : A → Prop} {Q : B → Prop} {p : Computation N A}
    (h : AllOutputs P p) (f : A → B) (hf : ∀ a, P a → Q (f a)) : AllOutputs Q (p.map f) :=
  h.bind (fun a => .pure (f a)) fun a ha => .pure (hf a ha)

theorem AllOutputs.map_of_forall {Q : B → Prop} (p : Computation N A) (f : A → B)
    (h : ∀ a, Q (f a)) : AllOutputs Q (p.map f) := by
  induction p with
  | pure a => exact .pure (h a)
  | ask _ _ ih => exact .ask ih

theorem AllOutputs.run {P : A → Prop} {p : Computation N A}
    (h : AllOutputs P p) (reply : List (Query N × Bool) → Query N → Bool)
    (history : List (Query N × Bool)) : P (p.run reply history) := by
  induction h generalizing history with
  | pure ha => exact ha
  | @ask q next _ ih =>
    exact ih (reply history q) ((q, reply history q) :: history)

end Computation

namespace TrialExecution

open Moment States.Mass
open OAI.Optimization.LinearProgramming.PriceGame.Computation

variable {N ne r l : ℕ}

/-- Uniform event invariants propagate through a finite schedule, even when each
step selects its next computation after observing all preceding values. -/
theorem runSchedule_all {A : Type*} (P : (j : ℕ) → (Fin j → A) → A → Prop)
    (step : ∀ j xs, Computation N {y // P j xs y}) (Q : A → Prop) (n : ℕ)
    (h : ∀ j < n, ∀ xs, AllOutputs (fun y => Q y.val) (step j xs)) :
    AllOutputs (fun s : Schedule P n => ∀ j, Q (s.val j)) (runSchedule P step n) := by
  induction n with
  | zero => exact .pure (fun j => Fin.elim0 j)
  | succ n ih =>
    rw [runSchedule]
    apply (ih fun j hj => h j (Nat.lt_succ_of_lt hj)).bind
    intro s hs
    apply (h n (Nat.lt_succ_self n) s.val).map
    intro x hx j
    cases j using Fin.lastCases with
    | cast i => simpa [snocSchedule] using hs i
    | last => simpa [snocSchedule] using hx

theorem executeStep_all_child_height (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (history : History N)
    (path : States.Path (Fin N) (Vertex N l))
    (child : (y : Prices N l) → (dw : Weights ne) → (∀ e, 0 ≤ dw e) →
      Computation N (Certified (N := N) (r := r) (l := l+1) dw))
    (d : ℕ) (hc : ∀ y dw hdw, AllOutputs (fun ch => ch.val.trace.height ≤ d) (child y dw hdw))
    (j : ℕ) (xs : Fin j → Call N ne r l) :
    AllOutputs (fun c => c.val.child.trace.height ≤ d)
      (executeStep experts solve w hw history path child j xs) := by
  unfold executeStep
  dsimp only
  split
  · apply (hc _ _ _).bind
    intro ch hch
    apply AllOutputs.map_of_forall
    exact fun _ => hch
  · apply (hc _ _ _).map
    exact fun _ hch => hch

theorem execute_all_trace_height (r R : ℕ) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (fuel l : ℕ) (path : States.Path (Fin N) (Vertex N l))
    (history : History N) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) :
    AllOutputs (fun o => o.val.trace.height ≤ fuel) (execute r R experts solve fuel l path history w hw) := by
  induction fuel generalizing l history w with
  | zero => exact .pure (by rfl)
  | succ d ih =>
    let child := fun (y : Prices N l) (dw : Weights ne) (hdw : ∀ e, 0 ≤ dw e) =>
      execute r R experts solve d (l+1) (.extend path y (vertexDecidableEq N l)) (history.push l y) dw hdw
    let p := fun (j : ℕ) (xs : Fin j → Call N ne r l) (c : Call N ne r l) => StepOK experts w xs c
    let step := executeStep experts solve w hw history path child
    change AllOutputs _ ((runSchedule p step (2*r)).map (assemble experts history w))
    apply (runSchedule_all p step (fun c => c.child.trace.height ≤ d) (2*r) ?_).map
    · intro s hs
      exact assemble_height_le experts history w s d hs
    · intro j _ xs
      apply executeStep_all_child_height
      intro y dw hdw
      exact ih (l+1) _ (history.push l y) dw hdw

theorem execute_result_height (r R : ℕ) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (fuel l : ℕ) (path : States.Path (Fin N) (Vertex N l))
    (history : History N) (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    (reply : List (Query N × Bool) → Query N → Bool) (answers : List (Query N × Bool)) :
    ((execute r R experts solve fuel l path history w hw).run reply answers).val.trace.height ≤ fuel :=
  AllOutputs.run (p := execute r R experts solve fuel l path history w hw)
    (P := fun o => o.val.trace.height ≤ fuel)
    (execute_all_trace_height r R experts solve fuel l path history w hw) reply answers

theorem run_trace_height (R : ℕ) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool)) :
    ((run R experts solve w hw).run reply history).val.trace.height ≤ depth N := by
  unfold run
  exact execute_result_height probes R experts solve (depth N) 0 .root (fun _ _ => 0) w hw reply history

theorem run_trial_calls_le (R : ℕ) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (hN : 0 < N)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool)) :
    Complexity.calls ((run R experts solve w hw).run reply history).val.trace ≤ (2 * N)^602 :=
  Complexity.trial_calls_polynomial N hN _ (run_trace_height R experts solve w hw reply history)

theorem certified_multiplier_size_le (C B : ℕ) (hC : scaleQ = (C : ℚ)) (hB : C + 2 ≤ 2 ^ B)
    (w : Weights ne) (out : Certified (N := N) (r := r) (l := l) w) (hN : 0 < N)
    (hh : out.val.trace.height ≤ Nat.log 2 N + 1) (e : Fin ne) :
    Nat.size (2 ^ out.val.scores[e]) ≤ (2*N)^B+1 := by
  have hσ : 0 ≤ sigmaQ := div_nonneg zero_le_one (pow_nonneg (by norm_num) _)
  have ha := Eq.mp (congrArg (fun c : ℚ => out.val.trace.Admissible c sigmaQ eta
    (fun e => (w e : ℝ))) hC) out.property
  have he := (out.val.scores_eq e).trans (congrArg (fun c : ℚ => out.val.trace.score c sigmaQ e) hC)
  exact (congrArg (fun v : ℕ => Nat.size (2 ^ v)) he).le.trans
    (out.val.trace.multiplier_size_le C B N sigmaQ eta hσ hN.ne' hB hh _ ha e)

theorem run_multiplier_size_le (R C B : ℕ) (hC : scaleQ = (C : ℚ)) (hB : C + 2 ≤ 2 ^ B)
    (experts : Fin ne → Expert N) (solve : MarketSolver experts)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (hN : 0 < N)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool)) (e : Fin ne) :
    Nat.size (2 ^ ((run R experts solve w hw).run reply history).val.scores[e]) ≤ (2*N)^B+1 := by
  refine certified_multiplier_size_le C B hC hB w ((run R experts solve w hw).run reply history)
    hN ?_ e
  simpa only [depth, Nat.log2_eq_log_two] using run_trace_height R experts solve w hw reply history

private theorem binaryScale_bound (k : ℕ) (hk : 1 ≤ k) : 2 ^ k + 2 ≤ (2 : ℕ) ^ (k + 1) := by
  have h : 2 ≤ (2 : ℕ)^k :=
    (show 2 = (2 : ℕ)^1 from (pow_one _).symm).le.trans (pow_le_pow_right' (by decide) hk)
  calc
    2 ^ k + 2 ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left h _
    _ = 2 ^ k * 2 := (mul_two _).symm
    _ = 2 ^ (k + 1) := (pow_succ 2 k).symm

theorem exists_integral_scale : ∃ C : ℕ, scaleQ = (C : ℚ) ∧ C + 2 ≤ 2 ^ 274 := by
  refine ⟨2 ^ 273, ?_, ?_⟩
  · simp only [scaleQ, sigmaQ, one_div, div_inv_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact (mul_comm 2 ((2 : ℚ) ^ 272)).trans (pow_succ 2 272).symm
  · exact (binaryScale_bound 273 (by decide)).trans_eq
      (congrArg (fun k : ℕ => (2 : ℕ) ^ k) (show 273 + 1 = 274 from rfl))

/-- Public dimension bound for any cached score in a certified output of suitable depth. -/
theorem certified_score_le_public (w : Weights ne) (out : Certified (N := N) (r := r) (l := l) w)
    (hN : 0 < N) (hh : out.val.trace.height ≤ Nat.log 2 N + 1) (e : Fin ne) :
    out.val.scores[e] ≤ (2*N)^274 := by
  obtain ⟨C, hC, hB⟩ := exists_integral_scale
  have hs := certified_multiplier_size_le C 274 hC hB w out hN hh e
  rw [Nat.size_pow] at hs
  exact Nat.le_of_succ_le_succ hs

/-- Each score multiplier in the returned root array uses at most ((2N)^{274}+1)
binary digits, including on a history which cannot arise from any hidden assignment. -/
theorem run_score_multiplier_bits (R : ℕ) (experts : Fin ne → Expert N)
    (solve : MarketSolver experts) (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (hN : 0 < N)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool)) (e : Fin ne) :
    Nat.size (2 ^ ((run R experts solve w hw).run reply history).val.scores[e]) ≤ (2*N)^274+1 := by
  obtain ⟨C, hC, hB⟩ := exists_integral_scale
  exact run_multiplier_size_le R C 274 hC hB experts solve w hw hN reply history e



end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
