import OAI.Optimization.LinearProgramming.PriceGame.TrialPathGrid
import OAI.Optimization.LinearProgramming.PriceGame.TrialLogDepth
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionComplexity

/-! The price/output invariant for each cached child retained in a partially completed
node schedule. Both possible answers are admitted at every source query. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

universe u

open States.Mass

/-- The first conjunct bounds baseline, mapped prices and every logged current and
historical price. The remaining fields apply to the same actual cached child. -/
def CachedCallBox {N ne r l : ℕ} (D U B top fuel : ℕ) (c : Call N ne r l) : Prop :=
  CallBox D U B c ∧ (∀ i, PriceBox D B (c.child.prices i)) ∧
    c.child.log.length ≤ probeLogBound r fuel ∧
    (∀ p ∈ c.child.log, p.level < top) ∧ c.child.trace.height ≤ fuel

/-- A prefix of the exact call-generating schedule internal to `execute`. -/
def cachedPrefix {N ne : ℕ} (r R : ℕ) (experts : Fin ne → Expert N) (fuel l : ℕ)
    (path : States.Path (Fin N) (Vertex N l)) (history : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (j : ℕ) :=
  let solve := marketSolverAtCommonWeightUnit experts
  let child := fun (y : Prices N l) (dw : Weights ne) (hdw : ∀ e, 0 ≤ dw e) =>
    execute r R experts solve fuel (l+1) (.extend path y (vertexDecidableEq N l))
      (history.push l y) dw hdw
  runSchedule (fun _ xs c => StepOK experts w xs c)
    (executeStep experts solve w hw history path child) j

private theorem keep_output {N : ℕ} {A : Type u} {Q : Query N → Prop} {P S : A → Prop}
    {p : Computation N A} (hp : p.Guarded Q P) (hs : Computation.AllOutputs S p) :
    p.Guarded Q (fun x => P x ∧ S x) := by
  induction hs with
  | pure hx => exact ⟨hp,hx⟩
  | ask hs ih => exact ⟨hp.1,fun b => ih b (hp.2 b)⟩

/-- All previously completed calls at any source schedule prefix satisfy their simultaneous
cache bounds, including calls entered at a coordinatewise median baseline. -/
theorem cachedPrefix_guarded {N ne : ℕ} (r D R G top : ℕ) (hG : 0 < G)
    (experts : Fin ne → Expert N) (raw : RawBox D R experts)
    (hvertices : ∀ l ≤ top, ne+N*2^l+1 ≤ G)
    (fuel l : ℕ) (hl : l+1+fuel ≤ top)
    (path : States.Path (Fin N) (Vertex N l))
    (hp : path.pricesSatisfy (PriceBox D (Complexity.priceMax R G top)))
    (history : History N) (hh : HistoryBox D (Complexity.priceMax R G l) l history)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e) (j : ℕ) :
    (cachedPrefix r R experts fuel l path history w hw j).Guarded
      (fun q => ∀ i, PriceBox D (Complexity.priceMax R G top) (q.prices i))
      (fun xs => ∀ i : Fin j, CachedCallBox D (Complexity.priceMax R G (l+1))
        (Complexity.priceMax R G top) top fuel (xs.val i)) := by
  let U := Complexity.priceMax R G (l+1)
  let B := Complexity.priceMax R G top
  let solve := marketSolverAtCommonWeightUnit experts
  let child := fun (y : Prices N l) (cw : Weights ne) (hcw : ∀ e, 0 ≤ cw e) =>
    execute r R experts solve fuel (l+1) (.extend path y (vertexDecidableEq N l))
      (history.push l y) cw hcw
  let extra := fun (o : Output N ne r (l+1)) =>
    (∀ i, PriceBox D B (o.prices i)) ∧ o.log.length ≤ probeLogBound r fuel ∧
      (∀ p ∈ o.log, p.level < top) ∧ o.trace.height ≤ fuel
  have hB : U ≤ B := priceMax_mono R G hG (by omega)
  have hc (y : Prices N l) (hy : ∀ i, PriceBox D U (y i)) (cw : Weights ne) (hcw : ∀ e, 0 ≤ cw e) :
      (child y cw hcw).Guarded (fun q => ∀ i, PriceBox D B (q.prices i))
        (fun out => OutputBox D B out.val ∧ extra out.val) := by
    let next := States.Path.extend path y (vertexDecidableEq N l)
    have hprice := execute_price_grid r D R G top hG experts raw hvertices fuel (l+1) hl next
      ⟨hp,fun i => (hy i).mono hB⟩ (history.push l y)
      (historyBox_push (priceMax_mono R G hG (Nat.le_succ _)) hh hy) cw hcw
    have hlen := execute_log_length r R experts solve fuel (l+1) next (history.push l y) cw hcw
    have hlevels := execute_log_depth r R top experts solve fuel (l+1) hl next (history.push l y) cw hcw
    have hheight := execute_all_trace_height r R experts solve fuel (l+1) next (history.push l y) cw hcw
    apply Computation.guarded_mono (keep_output (keep_output (keep_output hprice hlen) hlevels) hheight)
      (fun _ h => h)
    intro out h
    exact ⟨h.1.1.1,h.1.1.1.1,h.1.1.2,h.1.2,h.2⟩
  unfold cachedPrefix
  apply runSchedule_guarded _ _ _ _ (fun _ c => CachedCallBox D U B top fuel c)
  intro k _ xs hx
  exact executeStep_box_with extra D R G B experts raw history hh path hp w hw (hvertices l (by omega))
    hB child hc k xs (fun i => (hx i).1)

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
