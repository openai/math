import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialWeightWire
import OAI.Optimization.LinearProgramming.PriceGame.TrialRecursiveWeightBounds
import OAI.Optimization.LinearProgramming.PriceGame.TrialWireBound
import OAI.Optimization.LinearProgramming.PriceGame.TrialCachedGrid
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialPrepare
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialScan

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire
namespace Envelope

open States.Mass TrialExecution Trial

variable {N ne : ℕ}

/-- Full arrays in every visited node input, plus the exact record returned by the physical
preparation function at every prefix of that node. The per-child assertion follows the
same baseline, history, table of earlier completions, and deeper weights as execution. -/
def TrialArraysFit (env : Envelope) (r R : ℕ) (es : Fin ne → Expert N) :
    (fuel l : ℕ) → States.Path (Fin N) (Vertex N l) → History N →
      (w : Weights ne) → (∀ e, 0 ≤ w e) → Prop
  | 0, l, _, h, w, _ => env.InputFits (codeInput l h w)
  | fuel+1, l, path, h, w, hw =>
    env.InputFits (codeInput l h w) ∧
    (weightSchedule r R es fuel l path h w hw).Guarded (fun _ => True) (fun xs =>
      ∀ j : Fin (2*r),
        let prior := TrialExecution.«prefix» xs.val j
        let y := (xs.val j).data.baseline
        env.PreparedFits (preparePacketSized N r ne (List.ofFn fun e => packExpert (es e))
          (codeInput l h w) (List.ofFn fun i => codeCall (prior i))) ∧
        TrialArraysFit env r R es fuel (l+1) (.extend path y (vertexDecidableEq N l))
          (h.push l y) (incomingDeep es w prior) (incomingDeep_nonneg es w hw prior))

private theorem mass_vertex_size (hN : 0 < N) (l : ℕ) (hl : l ≤ States.Mass.depth N) :
    N*2^l ≤ 2*N^2 := by
  have hc := card_vertices_le N l hN hl
  simpa only [card_vertices, Nat.mul_comm (2^l) N] using hc

private theorem schedule_current_boxes (r R D : ℕ) (es : Fin ne → Expert N) (raw : RawBox D R es)
    (hN : 0 < N) (fuel l : ℕ) (hl : l+(fuel+1) ≤ States.Mass.depth N)
    (path : States.Path (Fin N) (Vertex N l)) (h : History N)
    (w : Weights ne) (hw : ∀ e, 0 ≤ w e)
    (hp : path.pricesSatisfy (PriceBox D (Complexity.priceMax R (trialMarketSize N ne) (States.Mass.depth N))))
    (hh : HistoryBox D (Complexity.priceMax R (trialMarketSize N ne) l) l h) :
    (weightSchedule r R es fuel l path h w hw).Guarded (fun _ => True)
      (fun xs => ∀ j, CallBox D (Complexity.priceMax R (trialMarketSize N ne) (l+1))
        (Complexity.priceMax R (trialMarketSize N ne) (States.Mass.depth N)) (xs.val j)) := by
  let G := trialMarketSize N ne
  have hG : 0 < G := Nat.succ_pos _
  have hv (j) (hj : j ≤ States.Mass.depth N) : ne+N*2^j+1 ≤ G :=
    Nat.add_le_add_right (Nat.add_le_add_left (mass_vertex_size hN j hj) ne) 1
  exact Computation.guarded_mono (cachedPrefix_guarded r D R G (States.Mass.depth N) hG es raw hv
    fuel l (by omega) path hp h hh w hw (2*r)) (fun _ _ => True.intro) (fun _ hs i => (hs i).1)

/-- Uniform bounds for every serialized input and all the allocation/deep-weight arrays
created during every internal call to the fixed market solver, on arbitrary oracle paths. -/
theorem trialArraysFit_of_registers (env : Envelope) (r R D Q localQ B d : ℕ)
    (es : Fin ne → Expert N) (raw : RawBox D R es) (hN : 0 < N) (hr : 0 < r)
    (hD : 0 < D) (hL : 0 < localQ) (hd : localQ ≤ 2^d)
    (edep : States.Mass.depth N ≤ env.depth) (ev : 2*N^2 ≤ env.vertices) (ee : ne ≤ env.experts)
    (pw : 2*trialPriceBits N ne R D+4 ≤ env.width) (ww : 2*B+4 ≤ env.width)
    (fw : 2*(3+2*(B+d))+4 ≤ env.width) :
    ∀ fuel l (_hl : l+fuel ≤ States.Mass.depth N) (path : States.Path (Fin N) (Vertex N l)) (h : History N)
      (w : Weights ne) (hw : ∀ e, 0 ≤ w e),
      (∀ j, l ≤ j → ∀ i, h j i = 0) →
      path.pricesSatisfy (PriceBox D (Complexity.priceMax R (trialMarketSize N ne) (States.Mass.depth N))) →
      HistoryBox D (Complexity.priceMax R (trialMarketSize N ne) l) l h →
      WeightRegistersWithin r R es Q localQ B fuel l path h w hw →
      env.TrialArraysFit r R es fuel l path h w hw := by
  let G := trialMarketSize N ne
  have hG : 0 < G := Nat.succ_pos _
  have price {j} {q : ℚ} (hj : j ≤ States.Mass.depth N) (hq : PriceBox D (Complexity.priceMax R G j) q) :
      2*RAM.ratBits q+4 ≤ env.width :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (priceBox_ratBits (N:=N) (ne:=ne) hD
      (hq.mono (priceMax_mono R G hG hj)))) 4).trans pw
  have emitInput {l} (hl : l ≤ States.Mass.depth N) (history : History N) (w : Weights ne)
      (hh : HistoryBox D (Complexity.priceMax R G l) l history) (hw : ∀ i, RAM.ratBits (w i) ≤ B) :
      env.InputFits (codeInput l history w) :=
    env.codeInput_fits history w (hl.trans edep) ee (fun j hj => (mass_vertex_size hN j (hj.le.trans hl)).trans ev)
      (fun j hj i => price hl (hh j hj i)) (fun i => (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw i)) 4).trans ww)
  intro fuel
  induction fuel with
  | zero =>
    intro l hl path h w hw _ _ hh regs
    exact emitInput (by simpa using hl) h w hh (fun i => (regs i).2)
  | succ fuel ih =>
    intro l hl path h w hw hz hp hh regs
    refine ⟨emitInput (by omega) h w hh (fun i => (regs.1 i).2), ?_⟩
    have hb := schedule_current_boxes r R D es raw hN fuel l hl path h w hw hp hh
    apply Computation.guarded_mono (Computation.guarded_and regs.2 hb) (fun _ _ => True.intro)
    intro xs hx j
    let prior := TrialExecution.«prefix» xs.val j
    let y := (xs.val j).data.baseline
    have hyr (i) : PriceBox D (Complexity.priceMax R G (l+1)) (y i) := (hx.2 j).1 i
    have hloc (e) : (incomingLocal es w prior e).den ∣ localQ ∧ RAM.ratBits (incomingLocal es w prior e) ≤ B :=
      (hx.1.1 j j.isLt.le e).1
    have hdeep (e) : 2*RAM.ratBits (incomingDeep es w prior e)+4 ≤ env.width :=
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hx.1.1 j j.isLt.le e).2.2) 4).trans ww
    have hv : N*2^l ≤ env.vertices := (mass_vertex_size hN l (by omega)).trans ev
    have hn := priceMax_mono R G hG (show l+1 ≤ States.Mass.depth N by omega)
    constructor
    · by_cases hj : j.val < r
      · rw [prepare_probe_spec es w hw h hz prior hj]
        apply env.codeProbe_fits es h _ _ _ localQ d B hL hd hloc hv ee _ fw hdeep
        intro i
        apply price (show l+1 ≤ States.Mass.depth N by omega)
        apply market_box D R G l es raw h hh _ _
        exact Nat.add_le_add_right (Nat.add_le_add_left (mass_vertex_size hN l (by omega)) ne) 1
      · rw [prepare_final_spec es w h prior (Nat.le_of_not_gt hj)]
        apply env.codeFinal_fits _ _ hv ee _ hdeep
        intro i
        unfold median
        rw [dite_eq_left hr]
        exact price (show l+1 ≤ States.Mass.depth N by omega) ((hx.2 _).1 i)
    · exact ih (l+1) (by omega) (.extend path y (vertexDecidableEq N l)) (h.push l y) _ _
        (history_push_zero_tail h y hz) ⟨hp, fun i => (hyr i).mono hn⟩
        (historyBox_push (priceMax_mono R G hG (Nat.le_succ _)) hh hyr) (hx.1.2 j)

end Envelope
end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
