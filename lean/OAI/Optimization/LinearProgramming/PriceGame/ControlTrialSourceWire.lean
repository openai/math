import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialResultWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingState
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSourceWeight
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSourceMarks
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionWeightSize
import OAI.Optimization.LinearProgramming.PriceGame.TrialCachedGrid

/-! Close the native stack's record invariants on the actual nested source execution. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire
namespace Source

open Trial TrialExecution States.Mass

variable {N ne r R D Q L B d : ℕ} {env : Envelope} {es : Fin ne → Expert N}

/-- Numeric limits consumed by the packet encoder. Each parameter is shared by all nodes. -/
structure Limits (env : Envelope) (r R D L B d : ℕ) (es : Fin ne → Expert N) : Prop where
  nonempty : 0 < N
  den : 0 < D
  localDen : 0 < L
  localBits : L ≤ 2^d
  raw : RawBox D R es
  depth : States.Mass.depth N ≤ env.depth
  vertices : 2*N^2 ≤ env.vertices
  experts : ne ≤ env.experts
  price : 2*trialPriceBits N ne R D+4 ≤ env.width
  gain : 2*(3+2*(B+d))+4 ≤ env.width
  score : (2*N)^274 ≤ env.score
  log : ∀ k ≤ States.Mass.depth N, probeLogBound r k ≤ env.logSize

structure NodeGood (env : Envelope) (r R D Q L B : ℕ) (es : Fin ne → Expert N)
    (k : ℕ) (c : SourceNode N ne) : Prop where
  level : c.level+k ≤ depth N
  path : c.path.pricesSatisfy (PriceBox D (Complexity.priceMax R (trialMarketSize N ne) (depth N)))
  prior : HistoryBox D (Complexity.priceMax R (trialMarketSize N ne) c.level) c.level c.history
  arrays : c.WeightArrays env r R es Q L B k

private theorem vertex_limit (lim : Limits env r R D L B d es) (j : ℕ) (hj : j ≤ depth N) :
    N*2^j ≤ 2*N^2 := by
  simpa [card_vertices,Nat.mul_comm] using card_vertices_le N j lim.nonempty hj

private theorem market_limit (lim : Limits env r R D L B d es) (j : ℕ) (hj : j ≤ depth N) :
    ne+N*2^j+1 ≤ trialMarketSize N ne :=
  Nat.add_le_add_right (Nat.add_le_add_left (vertex_limit lim j hj) ne) 1

private theorem width_of_box (lim : Limits env r R D L B d es) {q : ℚ}
    (hq : PriceBox D (Complexity.priceMax R (trialMarketSize N ne) (depth N)) q) :
    2*RAM.ratBits q+4 ≤ env.width :=
  (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (priceBox_ratBits lim.den hq)) 4).trans lim.price

private theorem score_width (lim : Limits env r R D L B d es) {l : ℕ} {w : Weights ne}
    (out : Certified (N:=N) (r:=r) (l:=l) w) (ht : out.val.trace.height ≤ depth N) (e : Fin ne) :
    out.val.scores[e].bits.length ≤ env.score :=
  (nat_le_self _).trans ((certified_score_le_public w out lim.nonempty
    (by simpa only [States.Mass.depth,Nat.log2_eq_log_two] using ht) e).trans lim.score)

theorem output_fits {k : ℕ} {c : SourceNode N ne} (lim : Limits env r R D L B d es)
    (h : NodeGood env r R D Q L B es k c) {tr out} (run : Emits (c.exec r R es k) tr out) :
    env.ResultFits (codeOutput out.val) := by
  let solve := marketSolverAtCommonWeightUnit es
  have box := run.of_guarded (execute_price_grid r D R (trialMarketSize N ne) (depth N) (Nat.succ_pos _)
    es lim.raw (market_limit lim) k c.level h.level c.path h.path c.history h.prior c.weights c.nonneg)
  have hs := run.of_guarded (execute_all_trace_height r R es solve k c.level c.path c.history c.weights c.nonneg).guarded
  have hl := run.of_guarded (execute_log_length r R es solve k c.level c.path c.history c.weights c.nonneg).guarded
  have hd := run.of_guarded (execute_log_depth r R (depth N) es solve k c.level h.level c.path c.history
    c.weights c.nonneg).guarded
  have le := h.level
  apply env.codeOutput_fits_of_grid D R out.val lim.nonempty lim.den (by omega) lim.depth lim.vertices
    lim.experts lim.price box (score_width lim out (hs.trans (by omega : k ≤ depth N))) (hl.trans (lim.log k (by omega))) hd

theorem cache_at {k j : ℕ} {c : SourceNode N ne} (lim : Limits env r R D L B d es)
    (h : NodeGood env r R D Q L B es (k+1) c) (p : SeenPrefix r R es c k j) :
    ∀ i : Fin j, CachedCallBox D (Complexity.priceMax R (trialMarketSize N ne) (c.level+1))
      (Complexity.priceMax R (trialMarketSize N ne) (depth N)) (depth N) k (p.calls.val i) := by
  have hl := h.level
  exact p.observed.of_guarded (cachedPrefix_guarded r D R (trialMarketSize N ne) (depth N) (Nat.succ_pos _)
    es lim.raw (market_limit lim) k c.level (by omega) c.path h.path c.history h.prior c.weights c.nonneg j)

private theorem completed_at {k j : ℕ} {c : SourceNode N ne} (lim : Limits env r R D L B d es)
    (h : NodeGood env r R D Q L B es (k+1) c) (hj : j ≤ 2*r) (p : SeenPrefix r R es c k j) :
    ∀ row ∈ c.rows p.calls.val, env.CompletedFits row := by
  intro row mem
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
  let call := p.calls.val i
  have ⟨bc,childPrices,lengths,levels,heights⟩ := cache_at lim h p i
  let w := incomingDeep es c.weights (TrialExecution.«prefix» p.calls.val i)
  let ch : Certified (N:=N) (r:=r) (l:=c.level+1) w := ⟨call.child,(p.calls.property i).admissible⟩
  have le := h.level
  have hw := h.arrays.gains lim.localDen lim.localBits j hj p.observed i
  have hu := priceMax_mono R (trialMarketSize N ne) (Nat.succ_pos _) (show c.level+1 ≤ depth N by omega)
  apply env.codeCall_fits call ((vertex_limit lim _ (by omega)).trans lim.vertices) lim.experts
    (fun u => width_of_box lim ((bc.1 u).mono hu)) (fun u => width_of_box lim (bc.2.1 u))
    (fun e => (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw e)) 4).trans lim.gain)
  exact env.codeOutput_fits_of_grid D R call.child lim.nonempty lim.den (by omega) lim.depth lim.vertices
    lim.experts lim.price ⟨childPrices,bc.2.2⟩ (score_width lim ch (heights.trans (by omega : k ≤ depth N)))
    (lengths.trans (lim.log k (by omega))) levels

private theorem nextGood {k j : ℕ} {c : SourceNode N ne} (lim : Limits env r R D L B d es)
    (h : NodeGood env r R D Q L B es (k+1) c) (hj : j < 2*r) (p : SeenPrefix r R es c k j) :
    NodeGood env r R D Q L B es k (c.next es p.calls.val) := by
  let G := trialMarketSize N ne
  have lev := h.level
  have hy (i) : PriceBox D (Complexity.priceMax R G (c.level+1)) (c.selectedPrice es p.calls.val i) := by
    unfold SourceNode.selectedPrice
    split
    · exact market_box D R G c.level es lim.raw c.history h.prior _ _ (market_limit lim _ (by omega)) i
    · rename_i finalStage
      exact median_box (fun z => (cache_at lim h p ⟨z.val,z.isLt.trans_le (not_lt.mp finalStage)⟩).1.1 i)
  have monot := priceMax_mono R G (show 0<G from Nat.succ_pos _)
  exact ⟨by change (c.level+1)+k ≤ depth N; omega,
    ⟨h.path,fun i => (hy i).mono (monot (by omega))⟩,
    historyBox_push (monot (Nat.le_succ _)) h.prior hy,
    (h.arrays.at_prefix hj p.observed).2.1⟩

private theorem frame_at {k j : ℕ} {c : SourceNode N ne} (lim : Limits env r R D L B d es)
    (h : NodeGood env r R D Q L B es (k+1) c) (hj : j < 2*r) (p : SeenPrefix r R es c k j) :
    env.FramePayload (c.frame R es k (2*r-(j+1)) p.calls.val) :=
  ⟨h.arrays.input, completed_at lim h hj.le p, (h.arrays.at_prefix hj p.observed).1⟩

/-- Concrete marks on the enter/schedule/call/feedback/return phases of the exact machine. -/
def sourceMarks (lim : Limits env r R D L B d es) (Q : ℕ) :
    SourceMarks r R es env.PCPayload env.FramePayload where
  NodeGood := NodeGood env r R D Q L B es
  enter h := h.arrays.input
  leaf {c} h := by
    change env.ResultFits (leafPacket N R ne c.input)
    rw [show leafPacket N R ne c.input = _ from leafPacket_spec r R c.level c.history c.weights]
    exact output_fits lim h (.pure _)
  schedule h hj p := ⟨h.arrays.input,completed_at lim h hj p⟩
  frame h hj p := frame_at lim h hj p
  child h hj p := nextGood lim h hj p
  feedback := by
    intro k c j h hj p tr ch run tape
    exact ⟨frame_at lim h hj p,output_fits lim (nextGood lim h hj p) run⟩
  assembled {k c} h p := by
    change env.ResultFits (assemblePacketSized N r ne (List.ofFn fun e => packExpert (es e))
      (codeInput c.level c.history c.weights) (List.ofFn fun j => codeCall (p.calls.val j)))
    rw [assemblePacket_spec es c.history c.weights p.calls]
    exact output_fits lim h (p.observed.map (f := assemble es c.history c.weights))

end Source
end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
