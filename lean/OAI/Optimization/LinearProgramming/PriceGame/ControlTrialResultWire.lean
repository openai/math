import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialWeightWire
import OAI.Optimization.LinearProgramming.PriceGame.TrialWireBound

/-! Actual return and completed-call records stored at every nested trial node. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open States.Mass TrialExecution Trial

variable {N ne r l : ℕ}

theorem Envelope.packProbe_fits (env : Envelope) (p : Probe N) (hd : p.level ≤ env.depth)
    (vertices : ∀ j ≤ p.level, N*2^j ≤ env.vertices)
    (price : ∀ i, 2*RAM.ratBits (p.prices i)+4 ≤ env.width)
    (prior : ∀ j < p.level, ∀ i, 2*RAM.ratBits (p.history j i)+4 ≤ env.width) :
    env.ProbeFits (packProbe p) := by
  refine ⟨hd,actualTable_fit _ (vertices _ le_rfl) price,?_,?_⟩
  · simpa [packProbe,packHistory] using hd
  · intro row hrow
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    exact actualTable_fit _ (vertices j j.isLt.le) (prior j j.isLt)

theorem Envelope.codeOutput_fits (env : Envelope) (out : Output N ne r l)
    (vertexCount : N*2^l ≤ env.vertices) (count : ne ≤ env.experts)
    (prices : ∀ i, 2*RAM.ratBits (out.prices i)+4 ≤ env.width)
    (scores : ∀ e : Fin ne, out.scores[e].bits.length ≤ env.score)
    (logs : out.log.length ≤ env.logSize)
    (rows : ∀ p ∈ out.log, env.ProbeFits (packProbe p)) : env.ResultFits (codeOutput out) := by
  refine ⟨actualTable_fit _ vertexCount prices,by simpa [codeOutput] using count,?_,
    by simpa [codeOutput] using logs,?_⟩
  · intro n hn
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hn
    exact scores ⟨j,by simpa [codeOutput] using hj⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact rows q hq

theorem Envelope.codeCall_fits (env : Envelope) (c : Call N ne r l)
    (vertexCount : N*2^l ≤ env.vertices) (count : ne ≤ env.experts)
    (base : ∀ i, 2*RAM.ratBits (c.data.baseline i)+4 ≤ env.width)
    (mapped : ∀ i, 2*RAM.ratBits (c.data.mapped i)+4 ≤ env.width)
    (gain : ∀ e : Fin ne, 2*RAM.ratBits c.data.gain[e]+4 ≤ env.width)
    (child : env.ResultFits (codeOutput c.child)) : env.CompletedFits (codeCall c) := by
  refine ⟨actualTable_fit _ vertexCount base,actualTable_fit _ vertexCount mapped,⟨?_,?_⟩,child⟩
  · simpa [codeCall] using count
  · intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hq
    exact (rat_le_machine _).trans (gain ⟨j,by simpa [codeCall] using hj⟩)

private theorem vertices_le (hN : 0 < N) (j : ℕ) (hj : j ≤ States.Mass.depth N) :
    N*2^j ≤ 2*N^2 := by
  simpa [card_vertices,Nat.mul_comm] using card_vertices_le N j hN hj

/-- Convert the actual recursive output price-grid and log-height invariants in one pass.
Each probe carries precisely the earlier rows selected by its level. -/
theorem Envelope.codeOutput_fits_of_grid (env : Envelope) (D R : ℕ) (out : Output N ne r l)
    (hN : 0 < N) (hD : 0 < D) (hl : l ≤ States.Mass.depth N) (depthBound : States.Mass.depth N ≤ env.depth)
    (vertices : 2*N^2 ≤ env.vertices) (count : ne ≤ env.experts)
    (width : 2*trialPriceBits N ne R D+4 ≤ env.width)
    (box : OutputBox D (Complexity.priceMax R (trialMarketSize N ne) (States.Mass.depth N)) out)
    (scores : ∀ e : Fin ne, out.scores[e].bits.length ≤ env.score)
    (logs : out.log.length ≤ env.logSize) (levels : ∀ p ∈ out.log, p.level < States.Mass.depth N) :
    env.ResultFits (codeOutput out) := by
  have hq (q : ℚ) (hq : PriceBox D (Complexity.priceMax R (trialMarketSize N ne) (States.Mass.depth N)) q) :
      2*RAM.ratBits q+4 ≤ env.width :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (priceBox_ratBits hD hq)) 4).trans width
  refine env.codeOutput_fits out ((vertices_le hN l hl).trans vertices) count
    (fun i => hq _ (box.1 i)) scores logs ?_
  intro p hp
  have lev := levels p hp
  obtain ⟨hp₁,hp₂⟩ := box.2 p hp
  exact env.packProbe_fits p (lev.le.trans depthBound)
    (fun j hj => (vertices_le hN j (hj.trans lev.le)).trans vertices)
    (fun i => hq _ (hp₁ i)) (fun j hj i => hq _ (hp₂ j hj i))

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
