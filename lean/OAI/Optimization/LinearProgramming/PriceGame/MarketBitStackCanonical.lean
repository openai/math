import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineEncoding
import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackCanonicalCore
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineGraph
import OAI.Optimization.LinearProgramming.PriceGame.MarketCompute

/-! A fresh zero-terminal Bellman table computes the final dummy-normalized prices
from the optimal integral flow. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace GridMachine
namespace Readout

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.PriceGame.Market.Graph Augment Augment.Machine Potentials Table

variable {m g : ℕ}

theorem zeroRows_packEnv (I : Augment.Input m g) (D : ℕ) (s : Augment.State m g) :
    zeroRows (packEnv I D s) =
      FlowMachine.Rows.encodeRaw (I.network s) (I.decideAcceptance s) D 0 := by
  simp [zeroRows,packEnv,FlowMachine.Rows.encodeRaw,List.map_ofFn,Function.comp_def,Grid.scaleInput]

theorem goodAddresses_packEnv (I : Augment.Input m g) (D : ℕ) (s : Augment.State m g) :
    goodAddresses (packEnv I D s) = List.ofFn (fun i : Fin g => m+(i.val+1)) := by
  simp [goodAddresses,packEnv,FlowMachine.Rows.encodeRaw,map_range_fin]

/-- The rational price word agrees with every coordinate of the algorithm's canonical
price vector for the supplied flow, regardless of the old dual-bank values. -/
theorem canonical_eq (I : Augment.Input m g) (D : ℕ) (s : Augment.State m g) (hD : 0 < D)
    (hc : ∀ e j, I.accepts e j → NumberBounds.OnGrid D (I.intercept e j)) :
    canonical (packEnv I D s) = List.ofFn (pricesFromFlow I.positive I.available I.intercept s.flow) := by
  let n := I.network s
  let dec := I.decideAcceptance s
  let ix := vertexIndex n
  let out := outgoing n dec
  let K := m+(g+1)-1
  let : ∀ a b : Vertex n, Fintype (a ⟶ b) := n.enumEdges dec
  have eg {a b : Vertex n} (e : a ⟶ b) : NumberBounds.OnGrid D (n.weight e) := n.weight_integral D hc e
  have zeg (v : Vertex n) : NumberBounds.OnGrid D ((0 : Vertex n → ℚ) v) := NumberBounds.grid_zero D
  have run := Table.solve_serializes ix n.weight 0 out (@FlowMachine.arcID m g n) D hD eg zeg K
  rw [canonical,zeroRows_packEnv,FlowMachine.Rows.make_eq_serializeGraph,horizon_pack,goodAddresses_packEnv,run,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  let p := fun v : Vertex n => Layer.lookup ix (plans ix n.weight 0 out K) v
  let vals := serializeValues ix n.weight 0 (@FlowMachine.arcID m g n) D p
  change normalized ((((D : ℤ).toNat,vals),(List.ofFn I.positive).length),m+(j.val+1)) = _
  rw [Int.toNat_natCast,List.length_ofFn]
  have ad : (ix (.opt none)).val = m := by simp [ix]
  have ag : (ix (.opt (some j))).val = m+(j.val+1) := by simp [ix]
  have eqPrice := (price_of_potential ix n.weight (@FlowMachine.arcID m g n) D hD eg out
    (mem_outgoing n dec) (.opt none) (.opt (some j))).trans
      (pricesFromFlow_eq_potential I.positive I.available I.intercept s.flow j).symm
  simpa only [ad,ag] using eqPrice

end Readout
end GridMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
