import OAI.Hierarchy.ProtocolRAMCoreSpillRoom
import OAI.Hierarchy.ProtocolRAMCoreRouteCost

namespace OAI
/-! # Uniform original spills and boundary-feed operand charges -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open scoped Classical
variable {z W k attempts : ℕ}

def laneOperandWork (N k attempts : ℕ) :=
  let code:=63+8*ReportSockets.copies k attempts
  max (blockWork code (2*N+1)) (max (blockWork code 2) (max (blockWork 2 (2*N+1)) (blockWork 2 2)))

def spillOperandWork (N k attempts : ℕ) :=
  max (6*operationBound N k attempts+12) (laneOperandWork N k attempts)

local notation "N" => Stages z (2^W)

theorem early_work (p : Recipes) (x : Source) (S : PurchaseSampler) (o : Orders z (2^W) k)
    (owner parity : Bank) :
    let t:=earlyTraversal p x S z W k attempts o owner parity
    t.edge.work≤ spillOperandWork N k attempts ∧ t.sourceRow.work≤ spillOperandWork N k attempts := by
  intro t
  have first:=index_work (S:=S) (z:=z) (W:=W) (k:=k) (attempts:=attempts) p x
  have sub:=CatalogueRows.substitute_work (indexWord p x S z W k attempts) evenPosition
  change _≤(indexWord p x S z W k attempts).work*(5+1) at sub
  constructor
  · apply le_trans _ (le_max_left ..)
    change ((indexWord p x S z W k attempts).atRow evenPosition).work≤6*operationBound N k attempts+12
    omega
  · apply le_trans _ (le_max_left ..)
    change 12≤6*operationBound N k attempts+12
    omega

theorem lane_work (x : Source) (S : PurchaseSampler) (l : Lane N k) (owner parity : Bank) :
    let t:=laneTraversal x S z W k attempts l owner parity
    t.edge.work≤laneOperandWork N k attempts ∧ t.sourceRow.work≤laneOperandWork N k attempts := by
  intro t
  let code:=63+8*ReportSockets.copies k attempts
  have edge : t.edge.work≤blockWork code (laneWidth l) := blocks_work (2^z) _ code _
    (fun j=>operator_work (S:=S) (z:=z) (W:=W) (k:=k) (attempts:=attempts) x (laneAction l j))
  have row : t.sourceRow.work≤blockWork 2 (laneWidth l) := blocks_work (2^z) _ 2 _ (fun _=>le_rfl)
  cases l with
  | none => exact ⟨edge.trans (le_max_left ..),row.trans ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))⟩
  | some a => exact ⟨edge.trans ((le_max_left ..).trans (le_max_right ..)),
      row.trans ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))⟩

theorem boundary_work (x : Source) (S : PurchaseSampler) (L : FeedLayout z N k) (owner parity : Bank) (c : CommodityColumn) :
    let t:=boundaryTraversal x S z W k attempts L owner parity c
    t.edge.work≤ spillOperandWork N k attempts ∧ t.sourceRow.work≤ spillOperandWork N k attempts := by
  intro t
  have source:=lane_work (attempts:=attempts) x S (decodeLane (feedLane L c)) owner parity
  exact ⟨source.1.trans (le_max_right ..),source.2.trans (le_max_right ..)⟩

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
