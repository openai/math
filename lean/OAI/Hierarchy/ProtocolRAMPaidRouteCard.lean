import OAI.Hierarchy.ProtocolRAMCoreSpillRoom

namespace OAI
/-! # The additional paired route header covers whole spills and each chronological feed lane -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open scoped BigOperators Classical
variable {z W k : ℕ}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "r" => Fintype.card (Slots z D k)

theorem early_positions_le_card (p : Recipes) (x : Source) (S : PurchaseSampler) (attempts : ℕ)
    (o : Orders z D k) (occ tag : Bank) :
    (earlyTraversal p x S z W k attempts o occ tag).positions≤r := by
  let ix (i : Fin (∑ j,arity (o.core.symm j))) : Slots z D k := .inl ((corePrefix o).symm i)
  have injective : Function.Injective ix := fun _ _ h=>(corePrefix o).symm.injective (Sum.inl.inj h)
  change (∑ j, arity (o.core.symm j)) ≤ Fintype.card (Slots z D k)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective ix injective

theorem lane_positions_le_card (l : Lane N k) : laneWidth l*2^z≤r := by
  cases l with
  | none =>
    let ix (v : Fin (2*N+1) × Fin (2^z)) : Slots z D k := .inl ⟨.inl v.2,v.1⟩
    have unique : Function.Injective ix := by
      rintro ⟨i,u⟩ ⟨j,v⟩ eq
      cases eq
      rfl
    simpa only [laneWidth,Option.elim_none,Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective ix unique
  | some s =>
    let ix (v : Fin 2 × Fin (2^z)) : Slots z D k := .inl ⟨.inr ((v.2,s.1),s.2),v.1⟩
    have unique : Function.Injective ix := by
      rintro ⟨i,u⟩ ⟨j,v⟩ eq
      cases eq
      rfl
    simpa only [laneWidth,Option.elim_some,Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective ix unique

theorem boundary_positions_le_card (x : Source) (S : PurchaseSampler) (attempts : ℕ) (L : FeedLayout z N k)
    (occ tag : Bank) (c : CommodityColumn) :
    (boundaryTraversal x S z W k attempts L occ tag c).positions≤r :=
  lane_positions_le_card (decodeLane (feedLane L c))

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
