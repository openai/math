import OAI.Computability.VPVNP.PairMapSuccessBudget
import OAI.Computability.VPVNP.PairSimulationShrinkRowAction

/-! # Native costs of a selected shrinking map row

The route uses a published resident identifier, a grid identifier and one
layout flag. The private operand-gather trace and the matrix descriptor
writer are charged on the scratch snapshot at this occurrence.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.ShrinkSlots
open Compression Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifGrid MotifBlocks MotifConversion MapResidentRows MapHandlerOperand NodeArguments.ChildScan
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {t shared w g endAddr : ℕ} (F : MapHandlerImage.Family B t shared) (G : ShrinkGatherBank.Family F)
  (X : State G.a (packingLaneBits G.a g)) {δ : ℝ}
  {ready : Ready (2 ^ G.a) (2 * 2 ^ G.a + 1) (2 ^ G.b) δ} (sel : X.ShrinkSelection B)
  (site : Site X) (m : Memory w) (level term : Word w)

/-- Classical decidable equality on the compression state’s base vertices for the cost bounds
of a selected shrinking map row. -/
private noncomputable local instance rowBudgetBase : DecidableEq X.Base := Classical.decEq _
variable {side : Bool} (R : MapRowSource X sel side m level term)
  (i : Fin (order X side site).length)
  (I : LocalHistory.EntryInput B) {jobMotif : X.packingData.Motif}
  (J : ShrinkPartyNative.Job (a := G.a) (b := G.b) (g := g) X B ready sel jobMotif I.party w)
  (hw : MapConstants.widthThreshold B ≤ w) (pub : Fin 5 → Word w)
  (W : Workspace F demandMass_pos I) (saved : DFS.Scratch w endAddr)

local notation "key" => Prod.mk (demandGrid B demandMass_pos I.demand) I.party
local notation "st" => rowOrdinalWord (w := w) (a := G.a) (g := g) X side site i
local notation "gTrace" => J.trace (G.operands (key)) (G.node (key)) pub (st) m

/-- The two finite selector chains are the only variable part of the route. -/
theorem routeEvents_length :
    (routeEvents X sel side site m level term R i).length =
      15 + 2*((demandOrder B.grid.demands).symm (rowGrid (B := B) X side site i)).val +
        2*(entry X side site i).2.val := by
  simp only [routeEvents,List.length_append,List.length_replicate,
    (MapResidentInputs.itemCost ..).1,(ShrinkLayoutBranch.cost ..).1]
  omega

set_option maxHeartbeats 1400000 in
-- The row trace transports the party-indexed gather through the selected matrix handler.
/-- A successful routed gather and matrix, including its concrete writes
to the histogram. The gather trace is the one for this job, with its real
stage-, term- and party-dependent operands. -/
theorem rowAction_cost {es : List (Event w)} {out : DFS.Scratch w endAddr}
    (hit : rowAction F G X sel site m level term R i I J hw pub W saved = some (es, out)) :
    es.length ≤ 15 + 2*Fintype.card B.grid.demands + 12 +
      (gTrace).length + F.clock (key) (repetitions B I.demand) ∧
    countProbes es = 3 + countProbes (gTrace) + F.probes (key) := by
  unfold rowAction at hit
  obtain ⟨⟨front,up⟩,gathered,routed⟩ := Option.map_eq_some_iff.mp hit
  unfold gatheredAction at gathered
  obtain ⟨⟨trace,last⟩,matrix,copied⟩ := Option.map_eq_some_iff.mp gathered
  obtain ⟨_,equal,_⟩ := (F.action_some_iff demandMass_pos I hw pub (st) m W endAddr
    (J.updated endAddr saved)).mp matrix
  rw [← (Prod.mk.inj routed).1,← (Prod.mk.inj copied).1,equal]
  obtain ⟨bound,probes⟩ := F.successEvents_cost demandMass_pos I hw pub (st) m
  have grid := ((demandOrder B.grid.demands).symm (rowGrid (B := B) X side site i)).isLt
  simp only [Finset.length_toList, ← Fintype.card_coe] at grid
  have party := (entry X side site i).2.isLt
  simp only [List.length_append,countProbes_append,routeEvents_length,
    (routeEvents_cost X sel side site m level term R i).1,probes]
  omega

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
