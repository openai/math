import OAI.Computability.VPVNP.PairSimulationShrinkRouteOrdinal
import OAI.Computability.VPVNP.PairSimulationShrinkGatherMatrix
import OAI.Computability.VPVNP.PairSimulationShrinkRouteReads

/-!
# Trace and acceptance of one shrinking resident map row
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
  {p r t shared w g endAddr : ℕ} (F : MapHandlerImage.Family B t shared)
  (G : ShrinkGatherBank.Family F) (S : Registers shared) (pc : GatherAddress F G → Fin p)
  (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (common : Fin shared ↪ Fin r)
  (own : F.PrivateReg ↪ Fin r) (gatherReg : G.PrivateReg ↪ Fin r) (tmp : Fin r) (ret : Fin p)
  (M : Machine w p r 11) (link : GatherLinked F G S pc dfs saved common own gatherReg tmp ret M)
  (mapApart : F.Apart dfs saved common own) (gatherApart : G.Apart dfs saved common gatherReg)
  (X : State G.a (packingLaneBits G.a g)) {δ : ℝ}
  {ready : Ready (2 ^ G.a) (2 * 2 ^ G.a + 1) (2 ^ G.b) δ} (sel : X.ShrinkSelection B)
  (site : Site X) (m : Memory w) (level term : Word w)

private noncomputable local instance rowActionBase : DecidableEq X.Base := Classical.decEq _
variable {side : Bool}

variable (R : MapRowSource X sel side m level term) (i : Fin (order X side site).length)
  (I : LocalHistory.EntryInput B)

local notation "entryPair" => MapResidentRows.entry X side site i
local notation "z" => demandGrid B demandMass_pos I.demand
local notation "key" => Prod.mk (z) I.party
local notation "route" => routeEvents X sel side site m level term R i
local notation "src" => rowCursor X sel side site m level term R i
local notation "reg" => S.headerReg common

variable {jobMotif : X.packingData.Motif}
  (J : ShrinkPartyNative.Job (a := G.a) (b := G.b) (g := g) X B ready sel jobMotif I.party w)
  (hw : MapConstants.widthThreshold B ≤ w) (P : Fin 5 → Word w)
  (W : Workspace F demandMass_pos I) (oldScratch : DFS.Scratch w endAddr)

local notation "st" => rowOrdinalWord (w := w) (a := G.a) (g := g) X side site i

set_option maxHeartbeats 1800000 in
-- The field gather and stored row use the same selected compression indices.
/-- Trace and final scratch for a successful row, including the route to its gather.
A rejected matrix entry yields `none`. -/
noncomputable def rowAction : Option (List (Event w) × DFS.Scratch w endAddr) :=
  (gatheredAction (g := g) F G (X := X) (ready := ready) (selection := sel)
    (motif := jobMotif) I J hw P (st) m W oldScratch).map fun pair ↦ ((route) ++ pair.1, pair.2)

set_option maxHeartbeats 1800000 in
-- Unfold the single dependent row action at its recorded stage and party.
/-- An indexed resident row succeeds exactly when its underlying grouped matrix succeeds. -/
theorem rowAction_isSome :
    (rowAction F G X sel site m level term R i I J hw P W oldScratch).isSome =
      (names F demandMass_pos I).isSome := by
  simp only [rowAction, gatheredAction, Option.isSome_map, MapHandlerImage.Family.action_isSome,
    names]

set_option maxHeartbeats 1800000 in
-- Unfold the single dependent row action at its recorded stage and party.
/-- The dispatch and map add no guesses to a physical operand gather. -/
theorem rowAction_noChoices {es : List (Event w)} {updated : DFS.Scratch w endAddr}
    (quiet : choiceBits (J.trace (G.operands (key)) (G.node (key)) P (st) m) = [])
    (got : rowAction F G X sel site m level term R i I J hw P W oldScratch = some (es, updated)) :
    choiceBits es = [] := by
  unfold rowAction at got
  obtain ⟨⟨mid, last⟩, gathered, pair⟩ := Option.map_eq_some_iff.mp got
  unfold gatheredAction at gathered
  obtain ⟨⟨trace, final⟩, raw, inner⟩ := Option.map_eq_some_iff.mp gathered
  have clean := F.action_noChoices demandMass_pos I hw P (st) m W endAddr
    (J.updated endAddr oldScratch) raw
  rw [← (Prod.mk.inj pair).1, ← (Prod.mk.inj inner).1]
  simp only [PrimedInputRAM.Flow.choiceBits_append,
    (routeEvents_cost X sel side site m level term R i).2, quiet, clean, List.nil_append]

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
