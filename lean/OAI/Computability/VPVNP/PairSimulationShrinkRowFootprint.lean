import OAI.Computability.VPVNP.PairSimulationShrinkRowAction
import OAI.Computability.VPVNP.PairShrinkGatherQuiet

/-!
# Reads and writes of a complete selected shrinking row
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.ShrinkSlots SourceTransport
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

private noncomputable local instance rowFootprintBase : DecidableEq X.Base := Classical.decEq _
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

set_option maxHeartbeats 1600000 in
-- Match the physical writer and gather traces to the dependent selected job.
/-- The returned event list consists of the route, gather and successful matrix traces. -/
theorem rowAction_trace {es : List (Event w)} {updated : DFS.Scratch w endAddr}
    (got : rowAction F G X sel site m level term R i I J hw P W oldScratch = some (es, updated)) :
    es = (route) ++ (J.trace (G.operands (key)) (G.node (key)) P (st) m ++
      F.successEvents demandMass_pos I hw P (st) m) := by
  unfold rowAction at got
  obtain ⟨⟨mid, last⟩, gathered, pair⟩ := Option.map_eq_some_iff.mp got
  unfold gatheredAction at gathered
  obtain ⟨⟨trace, final⟩, raw, inner⟩ := Option.map_eq_some_iff.mp gathered
  have known := (F.action_some_iff demandMass_pos I hw P (st) m W endAddr
    (J.updated endAddr oldScratch)).mp raw
  exact (Prod.mk.inj pair).1.symm.trans (congrArg (fun xs ↦ (route) ++ xs)
    ((Prod.mk.inj inner).1.symm.trans (congrArg (fun xs ↦ _ ++ xs) known.2.1)))

set_option maxHeartbeats 1600000 in
-- The exact row action specializes its geometric footprint to the live source words.
/-- A successful shrinking row has the concrete external read domain and never writes. -/
theorem rowAction_footprint {es : List (Event w)} {updated : DFS.Scratch w endAddr}
    (allow : ℕ → Prop) (idSafe : allow (src))
    (termSafe : allow (term.val + (ordinal X (entryPair).1).val * 10))
    (layoutSafe : allow (level + 38).val)
    (gather : Reads allow (J.trace (G.operands (key)) (G.node (key)) P (st) m))
    (baseSafe : (F.base (key)).ReadsFrom allow P (st) m)
    (fieldSafe : ∀ a, (F.field (key) a).ReadsFrom allow P (st) m)
    (got : rowAction F G X sel site m level term R i I J hw P W oldScratch = some (es, updated)) :
    Reads allow es ∧ Writes (fun _ ↦ False) es := by
  rw [rowAction_trace F G X sel site m level term R i I J hw P W oldScratch got]
  constructor
  · exact TerminalFootprint.reads_append
      (routeEvents_reads X sel side site m level term R i allow idSafe termSafe layoutSafe)
      (TerminalFootprint.reads_append gather
        (F.successEvents_readsFrom demandMass_pos I hw P (st) m allow baseSafe fieldSafe))
  · intro a v hit
    rcases List.mem_append.mp hit with routeHit | tail
    · exact routeEvents_noWrites X sel side site m level term R i a v routeHit
    rcases List.mem_append.mp tail with gatherHit | matrixHit
    · exact J.trace_noWrites (G.operands (key)) (G.node (key)) P (st) m a v gatherHit
    · exact F.successEvents_noWrites demandMass_pos I hw P (st) m a v matrixHit

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
