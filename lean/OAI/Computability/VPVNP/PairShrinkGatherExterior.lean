import OAI.Computability.VPVNP.PairSimulationMapScratchOutside
import OAI.Computability.VPVNP.PairShrinkUpdatedBelow
import OAI.Computability.VPVNP.PairSimulationShrinkGatherMatrix

/-!
# Exterior cells in the pure gather and grouped map

A packet witness fixes the gather intervals for every incoming scratch.
The grouped map's pure update subsequently preserves every word outside
its descriptor, directory, selector, label and histogram arrays.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.ShrinkSlots
open Compression Compression.PackingData Compression.ShrinkMotif
open MotifGrid MotifBlocks MotifConversion MapHandlerOperand
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {t shared w g endAddr packetEnd : ℕ} (F : MapHandlerImage.Family B t shared)
  (G : ShrinkGatherBank.Family F) {X : State G.a (packingLaneBits G.a g)} {δ : ℝ}
  {ready : Ready (2 ^ G.a) (2 * 2 ^ G.a + 1) (2 ^ G.b) δ} {selection : X.ShrinkSelection B}
  {motif : X.packingData.Motif} (I : LocalHistory.EntryInput B)
  (J : ShrinkPartyNative.Job X B ready selection motif I.party w)
  (hw : MapConstants.widthThreshold B ≤ w) (P : Fin 5 → Word w) (st : Word w) (mem : Memory w)
  (W : Workspace F demandMass_pos I) (saved : DFS.Scratch w endAddr)
local notation "key" => Prod.mk (demandGrid B demandMass_pos I.demand) I.party
local notation "L" => F.layout key
local notation "ptr" => PhaseRecipe.Expr.eval P st mem (F.base key)

/-- Every successful pure gathered action has the same exterior frame as its
installed interpreter, even for a scratch that has never been materialized
as a full private-memory configuration. -/
theorem gathered_exterior {baseline : Word w → Word w} (packets : J.Packets packetEnd baseline)
    (fit : (ptr).val + Fintype.card ShrinkCallFields.Arg ≤ 2 ^ w)
    {events : List (Event w)} {out : DFS.Scratch w endAddr}
    (got : gatheredAction F G I J hw P st mem W saved = some (events, out)) :
    ∀ q : Word w, q.val < J.scratch.staging →
      q.val < (ptr).val ∨ (ptr).val + Fintype.card ShrinkCallFields.Arg ≤ q.val →
      MapCallSetup.Outside (L).core ((L).corePC (L).locations) W q →
        NodeArguments.rawScratch out q = NodeArguments.rawScratch saved q := by
  obtain ⟨⟨es, s⟩, raw, eqn⟩ := Option.map_eq_some_iff.mp got
  have upper := (F.action_some_iff demandMass_pos I hw P st mem W endAddr
    (J.updated endAddr saved)).mp raw |>.2.2
  have same : s = out := (Prod.mk.inj eqn).2
  intro q below descriptor outside
  rw [← same, upper]
  exact (MapScratch.upper_outside (L).core (L).args ((L).corePC (L).locations) W ptr _
    F.ordinal endAddr (J.updated endAddr saved) q fit descriptor outside).trans
      (J.updated_below packets saved q below)

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
