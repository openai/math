import OAI.Computability.VPVNP.PairShrinkJobExterior
import OAI.Computability.VPVNP.PairSimulationShrinkRowAction

/-! # Exterior scratch of a complete shrinking resident occurrence -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif MotifEntry
open MotifBlocks MotifGrid MotifConversion NetworkKernel CompressorRecords
open CompressorRecords.ShrinkSlots NodeArguments ShrinkMapImage.Registers MapResidentRows

variable {w g packetEnd endAddr t n limit : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K}
variable (B : S.Templates) (ord : B.Entry → Fin t) (i : Fin S.steps)
local notation "degree" => slotDegree S
local notation "family" => ShrinkVertexImage.matrixFamily B ord i
local notation "gathers" => ShrinkVertexImage.gatherFamily B ord i
variable (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (sel : X.ShrinkSelection B.shrink)
variable (m : X.packingData.Motif) (party : Fin 6)
variable (J : Job X B.shrink (S.shrink i) sel m party w)
private noncomputable local instance routedBaseDecidable : DecidableEq X.Base := Classical.decEq _
local notation "BW" => ShrinkPreparedCall.widthsDemand X m
local notation "idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)
local notation "cd" => ShrinkCallDemandCells.cdBase X m J.arena J.nodes
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel))
  (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) m party))
local notation "call" => Job.entryInput B X (S.shrink i) sel m party J hidden
local notation "L" => MapHandlerOperand.layout family demandMass_pos call
variable (ok : ShrinkCallFields.Fits (w := w) (n := n) (limit := limit) (t := t)
  (u := repetitions B.shrink (ShrinkPreparedCall.widthsDemand X m)) B.shrink
  (ShrinkPreparedCall.widthsDemand X m) (sel m).val J.scratch (ShrinkMotifOrder.stateNumber X m).val
  (ShrinkCallDemandCells.cdBase X m J.arena J.nodes))
local notation "W" => Job.mapWorkspace B degree ord X (S.shrink i) sel m party J hidden ok
variable (hw : MapConstants.widthThreshold B.shrink ≤ w)
variable (P : Fin 5 → Word w) (mem : Memory w) (site : Site X) (level term : Word w)
variable {side : Bool} (src : MapRowSource X sel side mem level term)
variable (row : Fin (order X side site).length)
local notation "st" => rowOrdinalWord (w := w) (a := S.degreeExponent i.castSucc) (g := g)
  X side site row

set_option maxHeartbeats 2000000 in
-- The scheduled row, party input and gathered output share a dependent job index.
/-- The route adds events and passes the gathered map's scratch on to the
next action. All its exterior cells agree with the incoming logical scratch. -/
theorem Job.routed_preserves (saved : DFS.Scratch w endAddr)
    {baseline : Word w → Word w} (packets : J.Packets packetEnd baseline)
    (histEnd : J.scratch.hist + t ≤ J.scratch.hidden)
    {T : IncidenceDirectory w} {origin : ℕ}
    (old : J.OldPublished (ShrinkCallABI.operands degree) P st mem level T origin)
    {events : List (Event w)} {out : DFS.Scratch w endAddr}
    (got : rowAction (g := g) (ready := S.shrink i) (side := side) (jobMotif := m)
      family gathers X sel site mem level term src row call J hw P W saved =
      some (events, out)) :
    ∀ q : Word w, q.val < J.scratch.staging →
      (q.val < J.scratch.hist ∨ J.scratch.hist + t ≤ q.val) →
        rawScratch out q = rawScratch saved q := by
  unfold rowAction at got
  obtain ⟨⟨trace, last⟩, raw, pair⟩ := Option.map_eq_some_iff.mp got
  have same : last = out := (Prod.mk.inj pair).2
  rw [← same]
  exact Job.gathered_preserves B ord i X sel m party J hidden ok hw P st mem saved
    packets histEnd old raw

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
