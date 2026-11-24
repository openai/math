import OAI.Computability.VPVNP.PairShrinkCanonicalFieldSupport
import OAI.Computability.VPVNP.PairShrinkSiteFootprint

/-!
# External reads of the shrinking vertex interpreter

For each parent assignment, the canonical parser reads the physical resident
matrix rows in their stored order. Decoding the parent preserves the same
worker read domain and external memory for every successful visit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM DFS Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel CompressorRecords DescriptorSpace ShrinkBlockInputs ShrinkSlots SourceTransport
open LocalHistory NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess
open ShrinkVertexImage ShrinkMapImage.Registers MapResidentRows ResidentMapLoop.Exact
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {i : Fin S.steps} {g w n t : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
  {sel : X.ShrinkSelection B.shrink} {v : MapResidentRows.Site X}
  (site : CanonicalSite B i X sel v w n t) (ord : B.Entry → Fin t)
  {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

private noncomputable local instance canonicalFootBase : DecidableEq X.Base := Classical.decEq _
set_option quotPrecheck false
local notation "side" => selectedLayout X B.shrink sel
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "Old" => Placed (X.packingData.shrinkPlace side ∘ X.packingInputIso.site.symm)
  X.network.Half v

variable (H node : Word w) (saved : Scratch w n) (bits : List Bool)
  (job : VisitPath w n) (tail : List Bool) (room : H.val + 31 < 2 ^ w)
  (beforeHeader : endAddress (BlockProgram.layout B site.workspace.val site.positions
    site.blocks) ≤ H.val)
  (levelEq : site.level = (levelStart (BlockProgram.layout B site.workspace.val site.positions
    site.blocks) site.cur : Word w))
  (payload : CompiledResident.ShrinkPayload B site.workspace site.positions site.blocks n
    site.cur i X sel site.mem)
  (args : site.hiddenArgs = PackedHidden.arguments B i X sel site.workspace site.positions
    site.blocks site.cur n (TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
      (Fintype.card B.Entry)) v)
  (area : site.source.InLevel (BlockProgram.layout B site.workspace.val site.positions
    site.blocks) site.cur)
  (beforeNext : levelStart (BlockProgram.layout B site.workspace.val site.positions site.blocks)
    (site.cur + 1) ≤ H.val)
  (published : MapResidentInputs.Published site.mem site.level
    ((ShrinkResidentLayout.layout X site.source.first).params (a i) true w 3)
    ((ShrinkResidentLayout.layout X site.source.first).params (a i) true w 5) site.term 10)

local notation "domain" => TerminalLink.workerCell H
variable (locator : TraceSupport (TerminalLink.workerCell H)
    ((selectedChildSetup site.publicData site.mem site.levels site.passIndex S.steps i.val
      (a i)).trace node saved))
  (child : ∀ out rest, ChildArguments.reader
    (TerminalLayout.privateRegions (slotDegree S) n site.rowEnd (Fintype.card B.Entry)).arguments
    site.incidence site.mem site.older B.recordLimit site.descriptor node
    ((selectedChildSetup site.publicData site.mem site.levels site.passIndex S.steps i.val
      (a i)).updated node saved) bits = some (out, rest) →
      TraceSupport (TerminalLink.workerCell H) out.trace)

attribute [local irreducible] BlockProgram.layout Compression.ShrinkEnergy.chosenLayout
  TerminalLayout.privateRegions ResidentMapLoop.Exact.scan canonicalBank MapWitness.actions

set_option maxHeartbeats 1600000 in
-- Identify the typed old and absorbed fields used by the actual selected row bank.
include room beforeHeader levelEq payload args area beforeNext published locator child in
/-- Read and write footprints of a returned raw visit with its parent fixed. -/
theorem canonicalFamily_support (parent : (Y).network.Half v)
    (sources : ∀ (old : Old) q, ShrinkSiteBank.RowSources B i X sel site.workspace site.positions
      site.blocks site.cur site.bounds n site.rowEnd site.older site.later v old parent
        site.mem H q)
    (hit : (canonicalFamily site ord f hf parent).read node saved bits = some (job, tail)) :
    TraceSupport (domain) job.trace := by
  refine canonicalFamily_support_of_maps site ord f hf H node saved bits job tail room beforeHeader
    levelEq payload args area beforeNext published locator child parent ?_ hit
  intro xs hs s trace final scan
  dsimp only [canonicalActions, typedActions] at scan
  exact ShrinkSiteBank.scan_footprint site ord parent _ _ H room levelEq area beforeNext
    (sources _) node s scan

set_option maxHeartbeats 1300000 in
-- Recover the stored parent and specialize the fixed-parent parser without altering its trace.
include room beforeHeader levelEq payload args area beforeNext published locator child in
/-- Every successful shrinking visit reads only the worker's cells and returns the
same external memory, before examining any future choice bits. -/
theorem canonicalParent_worker
    (sources : ∀ (parent : (Y).network.Half v) (old : Old) q,
      ShrinkSiteBank.RowSources B i X sel site.workspace site.positions site.blocks site.cur
        site.bounds n site.rowEnd site.older site.later v old parent site.mem H q)
    (hit : (canonicalParent site ord f hf).read node saved bits = some (job, tail)) :
    Reads (domain) job.trace ∧ after site.mem job.trace = site.mem := by
  unfold canonicalParent parentParser at hit
  obtain ⟨parent, _, family⟩ := Option.bind_eq_some_iff.mp hit
  have support := canonicalFamily_support site ord f hf H node saved bits job tail room
    beforeHeader levelEq payload args area beforeNext published locator child parent
    (sources parent) family
  exact ⟨support.1, support.memory site.mem⟩

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
