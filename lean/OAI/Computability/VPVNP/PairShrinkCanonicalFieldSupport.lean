import OAI.Computability.VPVNP.PairShrinkVisitFootprint
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
import OAI.Computability.VPVNP.PairShrinkSiteRouteBounds
import OAI.Computability.VPVNP.PairShrinkSiteHiddenFootprint
import OAI.Computability.VPVNP.PairShrinkHiddenNoWrites
import OAI.Computability.VPVNP.PairShrinkHiddenSetupNoWrites

/-!
# External memory of a canonical shrinking visit

The locator and child reader enter the packed row. All remaining reads come
from that row's old level, stored term directory, hidden fields, and selected
matrix operands. The parent decoder and the scratch and histogram updates
take place in private memory. A returned visit therefore preserves external
memory on its entire choice stream, independently of later visits.
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

set_option quotPrecheck false
local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "D" => BlockProgram.layout B site.workspace.val site.positions site.blocks
local notation "childLoad" => selectedChildSetup site.publicData site.mem site.levels site.passIndex
  S.steps i.val (a i)
local notation "hiddenLoad" => physicalHiddenSetup B.shrink.selectorBits (hiddenStride i)
  site.level.val site.mem
local notation "mapLoad" => mapStartSetup site.mem site.level (Fin.val (siteIndex X v) : Word w)
local notation "seed" => ShrinkHiddenSlots.rows X side widths v site.seed

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

/-- A successful hidden-field parse emits only reads and private events. -/
theorem hiddenRead_noWrites {n w : ℕ} {a : Args w} {m : Memory w} {shape : List Row}
    {node : Word w} {s : Scratch w n} {tape rest : List Bool} {out : Outcome w n (List Row)}
    (hit : hiddenReader a m shape node s tape = some (out, rest)) :
    Writes (fun _ ↦ False) out.trace := by
  rw [(ShrinkNodeCost.hidden_trace a m shape node s tape rest out hit).1]
  exact ShrinkHiddenGuess.events_noWrites a m out.value

attribute [local irreducible] BlockProgram.layout Compression.ShrinkEnergy.chosenLayout
  TerminalLayout.privateRegions
  ResidentMapLoop.Exact.scan canonicalActions canonicalBank hiddenReader ShrinkHiddenSlots.rows

set_option maxHeartbeats 1600000 in
-- Identify the typed old and absorbed fields used by the actual selected row bank.
include room beforeHeader levelEq payload args area beforeNext published locator child in
/-- Read and write footprints of a returned raw visit with its parent fixed. -/
theorem canonicalFamily_support_of_maps (parent : (Y).network.Half v)
    (bank : ∀ xs hs s trace final, ResidentMapLoop.Exact.scan node
      (canonicalActions site ord f hf parent xs hs) s = some (trace, final) →
      TraceSupport (domain) trace)
    (hit : (canonicalFamily site ord f hf parent).read node saved bits = some (job, tail)) :
    TraceSupport (domain) job.trace := by
  unfold canonicalFamily at hit
  refine visit_footprint (n := n) (X := X) (regions).arguments site.incidence site.mem site.older
    B.recordLimit site.descriptor (fun _ ↦ site.hiddenArgs) (fun _ ↦ (seed))
    (canonicalActions site ord f hf parent) (childLoad) (fun _ ↦ (hiddenLoad))
    (fun _ _ ↦ (mapLoad)) node (domain) saved bits tail job locator child
    (fun _ s ↦ ⟨site.hiddenSetup_reads H room beforeHeader levelEq node s,
      physicalHiddenSetup_noWrites B.shrink.selectorBits (hiddenStride i) site.level.val
        site.mem node s⟩) ?_ ?_ bank hit
  · intro _ s b out rest read
    have hidden := CanonicalSite.hiddenReader_reads (g := g) (X := X) (sel := sel) site H
      room beforeHeader payload args (node := node) (saved := s) (bs := b) (tail := rest)
      (out := out) read
    exact ⟨hidden, hiddenRead_noWrites (a := site.hiddenArgs) (m := site.mem) (shape := (seed))
      (node := node) (s := s) (tape := b) (rest := rest) (out := out) read⟩
  · intro _ _ s
    exact ⟨ShrinkSiteBank.mapStart_worker (g := g) (X := X) (L := D) (cur := site.cur)
      B i site.source v H area beforeNext room published,
      mapStartSetup_noWrites site.mem site.level ((siteIndex X v).val : Word w) node s⟩

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
