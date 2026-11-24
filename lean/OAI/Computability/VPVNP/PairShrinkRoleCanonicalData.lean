import OAI.Computability.VPVNP.PairShrinkCanonicalSite
import OAI.Computability.VPVNP.PairShrinkRoleMapStart
import OAI.Computability.VPVNP.PairShrinkPackedPackets
import OAI.Computability.VPVNP.PairShrinkRoleChildTyped
import OAI.Computability.VPVNP.PairShrinkSiteSources
import OAI.Computability.VPVNP.PairShrinkVertexPlacement

/-!
# Published inputs for one canonical shrinking visit

The site data consist of its header words, field and map directories,
position in the selected schedule, and the bounds of its private arrays.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel CompressorRecords DescriptorSpace LocalHistory ShrinkBlockInputs ShrinkSlots
open VertexImage ShrinkVertexImage ShrinkMapImage.Registers MapResidentRows
open TraversalRows TraversalRoles TraversalControllerInputs NodeArguments NodeArguments.ChildScan
open ShrinkHiddenGuess
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {i : Fin S.steps} {g w n p r : ℕ} {Z : State (a i) (packingLaneBits (a i) g)}
  {sel : SelectedScore.Selection B Z} {v : MapResidentRows.Site Z}
  (site : CanonicalSite B i Z sel v w n (Fintype.card B.Entry))
  (M : Machine w p r 11)
  {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
  {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
  (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)
  (j : Fin (executeLevels B f hf T hT X z).length)
  (id : Fin (executeLevels B f hf T hT X z)[j].outputSites) (base : ℕ)

private noncomputable local instance : DecidableEq Z.Base := Classical.decEq _
local notation "vs" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "side" => selectedLayout Z B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink Z sel
local notation "Y" => Z.shrinkNext B.shrink (S.shrink i) sel
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "heap" => ShrinkCallABI.hiddenBase regions n
local notation "seed" => ShrinkHiddenSlots.rows Z side widths v site.seed
local notation "nodeAddr" => site.later + (B.recordLimit + 2) *
  PortRefresh.ArgumentAddress.siteOrdinal (Y) v
local notation "rowAddr" => address B.recordLimit (layerBase B.recordLimit base tags (j.val + 1))
  id.val
local notation "jobs" => ShrinkSiteBank.jobs B i Z sel site.workspace site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v
set_option quotPrecheck false in
local notation "readerAt" => (shrinkPassReaders B f hf i rfl Z).termParsers sel

/-- External row contents, nonwrapping address intervals and fixed schedule
coordinates used by this one installed shrinking visit. -/
structure CanonicalSiteData : Prop where
  publicData : site.publicData = M.publicData
  levels : site.levels = (vs).length
  passIndex : site.passIndex = j.val
  level : site.level = levelHead M.publicData site.mem j.val
  siteAddr : nodeAddr = rowAddr
  siteOrdinal : (siteIndex Z v).val = id.val
  shrinking : tagLevel B f hf (vs)[j] = .shrink
  index : (vs)[j].origin.ordinal = i.val
  fit : layerBase B.recordLimit base tags ((vs).length + 1) < 2 ^ w
  incidence : site.incidence.ActualColumns Z site.mem
  strideFit : B.recordLimit + 2 < 2 ^ w
  above : n ≤ NativeFrame.frameBase regions
  frameRoom : NativeFrame.frameBase regions + 12 ≤ 2 ^ w
  directory : ∀ node : Word w, node.val = nodeAddr →
    (site.descriptor node).directoryBase = site.level + 14 ∧
    ChildArguments.Resident (regions).arguments site.incidence site.mem site.older B.recordLimit n
      node (site.descriptor node)
  orderAt : ∀ node : Word w, node.val = nodeAddr →
    (site.descriptor node).sites = List.ofFn fun k => (((readerAt).order.children v).entries k).val
  abovePointer : ∀ u, n < (regions).arguments.base (childNode Z site.older B.recordLimit u)
  oldNodes : ∀ u, childNode Z site.older B.recordLimit u < site.rowEnd
  parentFit : nodeAddr < site.rowEnd
  earlier : ∀ u, childNode Z site.older B.recordLimit u < nodeAddr
  wire : Z.maxWireWidth ≤ n
  hiddenWidth : ∀ motif t, widths motif (!side, t) ≤ n ^ 2
  hiddenRoom : heap + (ShrinkHistoryRows.hiddenOrder Z).length * n ^ 2 ≤ 2 ^ w
  selectors : site.hiddenArgs.selectorBits = (B.shrink.selectorBits : Word w)
  rowStride : site.hiddenArgs.rowStride = hiddenStride i
  headRoom : site.level.val + 38 < 2 ^ w
  headers : Header.Published site.hiddenArgs site.level.val site.mem
  countFit : site.hiddenArgs.countBase + site.hiddenArgs.owner < 2 ^ w
  count : (site.mem (site.hiddenArgs.countBase + site.hiddenArgs.owner)).val = (seed).length
  valid : ValidRows site.hiddenArgs site.mem seed
  baseEq : site.hiddenArgs.scratchBase = heap
  strideEq : site.hiddenArgs.slotStride = n ^ 2
  ownerEq : site.hiddenArgs.owner = (siteIndex Z v).val
  words : MapResidentInputs.Published site.mem site.level
    ((ShrinkResidentLayout.layout Z site.source.first).params (a i) true w 3)
    ((ShrinkResidentLayout.layout Z site.source.first).params (a i) true w 5) site.term 10
  mapRoom : firstMap B i site.source v + (order Z side v).length < 2 ^ w
  levelEq : site.level = (levelStart
    (BlockProgram.layout B site.workspace.val site.positions site.blocks) site.cur : Word w)

/-- The actual packet bounds and retained source rows for this parent
assignment, at the physical vertex's external read boundary. -/
structure CanonicalMapData (H : Word w) (parent : (Y).network.Half v) : Prop where
  terminalRoom : H.val + 31 < 2 ^ w
  sources : ∀ old q, ShrinkSiteBank.RowSources B i Z sel site.workspace site.positions site.blocks
    site.cur site.bounds n site.rowEnd site.older site.later v old parent site.mem H q
  space : ∀ old q, ShrinkCanonicalJob.PacketSpace B i Z sel q.1.1 q.1.2 (jobs old parent q)
    n site.limit

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
