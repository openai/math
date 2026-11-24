import OAI.Computability.VPVNP.PairShrinkRoleCanonicalScanUpdate
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalExterior
import OAI.Computability.VPVNP.PairShrinkRoleMapHistogramNative

/-!
# The actual child, frame and counter effects of the selected shrinking parser

The stored parent selects the gather jobs. The old and absorbed field readers
recover the two arguments of the resident bank, whose physical stores preserve
the exterior and add the selected matrix entries to the histogram.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open LocalHistory NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess LeafSourceLoad
open CompressorRecords CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open ShrinkVertexImage ShrinkMapImage.Registers MapResidentRows ResidentMapLoop.Exact
open scoped Fin.CommRing
open private termAt readerAt childOrder from OAI.Computability.VPVNP.PairShrinkRoleScheduledSuffix
open private jobPublic from OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader

variable {K : Type} {C : Type*} [_root_.Field K] [CommRing C]
  {S : BlockSchedule K} {B : S.Templates}
  {i : Fin S.steps} {g n w t packetEnd : ℕ}
  {X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g)}
  {sel : X.ShrinkSelection B.shrink} {v : MapResidentRows.Site X}
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

variable (site : CanonicalSite B i X sel v w n t) (ord : B.Entry ≃ Fin t)
  (f : B.Entry → C) (hf : B.IsSolution f)
  (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
    X.packingInputIso.site.symm) X.network.Half v)
  (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
local notation "W" => B.shrinkPassWitnesses f hf i rfl X sel v old parent
local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "jobs" => ShrinkSiteBank.jobs B i X sel site.workspace site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v old parent
local notation "rowAt" => MapWitness.rowEquiv X side v
local notation "rdr" => readerAt B f hf i X sel
local notation "ordAt" => childOrder B f hf i X sel v
local notation "childAt" => childNode X site.older B.recordLimit
local notation "packetsAt" => TreeDecode.children rdr
  (fun u b => Packet.mk (childAt u) (packed X u b)) v old
local notation "rowsAt" => ShrinkHiddenSlots.rows X side widths v
local notation "heap" => ShrinkCallABI.hiddenBase regions n
set_option maxHeartbeats 4000000 in
-- Align the scheduled kernel's placement types and the actual gathered field assignments.
/-- The full native parent parser realizes the tree row's private-memory contract
for every supplied continuation and incoming stored parent. -/
theorem canonicalParent_update (x : (W).Choice) (node : Word w) (saved : Scratch w n)
    (stored : (Packet.mk node.val (packed (Y) v parent)).Stored (regions).arguments saved)
    (positive : 0 < w) (data : Fin 10 → Word w) (offset : Word w) (vals : Static 34 → Word w)
    (frame : TreeDecode.VertexFrameData regions data offset vals saved)
    (order : (site.descriptor node).sites = List.ofFn fun j => ((ordAt).entries j).val)
    (base : site.hiddenArgs.scratchBase = heap) (before : n < (regions).histBase)
    (heapFit : heap ≤ 2 ^ w)
    (rowFit : ∀ e ∈ rowsAt x.1, heap + e.1 * site.hiddenArgs.slotStride + e.2.length ≤ 2 ^ w)
    (fits : ∀ q ∈ packetsAt, q.Fits (regions).arguments w n)
    (nodes : ∀ q ∈ packetsAt, q.node < (regions).nodes)
    (above : ∀ q ∈ packetsAt, n < (regions).arguments.base q.node)
    (baseline : Word w → Word w) (packets : ∀ q, (jobs q).Packets packetEnd baseline)
    {T : IncidenceDirectory w} {origin : ℕ}
    (headers : ∀ j, let q := rowAt j
      (jobs q).OldPublished (ShrinkCallABI.operands (slotDegree S)) (jobPublic site old parent q)
        (rowOrdinalWord X side v j) site.mem site.level T origin)
    (tail : List Bool) (job : VisitPath w n)
    (hit : (canonicalParent site ord f hf).read node saved
      ((rdr).nodeBits v old parent x ++ tail) = some (job, tail)) :
    RowUpdate regions ord data offset vals saved job packetsAt ((W).exponents x) := by
  refine canonicalParent_update_of_bank site ord f hf old parent x node saved stored positive
    data offset vals frame order base before heapFit rowFit fits nodes above ?_ ?_ tail job hit
  · intro initial events final run
    exact canonicalBank_exterior (g := g) (w := w) (n := n) (packetEnd := packetEnd)
      (T := T) (origin := origin) (initial := initial) (final := final) (es := events)
      site ord old parent x.1 baseline packets headers node run
  · intro initial events final run
    exact canonicalBank_histogram (g := g) (w := w) (n := n) (packetEnd := packetEnd)
      (T := T) (origin := origin) (initial := initial) (final := final) (es := events)
      site ord f hf old parent x baseline packets headers node run

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
