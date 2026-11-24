import OAI.Computability.VPVNP.PairShrinkRoleScheduledUpdate
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader

/-!
# Reading a scheduled shrinking witness with the canonical parent parser

The stored parent selects the gather jobs. The two field readers recover the
actual placed and hidden assignments. The exterior and counter identities of
that bank then determine the private update on every witness prefix.
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

variable {K : Type} {C : Type*} [_root_.Field K] [CommRing C]
  {S : BlockSchedule K} {B : S.Templates}
  {i : Fin S.steps} {g n w t : ℕ}
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
local notation "rdr" => readerAt B f hf i X sel
local notation "ordAt" => childOrder B f hf i X sel v
local notation "childAt" => childNode X site.older B.recordLimit
local notation "packetsAt" => TreeDecode.children rdr
  (fun u b => Packet.mk (childAt u) (packed X u b)) v old
local notation "rowsAt" => ShrinkHiddenSlots.rows X side widths v
local notation "heap" => ShrinkCallABI.hiddenBase regions n
local notation "childLoad" => selectedChildSetup site.publicData site.mem site.levels site.passIndex
  S.steps i.val (a i)
local notation "hiddenLoad" => physicalHiddenSetup B.shrink.selectorBits (hiddenStride i)
  site.level.val site.mem
local notation "mapLoad" => mapStartSetup site.mem site.level (Fin.val (siteIndex X v) : Word w)

set_option maxHeartbeats 4000000 in
-- Align the scheduled kernel's placement types and the actual gathered field assignments.
/-- The full native parent parser realizes the tree row's private-memory contract
for every supplied continuation and incoming stored parent. -/
theorem canonicalParent_update_of_bank (x : (W).Choice) (node : Word w) (saved : Scratch w n)
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
    (preserve : ∀ initial events final, scan node (canonicalBank site ord parent old x.1) initial =
      some (events, final) → ∀ address : Word w, address.val < heap →
        (address.val < (regions).histBase ∨ (regions).histBase + t ≤ address.val) →
        rawScratch final address = rawScratch initial address)
    (count : ∀ initial events final, scan node (canonicalBank site ord parent old x.1) initial =
      some (events, final) → ∀ l, let address : Word w := ((regions).histBase + (ord l).val : ℕ)
        rawScratch final address = rawScratch initial address + ((W).exponents x l : Word w))
    (tail : List Bool) (job : VisitPath w n)
    (hit : (canonicalParent site ord f hf).read node saved
      ((rdr).nodeBits v old parent x ++ tail) = some (job, tail)) :
    RowUpdate regions ord data offset vals saved job packetsAt ((W).exponents x) := by
  rw [canonicalParent, parentParser_read _ _ _ _ node saved parent stored positive] at hit
  have labels : t ≤ (regions).histWords := by
    change t ≤ Fintype.card B.Entry
    exact (by simpa only [Fintype.card_fin] using (Fintype.card_congr ord).symm : t = _).le
  have bankEq := typedActions_encoded (term := termAt B f hf i X sel) X v ordAt
    side widths v site.seed (canonicalBank site ord parent) old x.1
  have scanRun {s : Scratch w n} {events final}
      (h : scan node (canonicalActions site ord f hf parent
        (children (t := termAt B f hf i X sel) X v ordAt old) (rowsAt x.1)) s =
          some (events, final)) :
      scan node (canonicalBank site ord parent old x.1) s = some (events, final) :=
    (congrArg (fun actions => scan node actions s) bankEq).symm.trans h
  refine scheduledRowUpdate B f hf i X sel v old parent x site.seed regions site.incidence site.mem
    site.older B.recordLimit site.descriptor site.hiddenArgs (canonicalActions site ord f hf parent)
    childLoad hiddenLoad mapLoad node saved ord data offset vals frame order
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) base before labels heapFit rowFit fits nodes above
    ?_ ?_ tail job hit
  · intro events final run address low outside
    exact preserve _ events final (scanRun run) address low outside
  · intro events final run l
    exact count _ events final (scanRun run) l

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
