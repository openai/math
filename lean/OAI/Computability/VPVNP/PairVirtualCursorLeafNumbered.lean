import OAI.Computability.VPVNP.PairSelectedCursorLeaf
import OAI.Computability.VPVNP.PairVirtualCursorLeafBounds
import OAI.Computability.VPVNP.PairVirtualCursorLeafTransfer
import OAI.Computability.VPVNP.PairVertexOrdinalRoleCost

/-! # Cursor leaf checks in the numbered lanes of the live processor -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.SelectedCursorLeaf

open BurstRAM PrivateRAM DFS CursorNetwork CursorRouting LeafStartup
open TreeDecode LocalHistory LeafHandler NodeArguments NetworkKernel CompressorRecords NativeFrame
  VertexImage
open CompressorRecords.SourceTransport Compression TraversalRows
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace
open scoped Fin.CommRing

set_option maxRecDepth 10000

/-- The two leaf-row obligations consumed by the selected role assembly,
using the common private frame and the ordinal worker's cost bound. -/
def Rows {w n p r g ex lanes : ℕ} {K : Type*} [CommRing K] {Label : Type} [Fintype Label]
    {κ : Label → K} {geometry rootFields leaf shrink refresh : Segment}
    (A : Placement (segments geometry rootFields leaf shrink refresh) p r) (M : Machine w p r 11)
    (handlers : NodeDispatch.Role → HookParser w n) (m : Memory w) (offset : Word w)
      (R : LeafArena.Regions)
    (data : Fin 10 → Word w) (vals : LeafSourceLoad.Static 34 → Word w) (cap base : ℕ)
    (format : Packet → Prop) (desc : ℕ → List ℕ) (order : Fin g ≃ Label) (allow : ℕ → Prop)
    (nodeCap limit power scan : ℕ) (X : State ex lanes) (sites : SiteParsers κ X.network) : Prop :=
  let leaves := sitePointers cap base (siteOrder X)
  let input := fun u z => Packet.mk (leaves u).1 (packed X u z)
  let hist := privateHistogram order R.histBase
  let valid := Budgeted R.arguments format (VertexFrameData R data offset vals) desc hist nodeCap
    limit
  Subtrees (dispatcher handlers m offset) valid sites (fun u => leafTree (leaves u)) input ∧
    Emits valid hist (JobGuard A M m allow (ordinalJobCost n power scan)) sites input
      (leafJobs sites leaves)

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}
  {geometry rootFields shrink refresh : Segment} {p r w : ℕ}
  (V : Placement (segments geometry rootFields LeafRole.segment shrink refresh) p r)
  (M : Machine w p r 11) {L : PrimedInputRAM.Lengths} {n a H s : ℕ}
    {Q : PrimedInputRAM.Layout L n a H w}
  (aux : PrimedCounter.Data Q s) {d b l e : ℕ} [NeZero d] (split : d = b + l)
  (dim : 1 < d) (cap : ProcessorBudget n d e w)
  {K : Type*} [CommRing K] {Label : Type} [Fintype Label] (κ : Label → K)
  (clock : NominationClock aux cap.tags cap.capFits (n ^ 39)) (m : Memory w)
    (header offset : Word w)
  (arity rowCap rowBase : ℕ)

local notation "region" => fromHeader arity M.publicData header m
local notation "words" => leafWords arity M.publicData header offset m
local notation "fields" => LeafRole.addressFields words
local notation "numbering" => Equiv.trans (finCongr split) (cursorCoordinateLabels b l)
local notation "X" => scanInput numbering dim S e w
local notation "leaves" => sitePointers rowCap rowBase (siteOrder X)
local notation "sites" => nominationSites aux cap.tags cap.capFits numbering dim
  (Nat.add_sub_of_le (And.left (BlockSchedule.degree_bounds S))) κ (n ^ 39) clock

/-- Splitting the processor's coordinate numbering into its base and lane
blocks preserves the actual occurrence readers and all physical leaf jobs. -/
theorem numberedRows (link : Contains V M) (fit : (region).stackBase + Fintype.card ScalarPort * n
  ^ 40 < 2 ^ w)
    (resources : LeafVisit.CursorLeafBounds aux cap) (hn : 2048 ≤ n)
    (stride : (m (header + 15).val).val = rowCap + 2) (rb : (m (header + 18).val).val = 2 ^ b)
    (rl : (m (header + 19).val).val = 2 ^ l) (span : (m (header + 20).val).val =
      LiveAuxiliaryHeaders.span L aux.hist.length)
    (shadowFit : (M.publicData 3).val + (m (header + 20).val).val ≤ 2 ^ w)
    (headers : ∀ i < (m (header + 20).val).val, (m ((M.publicData 3).val + i)).val =
      (aux.initial i).val)
    (size : (M.publicData 6).val = n) (baseAt : rowBase = (fields .base).val)
    (handlers : NodeDispatch.Role → HookParser w n)
    (leaf : handlers .leaf = LeafRole.parser (b := d) (l := 0) words aux cap region fit m (n ^ 39))
    (allow : ℕ → Prop) (shadow : ∀ site : Word w, site < fields .span → allow
      (fields .shadow + site).val)
    (tag : ∀ u, m (offset + ((leaves u).1 : Word w)).val = 0)
    (tagRead : ∀ u, allow (offset + ((leaves u).1 : Word w)).val)
    (format : Packet → Prop) (desc : ℕ → List ℕ)
    (typed : ∀ q, format q → q.node < (region).nodes ∧ q.node < 2 ^ w)
    {g : ℕ} (order : Fin g ≃ Label) (hcount : g ≤ (region).histWords)
    (nodeCap limit power scan : ℕ) (scanTwo : 2 ≤ scan) (shape : ∀ u, desc (leaves u).1 = []) :
    Rows V M handlers m offset region words (LeafVisit.cacheWords aux d e) rowCap rowBase format
      desc order
      allow nodeCap limit power scan X sites := by
  subst d rowBase
  have low : n ≤ (region).arguments.start := size.ge
  have before : n < (region).stackBase := by
    unfold LeafArena.Regions.stackBase LeafArena.Regions.cacheBase LeafArena.Regions.histBase
      Arena.base
    omega
  have out := checksBudgeted V M aux dim (Nat.add_sub_of_le S.degree_bounds.1) cap κ clock m
    header offset arity
    rowCap link fit hn resources.width stride rb rl span shadowFit headers size resources.time
      resources.room
    resources.boot handlers leaf allow shadow tag tagRead format
    (VertexFrameData region words offset (LeafVisit.cacheWords aux (b + l) e)) desc typed
      (fun _ h => h.cached)
    (fun _ h => h.record) (fun _ h => h.resident) (fun _ _ h => h.of_below_stack before) order
      hcount nodeCap limit shape
  exact ⟨out.1, emits_withCost out.2 (fun _ h => leaf_ordinal_cost (by omega) scanTwo h)⟩

end PairSimulation.SelectedCursorLeaf

end VPVNP
end Computability
end OAI
