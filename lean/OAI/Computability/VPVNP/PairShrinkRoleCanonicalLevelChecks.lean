import OAI.Computability.VPVNP.PairShrinkRoleIndexedUpdate
import OAI.Computability.VPVNP.PairShrinkRoleIndexedSuffix
import OAI.Computability.VPVNP.PairShrinkRoleLevelChecks
import OAI.Computability.VPVNP.PairShrinkSiteOrdinal

/-!
# Checking the selected physical shrinking level

The published row selects the stage, state and layout. Its stored parent
determines the map calls at every site. The canonical parser's private writes
and remaining tape therefore apply to the original selected term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM PrivateRAM DFS CompressorRecords Compression LocalHistory NetworkKernel
open TreeDecode NodeArguments TraversalRows TraversalRoles VertexImage LeafSourceLoad
open ShrinkRoleDirectory
open scoped Fin.CommRing
set_option quotPrecheck false

variable {w n : ℕ} {k : Type} {K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f) {lanes : ℕ}
    (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute f hf T hT X).Choices) (base : ℕ)
    (i : Fin (executeLevels B f hf T hT X z).length)
    (shrink : tagLevel B f hf ((executeLevels B f hf T hT X z).get i) = .shrink)

local notation "vs" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "leaf" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "cap" => B.recordLimit
local notation "pos" => layerBase cap base tags
local notation "rows" => selectedLayers B f hf T hT X z
local notation "v₀" => (vs).get i
local notation "term" => (v₀).pass.step.term (v₀).term
local notation "rdr" => originReader B f hf (v₀).origin (v₀).term
local notation "ptr" => sitePointers cap ((pos) (i.val + 1)) (outputOrder v₀)
local notation "row" u => (⟨⟨i,u⟩,shrink⟩ : ShrinkSite vs)

variable {geo rootFields leafSeg shrinkSeg refreshSeg : Segment} {p regs : ℕ}
    (A : Placement (segments geo rootFields leafSeg shrinkSeg refreshSeg) p regs)
    (M : Machine w p regs 11) (m : Memory w) (offset : ℕ) (data : Fin 10 → Word w)
    (vals : Static 34 → Word w) (order : B.Entry ≃ Fin (Fintype.card B.Entry))
    (nodeCap limit power scan : ℕ)
    (bank : (x : ShrinkSite (executeLevels B f hf T hT X z)) →
      CanonicalSite B x.occurrence.i x.occurrence.state x.occurrence.selection
        x.occurrence.site w n (Fintype.card B.Entry))
    (handlers : NodeDispatch.Role → HookParser w n)

local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n
  (base + words cap rows) (Fintype.card B.Entry)
local notation "hist" => privateHistogram order.symm (regions).histBase
local notation "stable" => VertexFrameData regions data (offset : Word w) vals
local notation "valid" => Budgeted (regions).arguments (SelectedPacketFormat B f hf T hT X z base)
  stable (selectedDesc B f hf T hT X z base) hist nodeCap limit
local notation "domain" => RoleDomains.Domain X cap base vs regions data (offset : Word w)
  vals hist nodeCap limit .shrink
local notation "H" => TerminalLink.header M.publicData
local notation "reader" x => canonicalParent (bank x) order f hf

attribute [local irreducible] executeLevels originReader selectedDesc shrinkPassReaders
  canonicalParent

include shrink
set_option maxHeartbeats 3000000 in
-- Compare the selected origin's dependent old and new halves with the physical kernel.
theorem canonicalLevelChecks
    (installed : handlers .shrink = ShrinkRoleDirectory.parser cap base leaf vs (fun x => reader x))
    (link : Contains A M) (published : TraversalRoles.Reads w m offset cap base tags)
    (codes : 2 < 2 ^ w) (tagEnd : offset + base + tagWords cap tags ≤ (H).val)
    (headerFit : (H).val + 31 < 2 ^ w)
    (start : n ≤ (regions).arguments.start)
    (stride : frameStride (slotDegree S) n ≤ (regions).arguments.stride)
    (histFit : (regions).histBase ≤ 2 ^ w) (nodes : base + words cap rows ≤ (regions).nodes)
    (width : B.growthConstant ^ T * (X.maxWireWidth + 1) ≤ n) (limitFit : limit < 2 ^ w)
    (run : (handlers .shrink).ExactOn domain M (A.entry (rolePart .shrink)) (A.dfsPC 3) A.dfs m)
    (endRow : ∀ x, (bank x).rowEnd = base + words cap rows)
    (oldBase : ∀ x, (bank x).older = (pos) x.val.1.val)
    (info : ∀ x, CanonicalSiteData (bank x) M f hf T hT X z x.val.1
      (RoleDomains.siteId B f hf T hT X z x) base)
    (maps : ∀ x parent, CanonicalMapData (bank x) H parent)
    (small : ∀ (u : (term).output.Site) (b : (term).output.Half u)
      (a : Placed (term).place (v₀).input.network.Half u) (k : ((rdr).witness u a b).Choice) l,
      ((rdr).witness u a b).exponents k l ≤ nodeCap)
    (trace : ∀ x s bits tail job, (reader x).read
      (ShrinkRoleDirectory.address cap base leaf vs x.val : Word w) s bits = some (job, tail) →
      after m job.trace = m ∧ SourceTransport.Reads (TerminalLink.workerCell H) job.trace ∧
        countProbes job.trace + 1 ≤ scan * (n.log2 + 1) ^ power ∧ job.trace.length + 9 ≤ n ^ 43) :
    LevelChecks B f hf (dispatcher handlers m (offset : Word w)) valid hist
      (JobGuard A M m (TerminalLink.workerCell H) (ordinalJobCost n power scan))
      cap ((pos) i.val) v₀ := by
  let family := fun x => reader x
  have positive : 0 < w := by
    cases w with
    | zero => exact False.elim ((by decide : ¬2 < 2 ^ 0) codes)
    | succ w => exact Nat.zero_lt_succ w
  have val (u : (term).output.Site) : ((ptr u).1 : Word w).val = (ptr u).1 := by
    apply Nat.mod_eq_of_lt
    let x : ShrinkSite vs := row u
    have bound := OutputRowDirectory.rowAddress_lt_end cap base leaf (outputTags vs)
      (siteRows vs x.val)
    have len : (outputTags vs).length = (vs).length := List.length_map _
    rw [len] at bound
    exact bound.trans (info x).fit
  have physical (u : (term).output.Site) :
      let x : ShrinkSite vs := row u
      ((ptr u).1 : Word w).val = (bank x).later + (cap + 2) *
        PortRefresh.ArgumentAddress.siteOrdinal x.occurrence.nextState x.occurrence.site := by
    intro x
    exact (val u).trans (info x).siteAddr.symm
  apply levelChecks B f hf T hT X z base i shrink A M m regions offset data vals order
    nodeCap limit power scan family handlers installed link published codes tagEnd headerFit
    start stride histFit nodes width limitFit run
  · intro u b pending s bits budget
    let x : ShrinkSite vs := row u
    refine indexedSiteSuffix v₀ u shrink (bank x) order _ s b ?_ positive
      ((info x).orderAt _ (physical u)) bits
    rw [endRow x, val u]
    exact budget.frontier.head.2.2.2
  · intro u b a k pending s tail job budget got
    let x : ShrinkSite vs := row u
    refine indexedSiteUpdate v₀ u shrink (bank x) (info x) order b a k (maps x _)
      ((pos) i.val) (base + words cap rows) (oldBase x) (endRow x) _ s (physical u) ?_
      data (offset : Word w) vals budget.frontier.frame tail job got
    rw [val u]
    exact budget.frontier.head.2.2.2
  · exact small
  · intro u b a k pending s job _ got
    exact trace (row u) s _ [] job got

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
