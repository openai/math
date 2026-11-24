import OAI.Computability.VPVNP.PairDispatchedRowEffects
import OAI.Computability.VPVNP.PairVertexRoleDomains
import OAI.Computability.VPVNP.PairVertexOrdinalRoleCost
import OAI.Computability.VPVNP.PairShrinkRoleRowUpdate
import OAI.Computability.VPVNP.PairVertexSelectedDesc
import OAI.Computability.VPVNP.PairSimulationFieldReadSafety

/-!
# Selected shrinking rows in the terminal traversal

The same address selects the physical role, the shrinking site, and the term
reader. Replacing the popped packet by the selected children consumes one
vertex's histogram allowance. This holds for every prepared parent half and
every remaining private tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM PrivateRAM DFS CompressorRecords Compression LocalHistory NetworkKernel
open TreeDecode NodeArguments TraversalRows TraversalRoles VertexImage LeafSourceLoad
open scoped Fin.CommRing
set_option quotPrecheck false

variable {w n h : ℕ}

variable {k K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f) {lanes : ℕ}
    (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute f hf T hT X).Choices) (base : ℕ)

local notation "vs" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "leaf" => (⟨leafLayer (siteOrder X), .cursor⟩ : TaggedLayer)
local notation "cap" => B.recordLimit
local notation "pos" => layerBase cap base (tags)
local notation "desc" => selectedDesc B f hf T hT X z base
local notation "fmt" => SelectedPacketFormat B f hf T hT X z base
local notation "rows" => selectedLayers B f hf T hT X z

variable (i : Fin (executeLevels B f hf T hT X z).length)
    (shrink : tagLevel B f hf ((executeLevels B f hf T hT X z).get i) = .shrink)
local notation "v₀" => (vs).get i
local notation "term" => ((v₀).pass.step.term (v₀).term)
local notation "Site" => (term).output.Site
local notation "Half" => (term).output.Half
local notation "PlacedAt" => Placed (term).place (v₀).input.network.Half
local notation "rdr" => originReader B f hf (v₀).origin (v₀).term
local notation "ptr" => sitePointers cap ((pos) (i.val + 1)) (ShrinkRoleDirectory.outputOrder v₀)
local notation "oldAddr" => (fun u => (sitePointers cap ((pos) i.val) (siteOrder (v₀).input) u).1)
local notation "before" => (fun u b => Packet.mk ((oldAddr) u) (packed (v₀).input u b))
local notation "head" => (fun u b => Packet.mk ((ptr) u).1 (pullBits ((v₀).pass.output_eq (v₀).term)
    (packed ((v₀).pass.next (v₀).term)) u b))
local notation "site" => (fun u => (⟨⟨i,u⟩, shrink⟩ : ShrinkRoleDirectory.ShrinkSite vs))

variable {geo rootFields leafSeg shrinkSeg refreshSeg : Segment} {p regs : ℕ}
    (A : Placement (segments geo rootFields leafSeg shrinkSeg refreshSeg) p regs)
    (M : Machine w p regs 11) (m : Memory w) (R : LeafArena.Regions)
    (offset : ℕ) (data : Fin 10 → Word w) (vals : Static 34 → Word w) (order : B.Entry ≃ Fin h)
    (nodeCap limit power scan : ℕ)
    (readers : ShrinkRoleDirectory.ShrinkSite (executeLevels B f hf T hT X z) → HookParser w n)
    (handlers : NodeDispatch.Role → HookParser w n)

local notation "stable" => VertexFrameData R data (offset : Word w) vals
local notation "hist" => privateHistogram order.symm R.histBase
local notation "valid" => Budgeted R.arguments fmt stable desc hist nodeCap limit
local notation "H" => TerminalLink.header M.publicData
local notation "allow" => TerminalLink.workerCell H
local notation "hook₀" => dispatcher handlers m (offset : Word w)
local notation "cost" => ordinalJobCost n power scan

attribute [local irreducible] executeLevels originReader selectedDesc

set_option maxHeartbeats 3500000 in
-- The indexed pass carries dependent input, output and kernel witness types.
/-- Assemble a genuinely indexed shrinking level from its site-reader and
machine-cell laws. Its descendant table, packet format, counter headroom,
physical dispatch tag and wrapped path costs are computed on the selected
branch. -/
theorem levelChecks
    (installed : handlers .shrink = ShrinkRoleDirectory.parser cap base leaf vs readers)
    (link : Contains A M) (published : TraversalRoles.Reads w m offset cap base tags)
    (codes : 2 < 2 ^ w) (tagEnd : offset + base + tagWords cap tags ≤ (H).val)
    (headerFit : (H).val + 31 < 2 ^ w)
    (start : n ≤ R.arguments.start) (stride : frameStride (slotDegree S) n ≤ R.arguments.stride)
    (histFit : R.histBase ≤ 2 ^ w) (nodes : base + words cap rows ≤ R.nodes)
    (width : B.growthConstant ^ T * (X.maxWireWidth + 1) ≤ n) (limitFit : limit < 2 ^ w)
    (run : (handlers .shrink).ExactOn
      (RoleDomains.Domain X cap base vs R data (offset : Word w) vals hist nodeCap limit .shrink)
      M (A.entry (rolePart .shrink)) (A.dfsPC 3) A.dfs m)
    (suffix : ∀ (u : Site) (b : Half u) pending s bits, valid (head u b :: pending) s →
      ((readers (site u)).read ((ptr u).1 : Word w) s bits).map Prod.snd =
        ((nodeReader rdr u b).read bits).map Prod.snd)
    (update : ∀ (u : Site) (b : Half u) (a : PlacedAt u)
      (k : ((rdr).witness u a b).Choice) pending s tail job, valid (head u b :: pending) s →
      (readers (site u)).read ((ptr u).1 : Word w) s ((rdr).nodeBits u a b k ++ tail) =
        some (job, tail) →
      RowUpdate R order data (offset : Word w) vals s job
        (TreeDecode.children rdr before u a)
        (((rdr).witness u a b).exponents k))
    (small : ∀ (u : Site) (b : Half u) (a : PlacedAt u)
      (k : ((rdr).witness u a b).Choice) l, ((rdr).witness u a b).exponents k l ≤ nodeCap)
    (trace : ∀ (u : Site) (b : Half u) (a : PlacedAt u)
      (k : ((rdr).witness u a b).Choice) pending s job, valid (head u b :: pending) s →
      (readers (site u)).read ((ptr u).1 : Word w) s ((rdr).nodeBits u a b k) = some (job, []) →
      after m job.trace = m ∧ SourceTransport.Reads allow job.trace ∧
      countProbes job.trace + 1 ≤ scan * (n.log2 + 1) ^ power ∧ job.trace.length + 9 ≤ n ^ 43) :
    LevelChecks B f hf hook₀ valid hist (JobGuard A M m allow cost) cap ((pos) i.val) v₀ := by
  have next : (pos) (i.val + 1) = TraversalRows.address cap ((pos) i.val)
      (siteOrder (v₀).input).length := selected_level_bases B f hf T hT X z base i
  unfold LevelChecks
  rw [← next]
  have tagFit : offset + base + tagWords cap tags ≤ 2 ^ w := tagEnd.trans (H).isLt.le
  have endEq : (pos) ((vs).length + 1) = base + tagWords cap tags := by
    rw [selected_endBase, tagWords, selected_layers]
  have rowsFit : (pos) ((vs).length + 1) ≤ 2 ^ w := by rw [endEq]; omega
  have nodeBelow (u) : (ptr u).1 < (pos) ((vs).length + 1) := by
    have bound := OutputRowDirectory.rowAddress_lt_end cap base leaf
      (ShrinkRoleDirectory.outputTags vs)
      (ShrinkRoleDirectory.siteRows vs (site u).val)
    have len : (ShrinkRoleDirectory.outputTags vs).length = (vs).length := List.length_map _
    rw [len] at bound
    exact bound
  have nodeVal (u) : ((ptr u).1 : Word w).val = (ptr u).1 :=
    Nat.mod_eq_of_lt ((nodeBelow u).trans_le rowsFit)
  have localRead u (s : Scratch w n) bits :
      (handlers .shrink).read ((ptr u).1 : Word w) s bits =
        (readers (site u)).read ((ptr u).1 : Word w) s bits := by
    rw [installed]
    exact ShrinkRoleDirectory.read_at cap base leaf vs readers rowsFit _ (site u) (nodeVal u) s bits
  have tag u : NodeDispatch.role (m ((offset : Word w) + ((ptr u).1 : Word w)).val) = .shrink := by
    have physical := ShrinkRoleDirectory.dispatch_at_site cap base leaf vs published codes tagFit
      ((ptr u).1 : Word w) (site u).val (nodeVal u)
    exact physical.trans (congrArg TraversalRoles.Role.dispatch shrink)
  have tagCell u : allow ((offset : Word w) + ((ptr u).1 : Word w)).val := by
    apply TerminalLink.workerCell_of_lt headerFit
    rw [← Nat.cast_add, Fin.val_natCast]
    have bound := nodeBelow u
    rw [endEq] at bound
    exact (Nat.mod_le ..).trans_lt (by omega)
  have counts u b a k pending (s : Scratch w n) (job : VisitPath w n)
      (h : valid (head u b :: pending) s)
      (eff : RowUpdate R order data (offset : Word w) vals s job
        (TreeDecode.children rdr before u a)
        (((rdr).witness u a b).exponents k)) (l) :
      hist (job.update s) l = hist s l + ((rdr).witness u a b).exponents k l := by
    change (rawScratch _ ((R.histBase + (order l).val : ℕ) : Word w)).val = _
    rw [eff.counters l]
    simpa only [privateHistogram, Equiv.symm_symm, Fin.cast_val_eq_self] using
      h.word_add limitFit l (small u b a k l)
  have types := selected_children_fit B f hf T hT X z base R start stride histFit nodes width i
  have raw : NodeStep (handlers .shrink) valid rdr ptr before head := by
    apply nodeStep_of_suffix
    · intro u b pending s bits h
      rw [localRead]
      exact suffix u b pending s bits h
    · intro u b pending s bits job tail a k h got enc
      rw [localRead, enc] at got
      have eff := update u b a k pending s tail job h got
      refine h.push ?_ eff.frame (types u a) ?_
        (fun l => (counts u b a k pending s job h eff l).le.trans
        (Nat.add_le_add_left (small u b a k l) _))
      · exact (selectedDesc_level B f hf T hT X z base i u).trans
          (children_addresses rdr before oldAddr (fun _ _ => rfl) desc u a).symm
      · intro q hq j
        have typed := (List.mem_append.mp hq).elim (types u a q)
          (fun old => (h.frontier.prepared.2 q (List.mem_cons_of_mem _ old)).imp_right And.left)
        have endArg := R.node_before
          ((selected_packet_node B f hf T hT X z base typed.1).trans_le nodes)
        have slot := typed.2.2.1
        have low := typed.2.1
        have index := j.isLt
        exact eff.arguments _ (by omega) (by omega)
  constructor
  · exact dispatcher_nodeStep tag raw
  · intro u b a k pending s h
    obtain ⟨body, read, remaining⟩ := raw.complete u b pending s a k [] h
    rw [List.append_nil] at read
    have domain : RoleDomains.Domain X cap base vs R data (offset : Word w) vals hist nodeCap limit
        .shrink ((ptr u).1 : Word w) s :=
      ⟨site u, nodeVal u, h.frontier.frame, h.headRoom, b, h.frontier.head.2.2⟩
    have native := run.success _ s domain _ body [] read
    rw [localRead] at read
    have full := read
    rw [← List.append_nil ((rdr).nodeBits u a b k)] at full
    have eff := update u b a k pending s [] body h full
    have bodyGuard := trace u b a k pending s body h read
    have charge := dispatchJob_cost (m := m) (offset := (offset : Word w))
      (node := ((ptr u).1 : Word w))
      (saved := s) body
    have realizes : RealizesJob hist
        ⟨(ptr u).1,(rdr).nodeBits u a b k,((rdr).witness u a b).exponents k⟩ body := by
      refine ⟨native.1, by simpa only [List.append_nil] using native.2.2.1.symm, ?_⟩
      intro t en l
      rw [eff.enabled_eq t en]
      exact counts u b a k pending s body h eff l
    let rawCost (j : VisitPath w n) := countProbes j.trace + 1 ≤ scan * (n.log2 + 1) ^ power ∧
      j.trace.length + 9 ≤ n ^ 43
    have guard : RoleJobGuard A M m .shrink allow rawCost body := ⟨native.2.2.2,bodyGuard⟩
    exact ⟨_, dispatchJob_realizes realizes, ⟨rfl,native.2.1⟩,
      dispatchJob_guard link h.frontier.frame.resident (tag u) (tagCell u) native.1 guard
        (fun ok => ⟨charge.1.trans_le ok.1, charge.2.trans ok.2⟩), remaining⟩

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
