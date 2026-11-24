import OAI.Computability.VPVNP.PairRefreshOriginLevelEffect
import OAI.Computability.VPVNP.PairRefreshOriginLevelDispatch
import OAI.Computability.VPVNP.PairRefreshOriginLevelMemory

/-! # Level checks for the installed refresh worker

The completed selected directory determines the row, its tag, and both
levels of incidence data. A positive read realizes the chosen local factor
and prepares its single old packet. An arbitrary successful read recovers
that same kind of occurrence and preserves all pending siblings.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace PortRefresh
open PortRefresh.NewSlots
open TraversalRows TraversalRoles LocalHistory NetworkKernel NodeArguments TreeDecode
open VertexImage DFS
open LiveProgram Filter
open scoped Fin.CommRing
set_option quotPrecheck false

attribute [local irreducible] executeLevels originReader selectedDesc siteOrder packed children
  layerBase choiceEquiv placedEquiv halfEquiv

section IndexedRow

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → K) (hf : B.IsSolution f) {hist : ℕ} (order : B.Entry ≃
      Fin hist)
    {lanes : ℕ} (blocks : ℕ) (budget : blocks * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (branch : (B.execute f hf blocks budget X).Choices)
    (n w start positions width : ℕ)
local notation "passes" => executeLevels B f hf blocks budget X branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "first" => endAddress (BlockProgram.layout B start positions blocks)
local notation "tags₀" => selected B f hf blocks budget X branch
local notation "rows" => tagWords B.recordLimit (tags₀)
local notation "offset" => (word (rows + width) : Word w)
local notation "region" => TerminalLayout.privateRegions (slotDegree S) n (first + rows) hist
local notation "pos" => layerBase B.recordLimit first (tags₀)
local notation "format₀" => SelectedPacketFormat B f hf blocks budget X branch first
local notation "desc₀" => selectedDesc B f hf blocks budget X branch first
local notation "counts" => privateHistogram order.symm (region).histBase
variable (room : Rooms n hist w start positions blocks ⟨leafLayer (siteOrder X), .cursor⟩
    (executeLevels B f hf blocks budget X branch))
local notation "site" => rowSite n hist w start positions blocks width (leaf₀) passes room
local notation "ties₀" => RefreshBlockPlan.order B
local notation "stride₀" => LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)

variable (constants : Constants) (p q : ℕ)
variable {pcs regs : ℕ} (V : Placement (TerminalProgram.nativeSegments B constants p q order)
  pcs regs) (M : Machine w pcs regs 11) (m : Memory w)
  (memory : LevelMemory B f hf blocks budget X branch n w start positions width room M.publicData m)
  (data : Fin 10 → Word w) (vals : LeafSourceLoad.Static 34 → Word w)
  (nodeCap limit power scanCap : ℕ)
  (handlers : NodeDispatch.Role → HookParser w n)
variable (refresh : handlers .refresh = SelectedRows.parser n hist w start positions blocks width
  ⟨leafLayer (siteOrder X), .cursor⟩ (executeLevels B f hf blocks budget X branch) room order
    M.publicData m)
local notation "valid" => Budgeted (region).arguments (format₀) (VertexFrameData region data
  offset vals)
  (desc₀) counts nodeCap limit
local notation "hook" => dispatcher handlers m offset
local notation "guard" => JobGuard V M m (TerminalLink.workerCell (TerminalLink.header
  M.publicData))
  (ordinalJobCost n power scanCap)

set_option maxHeartbeats 2000000 in
-- Resolve the row address in both the selected parser and the installed worker.
include memory refresh in
private theorem assemble
    (capFit : n ≤ nodeCap) (limitFit : limit < 2 ^ w)
    (protect : ∀ (x : Row passes) s bs tail body, (site x).Prepared (word (site x).parent) s →
      ((site x).hook (ties₀) (stride₀) order M.publicData m).read (word (site x).parent) s bs
        = some (body, tail) →
      guard (dispatchJob m offset (word (site x).parent) s body))
    (i : Fin (passes).length) (tag : tagLevel B f hf passes[i] = .refresh) :
    LevelChecks B f hf hook valid counts guard B.recordLimit ((pos) i.val) passes[i] := by
  let v := passes[i]
  let r := originReader B f hf v.origin v.term
  let afterBase := TraversalRows.address B.recordLimit ((pos) i.val) (siteOrder v.input).length
  let ptr := sitePointers B.recordLimit afterBase (ShrinkRoleDirectory.outputOrder v)
  let src := fun u z => Packet.mk (sitePointers B.recordLimit ((pos) i.val) (siteOrder v.input) u).1
    (packed v.input u z)
  let dst := fun u z => Packet.mk (ptr u).1
    (pullBits (v.pass.output_eq v.term) (packed (v.pass.next v.term)) u z)
  let row := fun u => (⟨⟨i, u⟩, tag⟩ : Row passes)
  have ptrEq u : (ptr u).1 = (site (row u)).parent :=
    level_parent B f hf blocks budget X branch n hist w start positions width room (row u)
  have tags u : NodeDispatch.role (m (offset + ((ptr u).1 : Word w)).val) = .refresh :=
    (level_dispatch B f hf blocks budget X branch n hist w start positions width room (row u)
      (rows + width) (TerminalLink.header M.publicData) m memory.tags memory.codes
        memory.tagEnd memory.headerFit).1
  have fit : (pos) ((passes).length + 1) ≤ 2 ^ w := by
    rw [selected_endBase]
    have he : rows = words B.recordLimit (selectedLayers B f hf blocks budget X branch) := by
      rw [tagWords, selected_layers]
    have h := memory.tagEnd.trans (TerminalLink.header M.publicData).isLt.le
    omega
  have hw : 0 < w := Nat.pos_of_ne_zero fun hz => (by decide : ¬2 < 2 ^ 0)
    ((congrArg (fun j : ℕ => 2 < 2 ^ j) hz).mp memory.codes)
  have readAt u z pending s (ready : valid (dst u z :: pending) s) bs :
      (handlers .refresh).read ((ptr u).1 : Word w) s bs =
        ((site (row u)).hook (ties₀) (stride₀) order M.publicData m).read (word (site (row
          u)).parent) s bs := by
    rw [refresh]
    have pr := level_prepared B f hf blocks budget X branch n hist w start positions width
      room (row u) z ready
    exact (read_at n hist w start positions blocks width (leaf₀) passes room order
      M.publicData m fit (row u)
      _ s pr bs).trans (congrArg (fun b : ℕ => ((site (row u)).hook (ties₀) (stride₀) order
        M.publicData m).read
        (word b) s bs) (ptrEq u))
  have tape u z pending s (ready : valid (dst u z :: pending) s) bs tail :
      (∃ body, (handlers .refresh).read ((ptr u).1 : Word w) s bs = some (body, tail)) ↔
      ∃ a c, bs = r.nodeBits u a z c ++ tail := by
    rw [readAt u z pending s ready bs]
    have packetEq := level_packet B f hf blocks budget X branch n hist w start positions width
      room (row u) z
    have stored := (congrArg (fun q : Packet => q.Stored (region).arguments s) packetEq).mp
      ready.frontier.head.2.2.2
    exact local_tape_iff n hist w start positions blocks width (leaf₀) passes room order
      M.publicData m
      (row u) z s bs tail hw stored
  have effects u z a c pending s (ready : valid (dst u z :: pending) s) tail body
      (hit : (handlers .refresh).read ((ptr u).1 : Word w) s (r.nodeBits u a z c ++ tail) =
        some (body, tail)) :=
    selected_effect B f hf blocks budget X branch n hist w start positions width room order
      M.publicData m
      (row u) data vals nodeCap limit z a c pending s ready hw (memory.published (row u)).positive
      memory.cacheFit limitFit capFit tail body ((readAt u z pending s ready _).symm.trans hit)
  have raw : NodeStep (handlers .refresh) valid r ptr src dst := by
    constructor
    · intro u z pending s bs body tail ready hit
      obtain ⟨a, c, eqn⟩ := (tape u z pending s ready bs tail).mp ⟨body, hit⟩
      subst bs
      exact ⟨a, c, rfl, (effects u z a c pending s ready tail body hit).2.2⟩
    · intro u z pending s a c tail ready
      obtain ⟨body, hit⟩ := (tape u z pending s ready _ tail).mpr ⟨a, c, rfl⟩
      exact ⟨body, hit, (effects u z a c pending s ready tail body hit).2.2⟩
  refine ⟨dispatcher_nodeStep tags raw, ?_⟩
  intro u z a c pending s ready
  obtain ⟨body, hit, frame⟩ := raw.complete u z pending s a c [] ready
  have eff := effects u z a c pending s ready [] body hit
  have prep := level_prepared B f hf blocks budget X branch n hist w start positions width
    room (row u) z ready
  have prepared := (congrArg (fun j : ℕ => (site (row u)).Prepared (word j) s) (ptrEq u)).mp prep
  have safe := protect (row u) s _ [] body prepared ((readAt u z pending s ready _).symm.trans hit)
  exact ⟨_, dispatchJob_realizes eff.1, ⟨rfl, eff.2.1⟩,
    (congrArg (fun j : ℕ => guard (dispatchJob m offset (word j) s body)) (ptrEq u)).mpr safe,
      frame⟩

end IndexedRow

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {hist : ℕ} (order : B.Entry ≃ Fin hist) (constants : Constants) (p q : ℕ)

set_option maxHeartbeats 2000000 in
-- Combine the native read bound with each indexed role check.
/-- A uniform threshold for all fields, selected branches and physical
refresh rows using these fixed map tables. -/
theorem eventually_levelChecks :
    ∀ᶠ n : ℕ in atTop, ∀ {K : Type} [CommRing K] (f : B.Entry → K) (hf : B.IsSolution f)
      {lanes : ℕ} (blocks : ℕ) (budget : blocks * S.laneBits ≤ lanes) (X : State
        (S.degreeExponent 0) lanes)
      (branch : (B.execute f hf blocks budget X).Choices) (w start positions width : ℕ),
      let vs := executeLevels B f hf blocks budget X branch
      let leafTag := TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
      let rowBase := endAddress (BlockProgram.layout B start positions blocks)
      let tags := selected B f hf blocks budget X branch
      let rowWords := tagWords B.recordLimit tags
      let roleWord : Word w := word (rowWords + width)
      let area := TerminalLayout.privateRegions (slotDegree S) n (rowBase + rowWords) hist
      let packetFormat := SelectedPacketFormat B f hf blocks budget X branch rowBase
      let treeDesc := selectedDesc B f hf blocks budget X branch rowBase
      let histogram := privateHistogram order.symm area.histBase
      ∀ (room : Rooms n hist w start positions blocks leafTag vs) {pcs regs : ℕ}
        (V : Placement (TerminalProgram.nativeSegments B constants p q order) pcs regs)
        (M : Machine w pcs regs 11) (m : Memory w),
        Contains V M → LevelMemory B f hf blocks budget X branch n w start positions width
          room M.publicData m →
        ∀ (data : Fin 10 → Word w) (vals : LeafSourceLoad.Static 34 → Word w) (nodeCap limit
          power scanCap : ℕ),
        n ≤ nodeCap → limit < 2 ^ w → 1 ≤ power →
        Site.scan B (RefreshBlockPlan.order B)
          (LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)) order ≤ scanCap →
        ∀ (handlers : NodeDispatch.Role → HookParser w n), handlers .refresh =
          SelectedRows.parser n hist w start positions blocks width leafTag vs room order
            M.publicData m →
        let prepared := Budgeted area.arguments packetFormat (VertexFrameData area data
          roleWord vals) treeDesc histogram nodeCap limit
        let checkJob := JobGuard V M m (TerminalLink.workerCell (TerminalLink.header M.publicData))
          (ordinalJobCost n power scanCap)
        ∀ i : Fin vs.length, tagLevel B f hf vs[i] = .refresh →
          LevelChecks B f hf (dispatcher handlers m roleWord) prepared histogram checkJob
            B.recordLimit
            (layerBase B.recordLimit rowBase tags i.val) vs[i] := by
  filter_upwards [Site.eventually_dispatched_guard B order constants p q] with n bound
  intro K _ f hf lanes blocks budget X branch w start positions width vs leafTag rowBase tags
    rowWords roleWord area
    packetFormat treeDesc histogram room pcs regs V M m link memory data vals nodeCap limit
      power scanCap capFit limitFit hp hs
    handlers refresh prepared checkJob i tag
  apply assemble B f hf order blocks budget X branch n w start positions width room constants
    p q V M m memory
    data vals nodeCap limit power scanCap handlers refresh capFit limitFit _ i tag
  intro x s bs tail body prep hit
  let R := rowSite n hist w start positions blocks width leafTag vs room x
  obtain ⟨prev, next, layout⟩ := memory.layout x
  have dispatch := (level_dispatch B f hf blocks budget X branch n hist w start positions
    width room x
    (rowWords + width) (TerminalLink.header M.publicData) m memory.tags memory.codes
      memory.tagEnd memory.headerFit).1
  rw [level_parent B f hf blocks budget X branch n hist w start positions width room x] at dispatch
  exact (bound R V M m start positions blocks prev next link (memory.published x) layout dispatch
    (memory.later x) power scanCap hp hs s bs tail body prep hit).2

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
