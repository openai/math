import OAI.Computability.VPVNP.PairTerminalVertexPackedStage
import OAI.Computability.VPVNP.PairTerminalSelectedHeaders
import OAI.Computability.VPVNP.PairTerminalVertexPackedGather
import OAI.Computability.VPVNP.PairTerminalPrefixLinked
import OAI.Computability.VPVNP.PairTraversalControllerTerminal

/-!
# Terminal bootstrap fields at the native vertex handoff

The prefix scan changes the total and role displacement. The traversal writes
the selected rows and tags, and the shared-bit scan writes the selected bit
bank. All three physical phases preserve the bootstrap values used by the
root gather and by the per-site geometry initializer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalPrefix.Linked

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace TerminalLink
open scoped Fin.CommRing

variable {w a g : ℕ} {workers : TerminalLink.Stage → LiveProgram.PairTable}
variable {pub : Fin 11 → Word w} {cap fuel : ℕ} {X : State a g} {T : IncidenceDirectory w}
variable {base : Word w} {calendar : Memory w} {rs : List (Report w)}

open private at_offset from OAI.Computability.VPVNP.PairTerminalVertexFrameLinked

/-- Only the running total, the role offset and the two terminal controls
can differ from the bootstrap image inside the header. -/
theorem Start.prefixField {raw : Report w} (s : Start workers pub cap fuel X T base calendar raw rs)
    (room : (header pub).val+32 ≤ 2^w) (below : base.val + arcCount X ≤ (header pub).val)
    (j : ℕ) (lo : 0<j) (hi : j<31) (total : j≠12) (role : j≠14) :
    prefixMemory pub calendar raw rs (header pub+(j : Word w)).val =
      after calendar raw.events (header pub+(j : Word w)).val := by
  let H := header pub
  let x := (H+(j : Word w)).val
  have atJ : x = H.val+j := at_offset H room j (by omega)
  have at12 : (H+12).val = H.val+12 := at_offset H room 12 (by decide)
  have at14 : (H+14).val = H.val+14 := at_offset H room 14 (by decide)
  have at31 : (H+31).val = H.val+31 := at_offset H room 31 (by decide)
  have area : workerCell H x := ⟨by omega,by omega⟩
  have before : base.val+arcCount X ≤ H.val := below
  have kept := s.rawScan.stored.outside x (by change x ≠ (H+12).val; omega) (Or.inr (by omega))
  change after (after calendar raw.events) (eventLog rs) x =
    writeMemory (after calendar raw.events) (H+14) _ x at kept
  exact (s.handoff_rows.1 x area).symm.trans (kept.trans (ite_eq_right (by omega)))

/-- Read every unaffected bootstrap publication from the exact physical prefix
exit. The width and prefix pointers, terminal site count, row interval, and
both radices are instances of this one formula. -/
theorem Start.bootstrapField (D : DescriptorSpace.Layout) (last limit r : ℕ)
    (A : TerminalBootstrap.Header D last) (ready : TerminalBootstrap.Ready D last A pub calendar)
    (exp : (pub 7).val=r) (hr : r<w) (reserve : 32 ≤ D.base+2^r*2^r)
    (word : D.base+2^r*2^r ≤ 2^w)
    (s : Start workers pub cap fuel X T base calendar (TerminalBootstrap.report D.shape limit pub 0 calendar) rs)
    (below : base.val + arcCount X ≤ (header pub).val)
    (j : Fin 21) (lo : 0<j.val) (total : j.val≠12) (role : j.val≠14) :
    prefixMemory pub calendar (TerminalBootstrap.report D.shape limit pub 0 calendar) rs
      (header pub+(j.val : Word w)).val = TerminalBootstrap.values D last A limit pub calendar j := by
  have addr : (header pub).val = TerminalBootstrap.address D.base r :=
    header_val D pub r ready.workspace exp hr reserve word
  have fit : (header pub).val+32 ≤ 2^w := by rw [addr,TerminalBootstrap.address]; omega
  have ix := j.isLt
  rw [s.prefixField fit below j.val lo (by omega) total role,at_offset _ fit _ (by omega),addr]
  exact (TerminalBootstrap.native D last A limit pub calendar 0 ready r exp hr reserve word).2.2.1 j

end PairSimulation.TerminalPrefix.Linked

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM PrivateRAM Compression PairSimulation CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles TerminalLink
open scoped Fin.CommRing

variable {G : Group} {D : DescriptorSpace.Layout} {limit width : ℕ} {roles : List TaggedLayer}
local notation "pub" => terminalOperands G
local notation "H" => vertexHeader G
local notation "size" => tagWords limit roles
local notation "first" => endAddress D

open private at_offset from OAI.Computability.VPVNP.PairTerminalVertexFrameLinked

/-- The traversal controller's physical handoff preserves all high data
fields. The raw memory image comes from its verified native Segment. -/
theorem VertexPacked.traversalField (P : VertexPacked G D limit roles width)
    (workers : TerminalLink.Stage → PairTable) (fuel cap calls probes : ℕ) (src phy : Memory G.w)
    (out : List (Report G.w))
    (segment : TraversalController.Segment (TraversalController.Native.machine pub).program fuel
      (some 0) none src (build limit first first (roles.map TaggedLayer.layer)
        (writeTags (size+width) limit first roles src)) calls probes out)
    (stage : StageRun workers pub cap (.resume TerminalLink.Stage.traversalRows 0) src phy
      (List.replicate calls []) out)
    (j : ℕ) (lo : 0<j) (hi : j<31) :
    after phy (eventLog (stageReports H (.resume TerminalLink.Stage.traversalRows 0) out))
      (H+(j : Word G.w)).val = src (H+(j : Word G.w)).val := by
  let x := (H+(j : Word G.w)).val
  have atJ : x = (H).val+j := at_offset _ P.room _ (by omega)
  have at31 : (H+31).val = (H).val+31 := at_offset _ P.room 31 (by decide)
  have area : workerCell H x := ⟨by omega,by omega⟩
  have eqn := (stage.agree x area).symm
  rw [segment.memory] at eqn
  exact eqn.trans (TerminalLayout.arena_above limit first width roles src x
    (P.arena.trans (atJ ▸ Nat.le_add_right _ _)))

/-- Numeric operands of the root gather, decoded from the selected bootstrap
publications. Each natural address is strictly below the word modulus. -/
theorem VertexPacked.gatherValues (P : VertexPacked G D limit roles width)
    {a k : ℕ} (X : State a k) (prior : List Layer) (last : Fin D.levels) (tab : Fin D.shape.tables)
    (index : last.val=prior.length) (b l : ℕ) (reference calendar : Memory G.w)
    (slots : TerminalPrefix.arcCount X ≤ slotCapacity D) (cells : TerminalPrefix.arcCount X ≤ tableWords D)
    (sizeEq : (TerminalBootstrap.fromState D prior limit b l X tab).rowWords limit = size)
    (fields : ∀ i : Fin 21, i.val ∈ ([7,8,9,10,11,13] : List ℕ) →
      reference (H+(i.val : Word G.w)).val = TerminalBootstrap.values D prior.length
        (TerminalBootstrap.fromState D prior limit b l X tab) limit pub calendar i) :
    (reference (H+7).val).val = (LocalHistory.siteOrder X).length ∧
      (reference (H+8).val).val = TerminalPrefix.arcCount X ∧
      (reference (H+10).val).val = incidenceBase D last (TerminalPrefix.arcCount X) 4 ∧
      (reference (H+9).val).val = incidenceBase D last (TerminalPrefix.arcCount X) 5 ∧
      (reference (H+11).val).val = DescriptorSpace.tableBase D last tab ∧
      (reference (H+13).val).val = first+size := by
  let A := TerminalBootstrap.fromState D prior limit b l X tab
  let arcs := TerminalPrefix.arcCount X
  have siteCount : (LocalHistory.siteOrder X).length = X.positions := by
    change (LocalHistory.siteOrder X).length = Fintype.card X.network.Site
    simpa only [Fintype.card_fin] using Fintype.card_congr (LocalHistory.siteOrder X).entries
  have eqSites : A.sites = X.positions := TerminalBootstrap.fromState_sites ..
  have eqSlots : A.sites*A.degree = arcs :=
    (congrArg (· * 2^a) eqSites).trans (TerminalPrefix.Segment.arc_count_positions X).symm
  have small : first < 2^G.w := by have h := P.arena; have q := P.room; omega
  have headBound (head : ℕ) (hh : head ∈ [incidenceBase D last arcs 4,incidenceBase D last arcs 5,
      DescriptorSpace.tableBase D last tab]) : head+arcs < 2^G.w :=
    ((P.heads last tab arcs slots cells head hh).2).trans_lt small
  have inv := headBound _ (List.mem_cons_self ..)
  have wid := headBound _ (by apply List.mem_cons_of_mem; exact List.mem_cons_self ..)
  have start := headBound (DescriptorSpace.tableBase D last tab) (by simp)
  have bound := P.arena
  have room := P.room
  have siteLe : X.positions ≤ arcs := by
    rw [show arcs = X.positions * 2^a from TerminalPrefix.Segment.arc_count_positions X]
    exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have exactWord {n : ℕ} {v : Word G.w} (h : v=(n : Word G.w)) (hn : n<2^G.w) :
      v.val=n := h ▸ Nat.mod_eq_of_lt hn
  have s7 : reference (H+7).val = (A.sites : Word G.w) := fields 7 (by decide)
  have s8 : reference (H+8).val = ((A.sites*A.degree : ℕ) : Word G.w) := fields 8 (by decide)
  have s10 : reference (H+10).val = ((incidenceBase D prior.length (X.positions*2^a) 4 : ℕ) : Word G.w) :=
    fields 10 (by decide)
  have s9 : reference (H+9).val = ((incidenceBase D prior.length (X.positions*2^a) 5 : ℕ) : Word G.w) :=
    fields 9 (by decide)
  have s11 : reference (H+11).val = ((DescriptorSpace.tableBase D prior.length tab : ℕ) : Word G.w) :=
    fields 11 (by decide)
  have s13 : reference (H+13).val = ((first+A.rowWords limit : ℕ) : Word G.w) := fields 13 (by decide)
  have eqArc : X.positions*2^a = arcs := (TerminalPrefix.Segment.arc_count_positions X).symm
  rw [eqSites] at s7
  rw [eqSlots] at s8
  rw [← index,eqArc] at s10 s9
  rw [← index] at s11
  change A.rowWords limit = size at sizeEq
  rw [sizeEq] at s13
  exact ⟨(exactWord s7 (by omega)).trans siteCount.symm,exactWord s8 (by omega),
    exactWord s10 ((Nat.le_add_right _ arcs).trans_lt inv),exactWord s9 ((Nat.le_add_right _ arcs).trans_lt wid),exactWord s11 (by omega),exactWord s13 (by omega)⟩

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
