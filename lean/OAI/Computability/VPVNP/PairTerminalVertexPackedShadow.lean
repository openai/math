import OAI.Computability.VPVNP.PairTerminalVertexPackedHeaders
import OAI.Computability.VPVNP.PairNativeFramePrepared

/-!
# Auxiliary reset memory through the physical terminal stages

The low addresses of the prepared auxiliary input survive the bootstrap
publication, prefix scan, and descriptor-row stage. After the shared scan,
a site flush preserves the entire reserved auxiliary interval. The resulting
readback supplies the typed leaf reader for the nominated grammar counters.
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

/-- The physical prefix exit preserves every calendar cell below the header
outside the actual final-level prefix destination. This also covers retained
tables above that destination. -/
theorem Start.calendarDirectory (D : DescriptorSpace.Layout) (last limit r : ℕ)
    (A : TerminalBootstrap.Header D last) (ready : TerminalBootstrap.Ready D last A pub calendar)
    (exp : (pub 7).val=r) (hr : r<w) (reserve : 32 ≤ D.base+2^r*2^r)
    (word : D.base+2^r*2^r ≤ 2^w)
    (s : Start workers pub cap fuel X T base calendar (TerminalBootstrap.report D.shape limit pub 0 calendar) rs)
    (x : ℕ) (before : x < (header pub).val)
    (apart : x < base.val ∨ base.val+arcCount X ≤ x) :
    prefixMemory pub calendar (TerminalBootstrap.report D.shape limit pub 0 calendar) rs x = calendar x := by
  let H := header pub
  have addr : H.val = TerminalBootstrap.address D.base r := header_val D pub r ready.workspace exp hr reserve word
  have room : H.val+32 ≤ 2^w := by rw [addr,TerminalBootstrap.address]; omega
  change x < H.val at before
  have at12 : (H+12).val = H.val+12 := at_offset H room 12 (by decide)
  have at14 : (H+14).val = H.val+14 := at_offset H room 14 (by decide)
  have at31 : (H+31).val = H.val+31 := at_offset H room 31 (by decide)
  have frame := s.rawScan.stored.outside x (by change x≠(H+12).val; omega) apart
  have unchanged : after (after calendar (TerminalBootstrap.report D.shape limit pub 0 calendar).events)
      (eventLog rs) x = after calendar (TerminalBootstrap.report D.shape limit pub 0 calendar).events x :=
    frame.trans (ite_eq_right (by change x≠(H+14).val; omega))
  exact ((s.handoff_rows.1 x ⟨before.ne,by change x≠(H+31).val; omega⟩).symm.trans unchanged).trans
    ((TerminalBootstrap.native D last A limit pub calendar 0 ready r exp hr reserve word).2.2.2.1 x
      (.inl (before.trans_eq addr)))

theorem Start.calendarBelow (D : DescriptorSpace.Layout) (last limit r : ℕ)
    (A : TerminalBootstrap.Header D last) (ready : TerminalBootstrap.Ready D last A pub calendar)
    (exp : (pub 7).val=r) (hr : r<w) (reserve : 32 ≤ D.base+2^r*2^r)
    (word : D.base+2^r*2^r ≤ 2^w)
    (s : Start workers pub cap fuel X T base calendar (TerminalBootstrap.report D.shape limit pub 0 calendar) rs)
    (below : base.val + arcCount X ≤ (header pub).val) (x : ℕ) (lo : x < base.val) :
    prefixMemory pub calendar (TerminalBootstrap.report D.shape limit pub 0 calendar) rs x = calendar x :=
  s.calendarDirectory D last limit r A ready exp hr reserve word x
    (lo.trans_le ((Nat.le_add_right _ _).trans below)) (.inl lo)

end PairSimulation.TerminalPrefix.Linked

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM PrivateRAM Compression PairSimulation CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles TerminalLink PrimedInputRAM PrimedCounter NativeFrame LiveAuxiliaryHeaders
open scoped Fin.CommRing

variable {G : Group} {D : DescriptorSpace.Layout} {cap width ord : ℕ} {roles : List TaggedLayer}
local notation "pub" => terminalOperands G
local notation "H" => vertexHeader G
local notation "size" => tagWords cap roles
local notation "first" => endAddress D

open private at_offset from OAI.Computability.VPVNP.PairTerminalVertexFrameLinked

theorem VertexPacked.traversalBelow (P : VertexPacked G D cap roles width)
    (workers : TerminalLink.Stage → PairTable) (fuel outer calls probes : ℕ) (src phy : Memory G.w)
    (out : List (Report G.w))
    (segment : TraversalController.Segment (TraversalController.Native.machine pub).program fuel
      (some 0) none src (build cap first first (roles.map TaggedLayer.layer)
        (writeTags (size+width) cap first roles src)) calls probes out)
    (stage : StageRun workers pub outer (.resume TerminalLink.Stage.traversalRows 0) src phy
      (List.replicate calls []) out)
    (x : ℕ) (hx : x < first) :
    after phy (eventLog (stageReports H (.resume TerminalLink.Stage.traversalRows 0) out)) x = src x := by
  have at31 : (H+31).val = (H).val+31 := at_offset _ P.room 31 (by decide)
  have hi := P.arena
  have safe : workerCell H x := ⟨by omega,by omega⟩
  have agree := (stage.agree x safe).symm
  rw [segment.memory,build_outside _ _ _ _ _ _ (.inl hx),
    write_tags_outside _ _ _ _ _ _ (.inl (hx.trans_le (Nat.le_add_left _ _)))] at agree
  exact agree

variable {i : Fin (2^(sizes G).h)} {before reference m bootMem : Memory G.w}
variable {N : Indexed G LiveProgram.Stage.nominations before (Nominations.Nom G)} {μ : Nominations.Nom G}
variable {hdr : Header (pairLengths G i) → Bool}

/-- The native vertex's immutable geometry and shadow suffice for the actual
typed auxiliary leaf, including the original nominal production words. -/
theorem VertexPacked.leafOperands (P : VertexPacked G D cap roles width)
    (frame : LinkedVertexMemory G reference ord m) (B : PreparedBranch G before i hdr N μ)
    (Q : PrimedInputRAM.Layout (pairLengths G i) G.g.n G.g.d G.g.H G.w) (degree : Fin G.g.n)
    (root : Fin (states G)) (slotDegree : ℕ) (role : Word G.w) {b l : ℕ}
    (read : NativeFrame.Readback reference H first size (cap+2) (2^b) (2^l)
      (TerminalBootstrap.shadowSpan pub bootMem))
    (descriptor : bootMem (histogramCell G) = B.copy.memory () (histogramCell G))
    (stored : ∀ j < span (pairLengths G i) (histLength G),
      reference ((pub 3).val+j) = headerMemory (pairLengths G i) hdr (histogram G μ) j)
    (hn : 1 ≤ G.g.n) (capacity : span (pairLengths G i) (histLength G) ≤ 2^(virtualSiteExponent G.g.d G.g.n))
    {p r k : ℕ} (pc : LeafImage.Label → Fin p) (reg : LeafImage.Reg ↪ Fin r)
    (operand : LeafImage.Pub → Fin k) (ret : Fin p) (M : Machine G.w p r k)
    (assigned : M.publicData ∘ operand = leafWords slotDegree pub H role m ∘ LeafGeometryLoad.slot)
    (sizeFit : G.g.n < 2^G.w) (shapeFit : max (cap+2) (max (2^b) (2^l)) < 2^G.w) :
    LeafFront.Operands (LeafImage.front pc reg operand ret) M m
      (Data.ofNomination Q degree root hdr (nominationEquiv G μ)) (fromHeader slotDegree pub H m) b l cap ∧
    M.publicData (operand .size) = (G.g.n : Word G.w) := by
  have shadowFit : shadowBase G < 2^G.w := by
    have baseFit := P.fit
    change shadowBase G + _ < 2^G.w at baseFit
    omega
  have baseVal : (pub 3).val = shadowBase G := Nat.mod_eq_of_lt shadowFit
  have room := shadow_span_room G i hn P.fit capacity
  have extent : shadowBase G + span (pairLengths G i) (histLength G) ≤ 2^G.w :=
    baseVal ▸ (room.trans (pub 2).isLt.le)
  apply B.leafOperands Q degree root slotDegree H role bootMem m (P.geometry frame read) descriptor
    _ pc reg operand ret M assigned P.fit sizeFit shapeFit extent
  intro j hj
  exact ((P.shadow frame i hn capacity hj).trans (stored j hj)).trans (B.shadowRead j).symm

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
