import OAI.Hierarchy.TraceReceiverRootBounds
import OAI.Hierarchy.TraceReceiverRootRetain

namespace OAI
/-! # Selected-root bounds in the actual evolving terminal memory -/

noncomputable section
namespace Hierarchy.TraceReceiverRootRetain
open ThreeFlat Diagonal PhysicalStage HistoryContraction RAM
open TickTerminalRoot HistoryStageBody.Physical HistoryStageSetup TickWorkspace
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Fin.CommRing Classical

variable {W u B p n d l : ℕ} {F Pins : Type} [Field F] [Fintype F]

/-- The original S11, S13, S17, S43, S44, and final half-table observations
at one selected root. Every member refers to the single pre-map image. -/
structure Publication (u B p suffix seeds heapLo heapHi : ℕ) (initial scan : Memory W)
    (X : State d l) (L : X.Words Pins) (O : X.ArchiveSites) (z : X.Site)
    (value : NodeValue F) (tag : ((Fin 3→Bool)→F)→ℕ) (b : NavigationNodeRows.Banks)
    (x : TerminalWireArchive.Layout) (i : Fin n) (rows : Fin n→ℕ) : Prop where
  sector : base u 45≤B
  sectorFit : B<2^W
  large : 162≤volume u
  nodesFit : O.layer.first+O.layer.count≤volume u
  count : n≤volume u
  records : ∀ j,4*rows j≤volume u
  degree : 2*d≤volume u
  pinLimit : value.pins≤volume u
  word : 2+p<2^W
  suffixIn : suffix≤p
  heapStart : base u 18+stride u≤heapLo
  heapEnd : heapHi≤B
  wireStart : base u 18+stride u≤x.prefixBase
  wireEnd : x.prefixBase+X.edgeCount≤B+16
  wireFit : TerminalWireArchive.Bounds x W
  edgeCount : x.edges=X.edgeCount
  widths : ∀ j : Fin X.edgeCount,(scan (x.widthBase+j.val)).val=X.wireWidth j
  wireCapacity : X.widthSum≤x.capacity
  emitted : ∀ j : Fin X.edgeCount,initial (x.prefixBase+j.val)=TerminalWireArchive.image x scan (x.prefixBase+j.val)
  picked : natMemory initial (base u 17+i.val)=(O.ord z).val
  first : natMemory initial (TickPhysicalABI.directory u 3)=O.layer.first
  nodePointer : natMemory initial (TickPhysicalABI.directory u 3+1)=b.nodes
  nodeBank : b.nodes=base u 44
  chargeBank : b.charges=base u 43
  directory : DirectoryRow b O.layer (O.ord z) initial
  posted : X.HalfRows O (fun a=>heapLo≤a ∧ a<heapHi) (natMemory initial)
  cache : value.Cached tag u (O.id z) initial
  external : value.external=L.ext z
  localPins : value.pins=L.ports.form.width z
  stream : value.stream=streamAt u seeds (O.id z)
  endpoints : value.ext=endsAt u seeds (O.id z)
  rowCount : rows i=value.net.cells

omit [Field F] [Fintype F] in
/-- Only two live words vary over map iterations. All root-specific source
data and archived pointers are recovered through the physically retained frame. -/
theorem selected_of_frame {suffix seeds heapLo heapHi : ℕ} {initial scan live : Memory W}
    {X : State d l} {L : X.Words Pins} {O : X.ArchiveSites} {z : X.Site}
    (order : X.OrderedHalves L) {value : NodeValue F} {tag : ((Fin 3→Bool)→F)→ℕ}
    {b : NavigationNodeRows.Banks} {x : TerminalWireArchive.Layout} {i : Fin n} {rows : Fin n→ℕ}
    (pub : Publication u B p suffix seeds heapLo heapHi initial scan X L O z value tag b x i rows)
    (frame : Frame u B initial live) (ordinal : natMemory live (base u 18)=i.val)
    (written : natMemory live (base u 18+2)=Tree.before rows i) :
    let A:=mounted u p (2+suffix) x.prefixBase
    RootBounds A live ∧ TraceReceiverTerminalMap.HalfRows X L z (terminal A (natMemory live)) (natMemory live) suffix ∧
      CompactRootAt u p (2+suffix) x.prefixBase live ∧ value.Cached tag u (O.id z) live := by
  have wide:=(slot_room pub.large).1
  have track : (O.id z)<volume u := by
    have lower:=(O.ord z).isLt
    have top:=pub.nodesFit
    change O.layer.first+(O.ord z).val<volume u
    omega
  have record:=pub.records i
  rw [pub.rowCount] at record
  have ports : value.external≤volume u := by
    have low : L.ext z≤L.ports.form.width z := Nat.le_add_right ..
    rw [←pub.external,←pub.localPins] at low
    exact low.trans pub.pinLimit
  have liveCache:=cached value tag frame pub.large track record ports pub.stream pub.endpoints pub.cache
  have nodeRow:=directory O z b frame pub.large pub.sector pub.nodesFit pub.nodeBank pub.chargeBank pub.directory
  have halfRow:=half_rows O frame (by omega) pub.heapStart pub.heapEnd pub.posted
  have high:=pub.wireStart
  have oldPick:=pick frame (i:=i.val) (by have h:=i.isLt;have nfit:=pub.count;omega) pub.picked
  have prefixKept:=«prefix» (edges:=X.edgeCount) x scan frame (by omega) pub.wireEnd pub.emitted
  have bounds:=TraceReceiverRootBounds.selected live scan X L O z order value tag b x i rows
    (pub.sector.trans_lt pub.sectorFit) pub.large pub.nodesFit pub.count pub.records pub.degree pub.pinLimit
    pub.word pub.suffixIn pub.heapStart (pub.heapEnd.trans pub.sectorFit.le) pub.wireStart pub.wireFit
    pub.edgeCount pub.widths pub.wireCapacity prefixKept ordinal oldPick
    (first frame (by omega) pub.first) (node_pointer frame (by omega) pub.nodePointer) pub.nodeBank
    nodeRow halfRow liveCache pub.external pub.localPins pub.stream pub.endpoints written pub.rowCount
  exact ⟨bounds.1,bounds.2.1,bounds.2.2,liveCache⟩


end Hierarchy.TraceReceiverRootRetain

end
end OAI
