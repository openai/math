import OAI.Hierarchy.TraceReceiverFramedRoot
import OAI.Hierarchy.TraceReceiverBeforeSelected

namespace OAI
/-! # The elected node publications after the actual parent mount and prefix scans -/

noncomputable section
namespace Hierarchy.TraceReceiverRootRetain
open ThreeFlat Diagonal PhysicalStage RAM TickWorkspace
open TickTerminalRoot HistoryStageBody.Physical Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical

variable {W u B p n d l suffix seeds heapLo heapHi : ℕ} {F Pins : Type} [Field F] [Fintype F]
variable {X : State d l} {L : X.Words Pins} {O : X.ArchiveSites} {z : X.Site}
variable {value : NodeValue F} {tag : ((Fin 3→Bool)→F)→ℕ}
variable {b : NavigationNodeRows.Banks} {x : TerminalWireArchive.Layout}
variable {initial scan live : Memory W}

omit [Field F] [Fintype F] in
/-- A cache, selected roster and wire scan entirely below the start of the
temporary arena survive any publisher that preserves every address below it. -/
theorem Publication.of_below {i : Fin n} {rows : Fin n→ℕ}
    (pub : Publication u B p suffix seeds heapLo heapHi initial scan X L O z value tag b x i rows)
    (preserved : ∀ a<B,live a=initial a) (sectorMargin : base u 45≤B-16)
    (heapMargin : heapHi≤B-16) (edgeEnd : x.prefixBase+X.edgeCount≤B) :
    Publication u B p suffix seeds heapLo heapHi live scan X L O z value tag b x i rows := by
  have wide:=(slot_room pub.large).1
  have lower:=apart (u:=u) (by decide : 14<45)
  have upper:=apart (u:=u) (by decide : 18<45)
  have margin : 16≤B := by omega
  have frame : Frame u (B-16) initial live := by
    intro a band
    apply preserved
    rcases band with low|roster|old <;> omega
  have idx : O.id z<volume u := by
    change O.layer.first+(O.ord z).val<volume u
    have nfit:=pub.nodesFit
    have rank:=(O.ord z).isLt
    omega
  have records:=pub.records i
  rw [pub.rowCount] at records
  have extBound : value.external≤volume u := by
    have ext : L.ext z≤L.ports.form.width z := Nat.le_add_right ..
    rw [←pub.external,←pub.localPins] at ext
    exact ext.trans pub.pinLimit
  have wireLow:=pub.wireStart
  have inc:=half_rows O frame (by omega) pub.heapStart heapMargin pub.posted
  have cache:=cached value tag frame pub.large idx records extBound pub.stream pub.endpoints pub.cache
  have table:=TraceReceiverRootRetain.directory O z b frame pub.large sectorMargin pub.nodesFit pub.nodeBank pub.chargeBank pub.directory
  have wire:=«prefix» (edges:=X.edgeCount) x scan frame (by omega) (by omega) pub.emitted
  have selected:=TraceReceiverRootRetain.pick frame (i:=i.val) (by have h:=i.isLt;have count:=pub.count;omega) pub.picked
  exact ⟨pub.sector,pub.sectorFit,pub.large,pub.nodesFit,pub.count,pub.records,pub.degree,pub.pinLimit,
    pub.word,pub.suffixIn,pub.heapStart,pub.heapEnd,pub.wireStart,pub.wireEnd,pub.wireFit,
    pub.edgeCount,pub.widths,pub.wireCapacity,wire,selected,TraceReceiverRootRetain.first frame (by omega) pub.first,
    node_pointer frame (by omega) pub.nodePointer,pub.nodeBank,pub.chargeBank,table,inc,cache,
    pub.external,pub.localPins,pub.stream,pub.endpoints,pub.rowCount⟩

omit [Field F] [Fintype F] in
/-- The selected publisher mounted the physical parent and executed all three
prefix scans before the map loop. Its own proved memory frame transports the
elected facts into that exact memory. -/
theorem Publication.prepared {N : ℕ} {ids : List (Fin N)} {i : Fin ids.length}
    {rows : Fin ids.length→ℕ} {A : GridReceiverTickDirectory.Banks} {D : TraceReceiverTasks.Layout}
    {count cap origin rootBase physicalPins : ℕ} {width : Fin 3→ℕ} {amount : Fin 3→Fin ids.length→ℕ}
    (pub : Publication u B p suffix seeds heapLo heapHi initial scan X L O z value tag b x i rows)
    (facts : TraceReceiverTasks.SelectedInputFacts A D ids count cap width origin amount initial rootBase physicalPins)
    (current : D.current=B) (sectorMargin : base u 45≤B-16) (heapMargin : heapHi≤B-16)
    (edgeEnd : x.prefixBase+X.edgeCount≤B) :
    Publication u B p suffix seeds heapLo heapHi
      (TraceReceiverTasks.beforeImage D count cap width ids.length
        (TraceAdmission.Resources.mounted D.parent [rootBase,physicalPins,0,0] initial))
      scan X L O z value tag b x i rows :=
  pub.of_below (fun a h=>facts.frame a (by simpa only [current] using h)) sectorMargin heapMargin edgeEnd

end Hierarchy.TraceReceiverRootRetain

end
end OAI
