import OAI.ThreeFlat.Diagonal.InitialSeedMount
import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.ThreeFlat.Diagonal.NavigationArchiveVisit
import OAI.ThreeFlat.Diagonal.SeedNodeRows

namespace OAI
/-! # Initial cursor graph, native seed rows and repetition counter at trace word width -/
namespace Hierarchy.TraceSeedWriter
open ThreeFlat ThreeFlat.Diagonal
open ThreeFlat.Diagonal.NavigationPass
open ThreeFlat.Diagonal.NavigationPass.Archive
open NavigationDirectory
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalProcedure
open CompressorPacking.Native
open scoped Classical Fin.CommRing
noncomputable section
variable {W : ℕ} (A : Archive) (ss : List NavigationDirectory.Stage) (edges : ℕ)
set_option quotPrecheck false
local notation "cur" => (A.control:Word W)
local notation "ctr" => ((A.control+1:ℕ):Word W)
local notation "C" => (⟨A.cursor.graph,A.axes*A.initialDegree,A.cursor.width⟩ : SlotImage.Columns)
local notation "R" => A.axes*A.initialDegree
local notation "IB" => InitialRelayBootstrap.procedure cur C A.axes A.initialDegree A.relayWidth
local notation "relay" => InitialRelayBootstrap.image C A.axes A.initialDegree A.remainingLanes A.relayWidth


/-- Source and output of the graph, width and metadata scans all precede the control pair. -/
structure Space (W : ℕ) : Prop extends A.RelayWindow W where
  widthsToRecords : A.cursor.width+A.axes*A.initialDegree*A.remainingLanes≤A.initialRecords
  recordsToControl : A.metadataEnd≤A.control
  counterFit : A.control+1<2^W

variable {A}
theorem Space.meta (s : Space A W) : A.MetadataSpace W where
  controlRoom := s.controlRoom
  control := .inr s.recordsToControl
  header := s.seedBefore.trans (s.toRelayWindow.columns.1.trans ((Nat.le_add_right ..).trans s.widthsToRecords))
  endFit := s.recordsToControl.trans_lt s.controlRoom

variable (A)
def procedure (blocks : ℕ) : Procedure W :=
  (A.boot ss edges).seq ((IB).seq (A.initialMetadata.seq ((start cur A.cursor.header).seq (start ctr blocks))))

def memory (library : List ℕ) (raw : ℕ→Bool) (input : Memory W) (blocks : ℕ) : Memory W :=
  let mount:=A.mountedMemory ss edges library raw input
  let data:=A.metadataMemory (relay mount)
  writeMemory (writeMemory data cur (A.cursor.header:Word W)) ctr (blocks:Word W)

variable {F : Type} [Field F] (P : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k+1) (low off slots : ℕ)
local notation "X" => P.cursorState hk low off slots

structure Ready (de : 2^(P.exponent 0)=A.initialDegree) (ax : k+1=A.axes)
    (raw : ℕ→Bool) (blocks : ℕ) (input out : Memory W) : Prop where
  nodes : A.InitialNodeMetadata (Archive.reseedDegree de (X).graph) (finCongr ax) (fun _=>A.relayWidth) out
  slots : SlotImage.Stored (X).graph (X).order (tagOrdinal _) C (fun i=>(out i).val) (X).width
  live : A.Live ss edges raw cur A.cursor out
  counter : (out (ctr).val).val=blocks
  low : ∀i,i<A.seed → out i=input i

theorem ready (de : 2^(P.exponent 0)=A.initialDegree) (ax : k+1=A.axes)
    (lanes : A.remainingLanes=2^(k+1)) (wire : A.relayWidth=2^low*(off*slots*3))
    (library suffix : List ℕ) (raw : ℕ→Bool) (input : Memory W) (blocks : ℕ) (s : Space A W)
    (banks : A.MountedRange ss edges W) (src : A.SeedSources ss edges library suffix raw input)
    (bits : A.relayWidth<2^W) (axesWord : k+1≤W) (degreeWord : 2*A.initialDegree<2^W)
    (laneWord : 2^(k+1)<2^W) (wide : 8<2^W) (first : A.cursor.header=A.seed+64)
    (countFit : blocks<2^W) :
    Ready A ss edges P hk low off slots de ax raw blocks input (memory A ss edges library raw input blocks) := by
  let m0:=A.mountedMemory ss edges library raw input
  let m1:=relay m0
  let m2:=A.metadataMemory m1
  let out:=memory A ss edges library raw input blocks
  have mounted:=src.mounted_of_window s.toRelayWindow banks
  have H:=s.toRelayWindow.relay_header mounted.1
  have gr : (C).graph+6*(C).rows≤A.control := s.graphBefore.trans ((Nat.le_add_right ..).trans s.widthsBefore)
  have below : (C).graph≤A.control := (Nat.le_add_right ..).trans gr
  have wr : (C).widths+(C).rows*2^(k+1)≤A.control := by simpa only [lanes] using s.widthsBefore
  have typed:=A.cursorImage_of_window P hk low off slots de ax lanes m0 s.toRelayWindow bits axesWord
  have wr0 : (C).widths+(C).rows*2^(k+1)≤A.initialRecords := by simpa only [lanes] using s.widthsToRecords
  have g0 := s.graphBefore.trans ((Nat.le_add_right ..).trans s.widthsToRecords)
  have rows:= A.metadata_actual (Archive.reseedDegree de (X).graph) (finCongr ax) (fun _=>A.relayWidth) m1 s.meta H typed
    lanes g0 wr0 degreeWord laneWord wide
  have physical : SlotImage.Stored (X).graph (X).order (tagOrdinal _) C (fun i=>(m2 i).val) (X).width := by
    have eqWidth : (X).width = (fun _ => A.relayWidth) := by
      funext j
      rw [P.cursorState_width,wire]
    rw [eqWidth]
    exact Archive.stateImage (G := (X).graph) de ax rows.2
  have keep:= A.metadata_frame m1 s.meta H
  have cf := s.counterFit
  have current : (cur).val=A.control := Fin.val_cast_of_lt s.controlRoom
  have countCell : (ctr).val=A.control+1 := Fin.val_cast_of_lt cf
  have headFit : A.cursor.header<2^W := by rw [first];exact (s.seedBefore.trans below).trans_lt s.controlRoom
  have same (i : ℕ) (avoid : i<A.control ∨ A.control+1< i) : out i=m2 i := by
    change (if i=(ctr).val then (blocks : Word W) else
      if i=(cur).val then (A.cursor.header : Word W) else m2 i)=m2 i
    rw [current,countCell,ite_eq_right (by omega : i≠A.control+1),ite_eq_right (by omega : i≠A.control)]
  have lowFrame (i : ℕ) (h : i<(C).graph) : out i=m0 i :=
    (same i (.inl (h.trans_le below))).trans ((keep i (.inl (h.trans_le ((Nat.le_add_right ..).trans g0)))).trans
      (s.toRelayWindow.relay_frame m0 i (.inl h)))
  have head : (out (cur).val).val=A.cursor.header := by
    change (if (cur).val=(ctr).val then (blocks : Word W) else
      if (cur).val=(cur).val then (A.cursor.header : Word W) else m2 (cur).val).val=A.cursor.header
    rw [current,countCell,ite_eq_right (by omega : A.control≠A.control+1),ite_eq_left rfl,Fin.val_cast_of_lt headFit]
  refine ⟨Archive.InitialNodeMetadata.transfer A (Archive.reseedDegree de (X).graph) (finCongr ax)
    (fun _ => A.relayWidth) rows.1 lanes (fun i h=>same i (.inl (h.2.trans_le s.recordsToControl))),?_,?_,?_,?_⟩
  · apply physical.frame
    · intro i _ hi;exact congrArg Fin.val (same i (.inl (hi.trans_le gr)))
    · intro i _ hi;rw [←physical.rowCount] at hi;exact congrArg Fin.val (same i (.inl (hi.trans_le wr)))
  · exact Archive.Live.seed_frame banks mounted.2 (by change A.seed≤A.cursor.header;rw [first];omega) head lowFrame
  · change (if (ctr).val=(ctr).val then (blocks : Word W) else
      writeMemory m2 (cur) (A.cursor.header : Word W) (ctr).val).val=blocks
    rw [ite_eq_left rfl,Fin.val_cast_of_lt countFit]
  · intro i hi
    exact (lowFrame i (hi.trans_le ((Nat.le_add_right ..).trans s.seedBefore))).trans (src.before_of_window s.toRelayWindow i hi)


section
variable {F : Type} [Field F] {W k low off slots blocks : ℕ}
variable {P : PhysicalStage.Block F} {hk : 2≤k+1} {A : Archive} {ss : List Stage} {edges : ℕ}
variable {raw : ℕ→Bool} {input out : Memory W} {ax : k+1=A.axes} {de : 2^(P.exponent 0)=A.initialDegree}
theorem Ready.visit (r : Ready A ss edges P hk low off slots de ax raw blocks input out)
    (lanes : A.remainingLanes=2^(k+1)) (gLow : A.cursor.dense≤A.cursor.graph) (wLow : A.cursor.dense≤A.cursor.width)
    (gHigh : A.cursor.graph+6*(A.axes*A.initialDegree)≤A.cursor.heap)
    (wHigh : A.cursor.width+A.axes*A.initialDegree*A.remainingLanes≤A.cursor.heap) :
    A.Visit ss edges raw (A.control:Word W) [] (P.cursorState hk low off slots) out := by
  have card : Fintype.card (P.cursorState hk low off slots).Base=A.axes := (Fintype.card_fin (k+1)).trans ax
  have cols : RefreshStageNav.oldColumns A.cursor (Fintype.card (P.cursorState hk low off slots).Base) (2^P.exponent 0)=
      ⟨A.cursor.graph,A.axes*A.initialDegree,A.cursor.width⟩ := by unfold RefreshStageNav.oldColumns;rw [card,de]
  exact ⟨r.live,gLow,wLow,by simpa only [finish,card,de] using gHigh,
    by simpa only [finish,PhysicalStage.State.edgeCount,card,de,←lanes] using wHigh,
    by simpa only [finish,cols] using r.slots⟩

end

private theorem fixedInput {p : Procedure W} {pre : Memory W→Prop} {f : Memory W→Memory W} {n : ℕ}
    (run : p.Spec pre (fun m out=>out=f m) n) {m : Memory W} (take : pre m) :
    p.Spec (fun input=>input=m) (fun _ out=>out=f m) n := by
  intro n r k M pc reg pub exit inst rom c input entry same
  subst input
  exact run M pc reg pub exit inst rom c m entry take


/-- Execute the actual directory/histogram packers, graph, width and metadata scans and both clocks. -/
theorem run (library suffix : List ℕ) (raw : ℕ→Bool) (input : Memory W) (blocks : ℕ) (s : Space A W)
    (banks : A.MountedRange ss edges W) (src : A.SeedSources ss edges library suffix raw input)
    (degree : 0<A.initialDegree) (axesWord : A.axes≤W) (wide : 8<2^W) :
    (procedure A ss edges blocks).Spec (fun m=>m=input)
      (fun _ out=>out=memory A ss edges library raw input blocks) (A.bootTime ss edges W+A.seedTime+6) := by
  let m0:=A.mountedMemory ss edges library raw input
  let m1:=relay m0
  let m2:=A.metadataMemory m1
  let m3:=writeMemory m2 cur (A.cursor.header:Word W)
  have boot : (A.boot ss edges).Exec input m0 (A.bootTime ss edges W) :=
    src.boot_of_window (s:=s.toRelayWindow) banks
  have mounted:=src.mounted_of_window s.toRelayWindow banks
  have graphTop : (C).graph+6*R<2^W :=
    (s.graphBefore.trans ((Nat.le_add_right ..).trans s.widthsBefore)).trans_lt s.controlRoom
  have graphRun : (IB).Exec m0 m1 (InitialRelayBootstrap.budget W C A.axes A.initialDegree A.remainingLanes) := by
    intro programCount registerCount wordCount machine
    exact fixedInput (InitialRelayBootstrap.spec cur C A.axes A.initialDegree A.remainingLanes A.relayWidth
      graphTop (s.widthsBefore.trans_lt s.controlRoom) degree axesWord (by omega))
      (s.toRelayWindow.loaded mounted.1) machine
  have metadataRun : (A.initialMetadata : Procedure W).Exec m1 m2 (33+A.metadataUnit*A.initialSites) := by
    intro programCount registerCount wordCount machine
    apply Procedure.Spec.mono (A := A.initialMetadata)
      (A.metadata_spec m1 s.meta (s.toRelayWindow.relay_header mounted.1))
      (fun _ h => h) _ le_rfl machine
    exact fun _ _ h => h.1
  have pointerRun : (start cur A.cursor.header).Exec m2 m3 3 := by
    intro programCount registerCount wordCount machine
    exact fixedInput (m:=m2) (start_spec cur (A.cursor.header:Word W)) trivial machine
  have counterRun : (start ctr blocks).Exec m3 (writeMemory m3 ctr (blocks:Word W)) 3 := by
    intro programCount registerCount wordCount machine
    exact fixedInput (m:=m3) (start_spec ctr (blocks:Word W)) trivial machine
  have cost : A.bootTime ss edges W +
      (InitialRelayBootstrap.budget W C A.axes A.initialDegree A.remainingLanes +
        ((33+A.metadataUnit*A.initialSites)+(3+3))) = A.bootTime ss edges W+A.seedTime+6 := by
    rw [InitialRelayBootstrap.budget_eq, A.metadataUnit_eq, Archive.seedTime]
    omega
  rw [← cost]
  intro programCount registerCount wordCount machine
  exact Procedure.Exec.then boot (Procedure.Exec.then graphRun
    (Procedure.Exec.then metadataRun (Procedure.Exec.then pointerRun counterRun))) machine

/-- The public code has fixed size once the compressor degree is fixed. The
raw selector, native word width, initial layout and repetition count change
instruction operands while preserving these exact program dimensions. -/
theorem format (n : ℕ) :
    let p:=procedure (W:=W) A ss edges n
    p.labels=3346+1644*A.initialDegree ∧ p.registers=1119+548*A.initialDegree ∧ p.slots=0 := by
  have literal : (DescriptorExpr.Term.literal (A.relayWidth : Word W) : DescriptorExpr.Term W 0 1).binds=1 := rfl
  dsimp only
  simp only [procedure,Archive.boot,InitialRelayBootstrap.procedure,
    InitialRelayGraph.procedure,InitialRelayWidth.procedure,Archive.initialMetadata,
    PackedStageArchive.procedure,HeaderScan.procedure,start,Procedure.seq,
    DescriptorExpr.Term.labels_eq,InitialRelayBootstrap.graph_binds,HeaderScan.binds_closed,
    Archive.initialKernel_work,Archive.initialHalfHeader_work,Archive.initialHalf_work,literal]
  refine ⟨?_,?_,trivial⟩ <;> ring

/-- After the repeated-stage counter, every cell lies outside the graph, width
and metadata output ranges. The public parameter bank has an empty codebook. -/
theorem memory_above (bits : ℕ→Bool) (input : Memory W) (n : ℕ) (s : Space A W)
    (banks : A.MountedRange ss edges W) (src : A.SeedSources ss edges [] [] bits input)
    (i : ℕ) (above : A.control+1 < i) : memory A ss edges [] bits input n i=input i := by
  let m0:=A.mountedMemory ss edges [] bits input
  let m1:=relay m0
  have mounted:=src.mounted_of_window s.toRelayWindow banks
  have H:=s.toRelayWindow.relay_header mounted.1
  have keep:=A.metadata_frame m1 s.meta H
  have ctrl : (cur).val=A.control := Fin.val_cast_of_lt s.controlRoom
  have count : (ctr).val=A.control+1 := Fin.val_cast_of_lt s.counterFit
  have tail : memory A ss edges [] bits input n i=m1 i := by
    have met := keep i (.inr (s.recordsToControl.trans (by omega)))
    simpa only [memory,writeMemory,count,ctrl,ite_eq_right (show i≠A.control+1 by omega),
      ite_eq_right (show i≠A.control by omega)] using met
  have gBelow : (C).graph+6*(C).rows≤ i := s.graphBefore.trans (s.toRelayWindow.columns.2.trans (by omega))
  have wBelow : (C).widths+(C).rows*A.remainingLanes≤ i := s.widthsBefore.trans (by omega)
  have past : (C).graph≤A.control := s.toRelayWindow.columns.1.trans s.toRelayWindow.columns.2
  have graph : m1 i=m0 i := by
    dsimp only [m1,InitialRelayBootstrap.image]
    rw [InitialRelayWidth.image_outside _ _ _ _ _ (.inr wBelow)]
    simp [InitialRelayGraph.image,fillSegment,show ¬((C).graph≤ i ∧ i<(C).graph+6*(C).rows) by omega]
  have head := banks.headers.trans past
  have hist := banks.counts.trans past
  have noBook : A.codebookWords=0 := src.book
  have dirEnd : A.seed+64*(ss.length+2)≤A.control := by
    simpa only [Archive.directory_length] using head
  exact tail.trans (graph.trans (by
    simp [m0,Archive.mountedMemory,writeMemory,ctrl,ne_of_gt (by omega : A.control < i),
      fillSegment,noBook,show ¬(A.seed≤ i ∧ i<A.seed+64*(ss.length+2)) by omega,
      show ¬(A.cursor.dense≤ i ∧ i<A.cursor.dense+A.histWords ss) by omega]))


end
end Hierarchy.TraceSeedWriter

end OAI
