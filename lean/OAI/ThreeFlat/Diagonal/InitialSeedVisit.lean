import OAI.ThreeFlat.Diagonal.TraceTerminalEdges
import OAI.ThreeFlat.Diagonal.NavigationTerminalWindow
import OAI.ThreeFlat.Diagonal.NativeTickParameterSpace
import OAI.ThreeFlat.RAM.TraceMountedSeed
import OAI.ThreeFlat.RAM.TickNavigationRaw
import OAI.ThreeFlat.RAM.TickBoundaryFields
import OAI.ThreeFlat.Diagonal.InitialSeedContinuation
import OAI.ThreeFlat.Diagonal.InitialSeedBounds
import OAI.ThreeFlat.Diagonal.NavigationTraversalCore
import OAI.ThreeFlat.RAM.AdmissionPost
import OAI.ThreeFlat.RAM.TickProcedureContracts

namespace OAI
/-! # Opening the traversal on the initialized cursor and reading its persistent public library -/
set_option quotPrecheck false

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM CompressorPacking.Native NavigationDirectory
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {P : PhysicalStage.Block F} {W k low off slots : ℕ} {hk : 2≤k+1}
variable {A : Archive} {ss : List Stage} {edges blocks : ℕ} {raw : ℕ→Bool} {input out : Memory W}
variable {ax : k+1=A.axes} {de : 2^(P.exponent 0)=A.initialDegree}
local notation "X" => P.cursorState hk low off slots

theorem Archive.SeedReady.visit (r : A.SeedReady ss edges P hk low off slots de ax raw blocks input out)
    (lanes : A.remainingLanes=2^(k+1)) (gLow : A.cursor.dense≤A.cursor.graph) (wLow : A.cursor.dense≤A.cursor.width)
    (gHigh : A.cursor.graph+6*(A.axes*A.initialDegree)≤A.cursor.heap)
    (wHigh : A.cursor.width+A.axes*A.initialDegree*A.remainingLanes≤A.cursor.heap) :
    A.Visit ss edges raw (A.control:Word W) [] X out := by
  have card : Fintype.card (X).Base=A.axes := (Fintype.card_fin (k+1)).trans ax
  have cols : RefreshStageNav.oldColumns A.cursor (Fintype.card (X).Base) (2^P.exponent 0)=
      ⟨A.cursor.graph,A.axes*A.initialDegree,A.cursor.width⟩ := by unfold RefreshStageNav.oldColumns;rw [card,de]
  exact ⟨r.live,gLow,wLow,by simpa only [finish,card,de] using gHigh,
    by simpa only [finish,PhysicalStage.State.edgeCount,card,de,←lanes] using wHigh,
    by simpa only [finish,cols] using r.slots⟩

variable (p : Parameters) (d : ℕ)
local notation "u" => p.age
local notation "w" => (16*u^10)
local notation "a" => p.archive d w

theorem Parameters.seed_visit {X0 X1 : Memory w} {degree : 2^(P.exponent 0)=(a).initialDegree}
    {axes : k+1=(a).axes} (r : (a).SeedReady ss edges P hk low off slots degree axes raw blocks X0 X1)
    (space : InitialSpace p d) :
    (a).Visit ss edges raw ((a).control:Word w) [] X X1 ∧ (X1 (((a).control+3:ℕ):Word w).val).val=blocks := by
  have lanes : (a).remainingLanes=2^(k+1) := by change 2^p.axes=_;exact congrArg (2^·) axes.symm
  exact ⟨r.visit lanes (Nat.le_add_right ..) (Nat.le_add_right ..) space.graphBeforeHeap space.widthsBeforeHeap,r.counter⟩

/-- The packed S38 codebook survives the cursor graph, metadata and clock starts. -/
theorem Parameters.started_book (library suffix : List ℕ) (ss : List Stage) (edges : ℕ) (raw : ℕ→Bool)
    (input : Memory w) (blocks : ℕ) (s : (a).SeedSpace w) (banks : (a).MountedRange ss edges w)
    (src : (a).SeedSources ss edges library suffix raw input) (space : InitialSpace p d)
    (bookRoom : p.codebookWords≤TickWorkspace.stride u) (counterRoom : (a).control+3<(a).initialRecords)
    (j : Fin library.length) :
    (a).startedMemory ss edges library raw input blocks ((a).staticCodebook+j.val)=(library[j.val]?.getD 0:Word w) := by
  let C : SlotImage.Columns:=⟨(a).cursor.graph,(a).axes*d,(a).cursor.width⟩
  let m0:=(a).mountedMemory ss edges library raw input
  let m1:=InitialRelayBootstrap.image C (a).axes d (a).remainingLanes (a).relayWidth m0
  let pos:=(a).staticCodebook+j.val
  have ge : (a).cursor.heap≤(a).staticCodebook := (Nat.le_add_right ..).trans (TickWorkspace.apart («u»:=u) (by decide : 22<38))
  have before : pos<(a).control := by
    have h:=TickWorkspace.apart («u»:=u) (by decide : 38<40)
    have book : p.codebookWords=library.length := src.book
    change TickWorkspace.base u 38+j.val<TickWorkspace.base u 40
    have:=j.isLt;omega
  have gHigh : C.graph+6*C.rows≤pos := space.graphBeforeHeap.trans (ge.trans (Nat.le_add_right ..))
  have wHigh : C.widths+C.rows*(a).remainingLanes≤pos := space.widthsBeforeHeap.trans (ge.trans (Nat.le_add_right ..))
  have dirHigh : (a).seed+((a).directory ss edges w).length≤pos := banks.headers.trans ((Nat.le_add_right ..).trans gHigh)
  have histHigh : (a).cursor.dense+(a).histWords ss≤pos := banks.counts.trans ((Nat.le_add_right ..).trans gHigh)
  have inside : pos<(a).staticCodebook+(a).codebookWords := Nat.add_lt_add_left (by rw [src.book];exact j.isLt) _
  have lo : (a).staticCodebook≤pos := Nat.le_add_right ..
  have cur : (((a).control:Word w)).val=(a).control := Fin.val_cast_of_lt s.controlRoom
  have ctr : ((((a).control+3:ℕ):Word w)).val=(a).control+3 :=
    Fin.val_cast_of_lt (counterRoom.trans_le ((Nat.le_add_right ..).trans s.endFit.le))
  have h:=s.relay_header (src.mounted s banks).1
  have metadata:=(a).metadata_frame m1 s.toMetadataSpace h pos (.inl (before.trans s.controlsBefore))
  have book : m0 pos=(library[j.val]?.getD 0:Word w) := by
    change writeMemory _ ((a).control:Word w) _ pos=_
    simp only [writeMemory,cur,ne_of_lt before,ite_false,fillSegment,
      show ¬pos<(a).cursor.dense+(a).histWords ss from not_lt.mpr histHigh,
      show ¬pos<(a).seed+((a).directory ss edges w).length from not_lt.mpr dirHigh,and_false,
      lo,inside,and_self,ite_true,Archive.bookWord,pos,Nat.add_sub_cancel_left]
  have relay : m1 pos=m0 pos := by
    rw [show m1=InitialRelayWidth.image C.widths (C.rows*(a).remainingLanes) (a).relayWidth
      (InitialRelayGraph.image C.graph (a).axes d m0) from rfl,
      InitialRelayWidth.image_outside _ _ _ _ _ (.inr wHigh)]
    simp [InitialRelayGraph.image,fillSegment,show ¬pos<C.graph+6*((a).axes*d) from not_lt.mpr gHigh]
  change writeMemory (writeMemory ((a).metadataMemory m1) ((a).control:Word w) _) ((((a).control+3:ℕ):Word w)) _ pos=_
  simpa only [writeMemory,cur,ctr,ne_of_lt before,show pos≠(a).control+3 by omega,ite_false] using
    metadata.trans (relay.trans book)


end
end ThreeFlat.Diagonal.NavigationPass

namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.TickStageSpec NavigationDirectory
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W : ℕ}

private theorem front {G : Type*} [Semiring G] (field : FieldCode G W) (a b : Procedure W)
    {pre : Memory W→Prop} {next : Memory W} {good : Prop} {post : Memory W→Prop} {ta tb : ℕ}
    (one : a.Spec pre (fun _ o=>o=next) ta)
    (two : Admission field b.block b.publicData (fun m=>m=next) (fun _=>good) (fun _ o=>post o) tb) :
    let proc:=a.seq b
    Admission field proc.block proc.publicData pre (fun _=>good) (fun _ o=>post o) (ta+tb) := by
  have linked : Admission field (a.seq b).block (a.seq b).publicData pre (fun _=>good)
      (fun _ out=>∃ tmp : Memory W, tmp=next ∧ post out) (ta+tb) := by
    apply admission_seq field a b (admission_of_spec field a one) two
    · exact fun _ _ _=>trivial
    · exact fun _ _ _ _ h=>⟨h,Iff.rfl⟩
  change Admission field (a.seq b).block (a.seq b).publicData pre (fun _=>good) (fun _ out=>post out) (ta+tb)
  intro labels regs slots M pc reg pub exit installed table c mem start hp
  obtain ⟨pass,fail⟩:=linked M pc reg pub exit installed table c mem start hp
  constructor
  · intro accepted
    obtain ⟨n,hn,last,out,halted,⟨_,_,result⟩,steps⟩:=pass accepted
    exact ⟨n,hn,last,out,halted,result,steps⟩
  · exact fail

private theorem exactInput {p : Procedure W} {pre : Memory W→Prop} {f : Memory W→Memory W} {n : ℕ}
    (run : p.Spec pre (fun m o=>o=f m) n) {m : Memory W} (h : pre m) :
    p.Spec (fun u=>u=m) (fun _ out=>out=f m) n := by
  intro p r k M pc reg pub exit installed table c u start same
  subst u;exact run M pc reg pub exit installed table c m start h

/-- Deterministic boot and cursor initialization followed by a chronological tail
which can reject malformed histories with zero total weight. -/
theorem boot_seed_admission (field : FieldCode F W) (A : Archive) (ss : List Stage) (edges blocks : ℕ)
    (library suffix : List ℕ) (raw : ℕ→Bool) (input : Memory W)
    (s : A.SeedSpace W) (banks : A.MountedRange ss edges W) (src : A.SeedSources ss edges library suffix raw input)
    (degree : 0<A.initialDegree) (axes : A.axes≤W) (wide : 8<2^W)
    (tail : Procedure W) (ok : Prop) (post : Memory W→Prop) (time : ℕ)
    (body : Admission field tail.block tail.publicData (fun m=>m=A.startedMemory ss edges library raw input blocks)
      (fun _=>ok) (fun _ out=>post out) time) :
    let proc:=A.seedThen ss edges blocks tail
    Admission field proc.block proc.publicData (fun m=>m=input) (fun _=>ok) (fun _ out=>post out)
      (A.bootTime ss edges W+A.seedTime+6+time) := by
  let cur:=(A.control:Word W)
  let ctr:=((A.control+3:ℕ):Word W)
  let C : SlotImage.Columns:=⟨A.cursor.graph,A.axes*A.initialDegree,A.cursor.width⟩
  let m0:=A.mountedMemory ss edges library raw input
  let m1:=InitialRelayBootstrap.image C A.axes A.initialDegree A.remainingLanes A.relayWidth m0
  let m2:=A.metadataMemory m1
  let m3:=writeMemory m2 cur (A.cursor.header:Word W)
  let m4:=A.startedMemory ss edges library raw input blocks
  let bootRelay := InitialRelayBootstrap.procedure cur C A.axes A.initialDegree A.relayWidth
  have a : (A.boot ss edges).Spec (·=input) (fun _ out=>out=m0) (A.bootTime ss edges W) :=
    src.boot (s:=s) banks
  have mounted:=src.mounted s banks
  have graphTop : C.graph+6*(A.axes*A.initialDegree)<2^W :=
    (s.graphBefore.trans ((Nat.le_add_right ..).trans s.widthsBefore)).trans_lt s.controlRoom
  have b : bootRelay.Spec (·=m0) (fun _ out=>out=m1)
      (InitialRelayBootstrap.budget W C A.axes A.initialDegree A.remainingLanes) := by
    intro programCount registerCount wordCount machine
    exact exactInput (m:=m0) (InitialRelayBootstrap.spec cur C A.axes A.initialDegree A.remainingLanes A.relayWidth
      graphTop (s.widthsBefore.trans_lt s.controlRoom) degree axes (by omega))
      (s.loaded mounted.1) machine
  have c : (A.initialMetadata : Procedure W).Spec (fun z=>z=m1) (fun _ out=>out=m2)
      (33+A.metadataUnit*A.initialSites) := by
    intro programCount registerCount wordCount machine
    exact Procedure.Spec.mono (A:=A.initialMetadata)
      (A.metadata_spec m1 s.toMetadataSpace (s.relay_header mounted.1))
      (fun _ h=>h) (fun _ _ h=>h.1) le_rfl machine
  have f : (start cur (A.cursor.header:Word W)).Spec (·=m2) (fun _ out=>out=m3) 3 := by
    intro programCount registerCount wordCount machine
    exact exactInput (m:=m2) (start_spec cur (A.cursor.header:Word W)) trivial machine
  have g : (start ctr (blocks:Word W)).Spec (·=m3) (fun _ out=>out=m4) 3 := by
    intro programCount registerCount wordCount machine
    exact exactInput (m:=m3) (start_spec ctr (blocks:Word W)) trivial machine
  let counter := start ctr (blocks : Word W)
  let pointer := start cur (A.cursor.header : Word W)
  let starts := pointer.seq (counter.seq tail)
  let afterRelay := (A.initialMetadata : Procedure W).seq starts
  have cost : A.bootTime ss edges W +
      (InitialRelayBootstrap.budget W C A.axes A.initialDegree A.remainingLanes +
        ((33+A.metadataUnit*A.initialSites)+(3+(3+time)))) = A.bootTime ss edges W+A.seedTime+6+time := by
    rw [InitialRelayBootstrap.budget_eq,A.metadataUnit_eq,seedTime]
    omega
  dsimp only
  rw [←cost]
  intro pc regs slots machine
  exact front field (A.boot ss edges) (bootRelay.seq afterRelay) a
    (front field bootRelay afterRelay b
      (front field A.initialMetadata starts c
        (front field pointer (counter.seq tail) f
          (front field counter tail g body)))) machine


end
end ThreeFlat.Diagonal.NavigationPass.Archive


namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.TickStageSpec PhysicalStage NavigationDirectory
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W : ℕ}

theorem decode_requires_prefix {S : HistoryContraction.Shape} (P : HistoryContraction.Plan F S) (E : P.Codes)
    (amount : P.History→ℕ) (cap : ℕ) (xs : List Bool) :
    (P.decodeShared E amount cap xs).isSome → (P.read E xs).isSome := by
  cases h : P.read E xs with
  | none => simp [HistoryContraction.Plan.decodeShared,h]
  | some v => simp

variable {u s : ℕ} (A : Archive) (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem))
local notation "w" => (16*u^10)
local notation "ss" => P.directory rem (Fintype.card X.Base)
local notation "edges" => P.finalEdges rem (Fintype.card X.Base)
local notation "c" => finish A.K ss A.cursor
local notation "x" => A.terminal ss edges w
local notation "cur" => (A.control:Word w)
local notation "R" => P.run rem X
local notation "amount" => (R).readTerminal (fun X=>X.widthSum)
variable (bits : ℕ→Bool)
local notation "raw" => List.ofFn (fun j : Fin A.pairCapacity=>bits j.val)
local notation "H" => w*A.histWords ss
local notation "tail" => (raw).drop H

theorem close_visit (field : FieldCode F w) (E : (R).Records) (m input : Memory w)
    (v : Run.WireLayer) (parsed : (R).EndsAt E raw v tail) (visit : A.Visit ss edges bits cur ss v.state m)
    (limits : A.Limits u cur ss edges A.pairCapacity) (room : A.TerminalRoom ss edges w)
    (window : A.RawWindow ss bits input) (small : 1<2^w) (low : ∀i,i<A.seed→m i=input i) :
    let Q:=TerminalWireArchive.program (W:=w) x
    Admission field Q.block Q.publicData (fun i=>i=m)
      (fun _=>((R).plan.decodeShared ((R).codes E) amount A.pairCapacity raw).isSome)
      (fun _ out=>out=TerminalWireArchive.image x m) (terminalTime x) := by
  obtain ⟨h,read,target⟩:=parsed
  have bound:=limits.capacity
  have grade : edges=v.state.edgeCount := by rw [←target];exact (P.finalEdges_eq rem X h).symm
  have card : v.state.widthSum=amount h := by rw [←target];exact (R).terminalLayer_width h
  have control:=limits.controls
  have rawLow:=limits.raw
  have headerFit : A.seed+(A.directory ss edges w).length<2^w :=
    (limits.tables.trans ((Nat.le_add_right ..).trans (rawLow.trans ((Nat.le_add_right ..).trans control)))).trans_lt (cur).isLt
  have phase:=window.phase.trans_le room.seed
  have old : (x).oldSource+(x).capacity≤(x).prefixBase := by
    change A.oldHistory+H+(A.pairCapacity-H)≤(c).heap
    exact (by have:=window.old;have:=room.seed;omega)
  have fresh : (x).newSource+(x).capacity≤(x).prefixBase := by
    change A.newHistory+H+(A.pairCapacity-H)≤(c).heap
    have:=window.fresh;have:=room.seed;omega
  have widthTop : (x).widthBase+(x).edges≤(x).prefixBase := by
    change (c).width+edges≤(c).heap
    rw [grade];exact visit.widthBound
  intro body machineSize registerCount publicCount machine
  exact A.terminal_admission ss edges (R).plan ((R).codes E) amount raw tail h read (by simp) field m bits
    v.state _ visit.live limits.origin headerFit room.bounds room.header room.control widthTop phase old fresh
    (window.terminal edges small low) (by simp [Archive.terminal]) rfl grade card visit.stored machine


end
end ThreeFlat.Diagonal.NavigationPass.Archive

namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.TickStageSpec PhysicalStage NavigationDirectory
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {u : ℕ} (A : Archive) (B : Block F) (n rem : ℕ)
local notation "W" => (16*u^10)
local notation "cur" => (A.control:Word W)
local notation "ctr" => ((A.control+3:ℕ):Word W)
local notation "P" => B.repeat n
variable (X : State (2^(B.exponent 0)) ((B.repeat n).charge+rem))
local notation "v" => Fintype.card X.Base
local notation "R" => (P).run rem X
local notation "ss" => (P).directory rem v
local notation "edges" => (P).finalEdges rem v
local notation "x" => A.terminal ss edges W
variable (bits : ℕ→Bool)
local notation "raw" => List.ofFn (fun j : Fin A.pairCapacity=>bits j.val)
local notation "tail" => (raw).drop (W*A.histWords ss)
local notation "amount" => (R).readTerminal (fun X=>X.widthSum)
local notation "body" => (repeated cur ctr A.K B).seq (TerminalWireArchive.program («W»:=W) x)

def loopTime :=
  let cost:=Program.nativeTicks A.K cur P A.cursor rem v
  let rows:=(B.prefix (.done _)).length
  n*(7+(rows*(rows*cost)+1))+4

/-- The entire successful native history, prior to the terminal output span, is
retained. The final image gives the terminal edge-prefix addresses and frames all
words outside that span. -/
def Closed (E : (R).Records) (origin out : Memory W) : Prop :=
  ∃ mid : Memory W,A.Journal u cur ctr P rem X A.cursor raw origin mid ∧
    (∃ layer : Run.WireLayer,(R).EndsAt E raw layer tail ∧ A.Visit ss edges bits cur ss layer.state mid) ∧
    out=TerminalWireArchive.image x mid

theorem closed_frame (E : (R).Records) {origin out : Memory W} (h : A.Closed B n rem X bits E origin out) :
    ∃ mid : Memory W,A.Journal u cur ctr P rem X A.cursor raw origin mid ∧
      (∃ layer : Run.WireLayer,(R).EndsAt E raw layer tail ∧ A.Visit ss edges bits cur ss layer.state mid) ∧
      ∀ i,(i<(x).prefixBase ∨ (x).prefixBase+(x).edges+1≤ i)→ out i=mid i := by
  obtain ⟨mid,log,atEnd,image⟩:=h
  refine ⟨mid,log,atEnd,?_⟩
  intro i hi
  rw [image]
  unfold TerminalWireArchive.image fillSegment
  split
  · omega
  · rfl

theorem run_initialized (field : FieldCode F W) (Z : ℕ)
    (fit : ∀ b∈(P).recordBounds,b.1≤A.K ∧ b.2*Z<2^W)
    (reach : (R).WidthCeiling Z) (small : Z≤(2^(u^10))^4) (fixed : ∀ b∈wordConstants P,b≤u)
    (age : 40≤u) (alphabet : A.K≤u) (limits : A.Limits u cur ss edges A.pairCapacity)
    (room : A.TerminalRoom ss edges W) (s : A.SeedSpace W) (counterFit : A.control+3<2^W)
    (origin input : Memory W) (window : A.RawWindow ss bits input)
    (valid : A.Visit ss edges bits cur [] X origin) (count : (origin (ctr).val).val=n)
    (low : ∀i,i<A.seed→ origin i=input i) :
    let q:=(P).table A.K W Z fit rem X reach
    Admission field (body).block (body).publicData (fun m=>m=origin)
      (fun _=>((R).plan.decodeShared q.codes amount A.pairCapacity raw).isSome)
      (fun _ out=>A.Closed B n rem X bits q.records origin out) (A.loopTime («u»:=u) B n rem X+terminalTime x) := by
  intro q
  let rows:=repeated cur ctr A.K B
  let finishProc:=TerminalWireArchive.program («W»:=W) x
  have a0 : (cur).val=A.control:=Fin.val_cast_of_lt s.controlRoom
  have a3 : (ctr).val=A.control+3:=Fin.val_cast_of_lt counterFit
  let arrived (m : Memory W) := A.Journal u cur ctr P rem X A.cursor raw origin m ∧
    ∃ layer : Run.WireLayer,(R).EndsAt q.records raw layer tail ∧ A.Visit ss edges bits cur ss layer.state m
  let parsed := ((R).plan.read q.codes raw).isSome
  let yes:= ((R).plan.decodeShared q.codes amount A.pairCapacity raw).isSome
  have left : Admission field rows.block rows.publicData (fun m=>m=origin)
      (fun _=>parsed) (fun _ out=>arrived out) (A.loopTime («u»:=u) B n rem X) := by
    intro np nr nk machine
    refine TickStageSpec.Admission.mono
      (fun {labels registers slots} m =>
        A.run_repeated B n rem X field cur ctr edges A.pairCapacity Z bits origin age alphabet
          (by rw [a0,a3]; omega) fit reach small fixed limits m)
      ?_ (fun _ _=>Iff.rfl) (fun _ _ _ _ h=>h) le_rfl machine
    rintro _ rfl
    exact ⟨rfl,valid,count⟩
  have right : Admission field finishProc.block finishProc.publicData arrived (fun _=>yes)
      (fun m o=>o=TerminalWireArchive.image x m) (terminalTime x) := by
    intro p r k M pc reg pub stop inst words config m atPC h
    obtain ⟨log,layer,read,store⟩:=h
    have denseLow : A.seed≤A.cursor.heap :=
      (Nat.le_add_right ..).trans (limits.tables.trans ((Nat.le_add_right ..).trans limits.raw))
    have before : A.seed≤(cur).val := denseLow.trans ((Nat.le_add_right ..).trans limits.controls)
    have rawSame (i : ℕ) (hi : i<A.seed) : m i=input i := by
      apply (Journal.frame P rem X A.cursor raw log (hi.trans_le before).ne (by rw [a3];rw [a0] at before;omega) _).trans (low i hi)
      exact ⟨.inl (by rw [limits.origin];omega),.inl (hi.trans_le denseLow)⟩
    have positiveAge : u ≠ 0 := by omega
    have wide : 1<2^W := Nat.one_lt_two_pow (Nat.mul_ne_zero (by decide) (pow_ne_zero 10 positiveAge))
    exact (A.close_visit P rem X bits field q.records m input layer read store limits room window wide rawSame)
      M pc reg pub stop inst words config m atPC rfl
  intro np nr nk machine
  refine TickStageSpec.Admission.mono
    (fun {labels registers slots} m =>
      admission_seq field rows finishProc (pre:=fun m=>m=origin) (good:=fun _=>yes)
        (fun {a b c} m => left m) (fun {a b c} m => right m)
        (fun _ _ h=>decode_requires_prefix _ _ _ _ _ h)
        (fun _ _ _ _ arr=>⟨arr,Iff.rfl⟩) m)
    (fun _ e=>e) (fun _ _=>Iff.rfl) ?_ le_rfl machine
  rintro _ _ _ _ ⟨m,⟨log,endGraph⟩,image⟩
  exact ⟨m,log,endGraph,image⟩


end
end ThreeFlat.Diagonal.NavigationPass.Archive

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.TickStageSpec PhysicalStage NavigationDirectory
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] (p : Parameters) (B : Block F) (n rem d : ℕ)
local notation "u" => p.age
local notation "W" => (16*u^10)
local notation "A" => p.archive d W
local notation "cur" => ((A).control : Word W)
local notation "P" => B.repeat n
variable {k : ℕ} (hk : 2≤k+1) (low offsets slots : ℕ)
variable (castLanes : k+1=(B.repeat n).charge+rem)
local notation "seed" => B.cursorState hk low offsets slots
local notation "X" => (castLanes ▸ B.cursorState hk low offsets slots : State (2^(B.exponent 0)) ((B.repeat n).charge+rem))
local notation "R" => (P).run rem X
local notation "steps" => (P).directory rem (Fintype.card (X).Base)
local notation "edges" => (P).finalEdges rem (Fintype.card (X).Base)
local notation "terminal" => (A).terminal steps edges W
variable (bits : ℕ→Bool)
local notation "raw" => List.ofFn (fun j : Fin (A).pairCapacity=>bits j.val)

include hk low offsets slots castLanes in
/-- The literal navigation program runs from the physical parameter bits up to
and including terminal padding rejection, for the actual initial cursor. -/
theorem Parameters.active_admission (field : FieldCode F W) (Z : ℕ)
    (fit : ∀ b∈(P).recordBounds,b.1≤(A).K ∧ b.2*Z<2^W) (reach : (R).WidthCeiling Z)
    (small : Z≤(2^(u^10))^4) (fixed : ∀ b∈wordConstants P,b≤u)
    (age : 40≤u) (alphabet : (A).K≤u) (depth : p.axes≤u^10+2*u^6) (degBound : d≤u)
    (degree : 2^(B.exponent 0)=d) (axes : k+1=p.axes) (wire : (A).relayWidth=2^low*(offsets*slots*3))
    (maximum : (A).relayWidth<2^W) (axisBits : k+1≤W) (blocks : n<2^W)
    (library suffix : List ℕ) (input : Memory W)
    (sources : (A).SeedSources steps edges library suffix bits input)
    (banks : (A).MountedRange steps edges W) (limits : (A).Limits u cur steps edges (A).pairCapacity)
    (room : (A).TerminalRoom steps edges W) (window : (A).RawWindow steps bits input) :
    let chart:=(P).table (A).K W Z fit rem X reach
    let origin:=(A).startedMemory steps edges library bits input n
    let machine:=NavigationPass.active («W»:=W) A B n rem edges
    Admission field machine.block machine.publicData (fun m=>m=input)
      (fun _=>((R).plan.decodeShared chart.codes ((R).readTerminal (fun z=>z.widthSum)) (A).pairCapacity raw).isSome)
      (fun _ out=>(A).Closed B n rem X bits chart.records origin out)
      ((A).bootTime steps edges W+(A).seedTime+6+((A).loopTime («u»:=u) B n rem X+Archive.terminalTime terminal)) := by
  intro chart origin machine
  let space:=p.initial_space d age degBound depth
  let seedSpace:=p.seed_space d age degBound depth
  have lanes : (A).remainingLanes=2^(k+1) := by change 2^p.axes=_;rw [axes]
  have ctr : (A).control+3<(A).initialRecords := by
    have gap:=TickWorkspace.apart («u»:=u) (by decide : 40<49)
    have large : 4≤TickWorkspace.stride u := by
      have hu : 1≤u^10 := Nat.one_le_pow _ _ (by omega)
      change 4≤(2^(u^10))^4
      exact le_trans (by decide : 4≤(2^1)^4) (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hu) _)
    change TickWorkspace.base u 40+3<TickWorkspace.base u 49;omega
  have s:=(A).started_ready steps edges B hk low offsets slots degree axes lanes wire library suffix bits input n
    seedSpace banks sources maximum axisBits space.degreeWord (by rw [axes]; exact space.laneWord)
    space.eight limits.origin ctr blocks
  obtain ⟨first,count⟩:=p.seed_visit d s space
  have v : (A).Visit steps edges bits cur [] X origin := first.cast castLanes
  have cf : (A).control+3<2^W := ctr.trans_le ((Nat.le_add_right ..).trans seedSpace.endFit.le)
  have card : Fintype.card (X).Base=(A).axes :=
    (Program.baseCast castLanes seed).trans ((Fintype.card_fin (k+1)).trans axes)
  change Admission field (NavigationPass.active («W»:=W) A B n rem edges).block (NavigationPass.active («W»:=W) A B n rem edges).publicData _ _ _ _
  have text : NavigationPass.active («W»:=W) A B n rem edges =
      (A).seedThen steps edges n ((repeated cur (((A).control+3:ℕ):Word W) (A).K B).seq (TerminalWireArchive.program terminal)) := by
    unfold NavigationPass.active Archive.seedThen
    rw [card]
  rw [text]
  intro labels registers slots machine
  exact Archive.boot_seed_admission field A steps edges n library suffix bits input seedSpace banks sources
    (degree ▸ Nat.two_pow_pos _) (show (A).axes ≤ W by change p.axes ≤ W; exact axes.ge.trans axisBits) space.eight _ _ _ _
    (fun {labels registers slots} m => (A).run_initialized B n rem X bits field Z fit reach small fixed
      age alphabet limits room seedSpace cf origin input window v count s.low m) machine


end
end ThreeFlat.Diagonal.NavigationPass

namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage NavigationDirectory HistoryContraction
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {u : ℕ} {A : Archive} {B : Block F} {n rem : ℕ}
local notation "W" => (16*u^10)
local notation "P" => B.repeat n
variable {X : State (2^(B.exponent 0)) ((B.repeat n).charge+rem)} {bits : ℕ→Bool}
local notation "R" => (P).run rem X
local notation "ss" => (P).directory rem (Fintype.card X.Base)
local notation "edges" => (P).finalEdges rem (Fintype.card X.Base)
local notation "x" => A.terminal ss edges W
local notation "raw" => List.ofFn (fun j : Fin A.pairCapacity=>bits j.val)
local notation "tail" => (raw).drop (W*A.histWords ss)
local notation "amount" => (R).readTerminal (fun X=>X.widthSum)

/-- The final prefix file addresses each actual edge bit of the decoded history.
The terminal suffix begins with exactly those decoded bits, in that same order. -/
theorem Closed.terminal_bits {E : (R).Records} {origin out : Memory W}
    (closed : A.Closed B n rem X bits E origin out) (room : A.TerminalRoom ss edges W)
    (passed : ((R).plan.decodeShared ((R).codes E) amount A.pairCapacity raw).isSome) :
    ∃ (h : (R).plan.History) (wire : Fin (amount h)→Bool),
      (R).plan.decodeShared ((R).codes E) amount A.pairCapacity raw=some ⟨h,wire⟩ ∧
      (R).plan.read ((R).codes E) raw=some (h,tail) ∧
      (tail).take (amount h)=List.ofFn wire ∧
      ∀ (i : Fin ((R).terminalLayer h).state.edgeCount) (j : Fin (((R).terminalLayer h).state.wireWidth i)),
        (out ((x).prefixBase+i.val)).val+j.val=(((R).terminalLayer h).state.bitAddress i j).val := by
  obtain ⟨mid,_,⟨layer,⟨h,read,target⟩,visit⟩,image⟩:=closed
  obtain ⟨z,ok⟩ : ∃ z,(R).plan.decodeShared ((R).codes E) amount A.pairCapacity raw=some z := by
    cases res : (R).plan.decodeShared ((R).codes E) amount A.pairCapacity raw with
    | none => simp [res] at passed
    | some t => exact ⟨t,rfl⟩
  obtain ⟨picked,wire⟩:=z
  let pad:=List.replicate (A.pairCapacity-((R).plan.write ((R).codes E) picked).length-amount picked) false
  have same : some (h,tail)=some (picked,List.ofFn wire++pad) := calc
    some (h,tail) = (R).plan.read ((R).codes E) raw := read.symm
    _ = (R).plan.read ((R).codes E) ((R).plan.encodeShared ((R).codes E) amount A.pairCapacity ⟨picked,wire⟩) :=
      congrArg ((R).plan.read ((R).codes E)) ((R).plan.encode_decode ((R).codes E) amount A.pairCapacity raw _ ok).symm
    _ = _ := (R).plan.read_write ((R).codes E) picked _
  have hist : h=picked := congrArg Prod.fst (Option.some.inj same)
  subst picked
  have suffix : tail=List.ofFn wire++pad := congrArg Prod.snd (Option.some.inj same)
  have cap := (((R).plan.decodeShared_suffix ((R).codes E) amount A.pairCapacity raw h tail read
    (by simp)).mp passed).1
  subst layer
  refine ⟨h,wire,ok,read,?_,?_⟩
  · rw [suffix]
    exact List.take_left' (List.length_ofFn (f:=wire))
  · intro i j
    rw [image]
    apply terminal_bit_address ((R).terminalLayer h).state _ x mid room.bounds rfl
      ((P).finalEdges_eq rem X h).symm _ visit.stored i j
    rw [(R).terminalLayer_width h]
    simpa only [Archive.terminal,List.length_drop,List.length_ofFn] using cap

/-- The actual decoded terminal history indexes the retained live edge prefixes. -/
theorem Closed.prefix_at {E : (R).Records} {origin out : Memory W}
    (closed : A.Closed B n rem X bits E origin out) (room : A.TerminalRoom ss edges W)
    (v : (R).plan.Terminal amount)
    (dec : (R).plan.decodeShared ((R).codes E) amount A.pairCapacity raw=some v) :
    ∀ (i : Fin ((R).terminalLayer v.1).state.edgeCount) (j : Fin (((R).terminalLayer v.1).state.wireWidth i)),
      (out ((x).prefixBase+i.val)).val+j.val=(((R).terminalLayer v.1).state.bitAddress i j).val := by
  obtain ⟨h,wire,decoded,_,_,address⟩:=closed.terminal_bits room (by simp [dec])
  have eq : h=v.1 := congrArg Sigma.fst (Option.some.inj (decoded.symm.trans dec))
  subst h
  exact address


end
end ThreeFlat.Diagonal.NavigationPass.Archive


namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage NavigationDirectory
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

variable (p : Parameters) (B : Block F) (n rem : ℕ)
local notation "u" => p.age
local notation "W" => (16*u^10)
local notation "d" => 2^(B.exponent 0)
local notation "A" => p.archive d W
local notation "P" => B.repeat n
local notation "ss" => (P).directory rem p.axes
local notation "edges" => (P).finalEdges rem p.axes
local notation "cur" => ((A).control:Word W)
local notation "c" => finish (A).K ss (A).cursor

/-- The terminal prefix stops before S38. This protects the persistent
codebook, the clock in S40, and the original node metadata in S49. -/
theorem Parameters.terminal_space (age : 40≤u) (degree : d≤u)
    (depth : p.axes≤u^10+2*u^6) (axes : (P).charge+rem=p.axes)
    (lim : (A).Limits u cur ss edges (A).pairCapacity)
    (old : (A).oldHistory+(A).pairCapacity≤(A).seed) (fresh : (A).newHistory+(A).pairCapacity≤(A).seed) :
    (A).TerminalRoom ss edges W ∧ (c).heap+edges+1≤(A).staticCodebook := by
  let sp:=p.initial_space d age degree depth
  let stride:=TickWorkspace.stride u
  have positive : 1≤ stride := Nat.one_le_pow _ _ (Nat.two_pow_pos _)
  have degreeR:=B.terminalExponent_repeat n
  have edgesFit : edges≤p.axes*d*2^p.axes := by
    calc _ ≤ 2^(P).terminalExponent*(p.axes*2^((P).charge+rem)) := (P).finalEdges_le rem p.axes
         _ = _ := by rw [degreeR,axes];ring
  have next : TickWorkspace.base u 22=TickWorkspace.base u 21+stride := by
    change (22+1)*stride=(21+1)*stride+stride;ring
  have width:=sp.widthsBeforeHeap
  change TickWorkspace.base u 21+stride/2+p.axes*d*2^p.axes≤TickWorkspace.base u 22 at width
  rw [next] at width
  have edgeLe : edges≤ stride := by omega
  have volume:=lim.volume
  have vLe : 2^(u^10)≤ stride := Nat.le_self_pow (by decide) _
  have hf:=heap_finish (A).K ss (A).cursor
  change (c).heap=TickWorkspace.base u 22+((ss).map Stage.heapWords).sum at hf
  have b1:=TickWorkspace.apart («u»:=u) (by decide : 22<23)
  have b2:=TickWorkspace.apart («u»:=u) (by decide : 23<24)
  have b3:=TickWorkspace.apart («u»:=u) (by decide : 24<38)
  have cover : (c).heap+edges+1≤(A).staticCodebook := by change _≤TickWorkspace.base u 38;dsimp only [stride] at *;omega
  have high : (A).staticCodebook≤(A).control :=
    (Nat.le_add_right ..).trans (TickWorkspace.apart («u»:=u) (by decide : 38<40))
  have cf:=sp.records.controlRoom
  have front:=header_finish (A).K ss (A).cursor
  have table:=lim.tables
  rw [Archive.directory_length] at table
  have head : (c).header<(A).cursor.dense := by rw [front,lim.origin];omega
  have de : (A).cursor.dense≤(c).heap :=
    (Nat.le_add_right ..).trans (lim.raw.trans (by rw [heap_finish];exact Nat.le_add_right ..))
  have seedLow : (A).seed≤(c).heap := (Nat.le_add_right ..).trans (table.trans de)
  have wide : (c).width≤(c).heap := width_before_heap (A).K ss (A).cursor ((Nat.le_add_right ..).trans sp.widthsBeforeHeap)
  have safe : (c).heap+edges+1<2^W := (cover.trans high).trans_lt cf
  have seedRoom : (A).seed+1<2^W := by omega
  have p0:=TickWorkspace.apart («u»:=u) (by decide : 0<20)
  have four : 4≤ stride := by
    have one : 1≤u^10 := Nat.one_le_pow _ _ (by omega)
    exact (by decide : 4≤(2^1)^4).trans (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) one) _)
  have phase : (A).phase<(A).seed := by change TickWorkspace.base u 0+2<TickWorkspace.base u 20;dsimp only [stride] at four;omega
  have prefixFits : W*(A).histWords ss≤(A).pairCapacity := lim.capacity
  refine ⟨⟨⟨?_,cf,?_,?_,?_,?_,?_⟩,head.trans_le de,by omega,seedLow⟩,cover⟩
  · exact phase.trans (by omega)
  · change (A).pairCapacity-W*(A).histWords ss+1<2^W;omega
  · change (c).heap+(edges+1)<2^W;omega
  · change (c).width+edges<2^W;omega
  · change (A).oldHistory+W*(A).histWords ss+((A).pairCapacity-W*(A).histWords ss)<2^W;omega
  · change (A).newHistory+W*(A).histWords ss+((A).pairCapacity-W*(A).histWords ss)<2^W;omega


end
end ThreeFlat.Diagonal.NavigationPass

namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage NavigationDirectory
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {u n rem : ℕ} {A : Archive} {B : Block F}
local notation "W" => (16*u^10)
local notation "cur" => (A.control:Word W)
local notation "ctr" => ((A.control+3:ℕ):Word W)
local notation "P" => B.repeat n
variable {X : State (2^(B.exponent 0)) ((B.repeat n).charge+rem)}
local notation "ss" => (P).directory rem (Fintype.card X.Base)
local notation "edges" => (P).finalEdges rem (Fintype.card X.Base)
local notation "x" => A.terminal ss edges W
local notation "c" => finish A.K ss A.cursor
local notation "R" => (P).run rem X

/-- The initialized chronology and terminal prefix scan preserve every input below the seed
header, including the original pin banks and S0 and S1. -/
theorem Closed.before_seed {E : (R).Records} {bits : ℕ→Bool} {input out : Memory W}
    (library suffix : List ℕ)
    (closed : A.Closed B n rem X bits E (A.startedMemory ss edges library bits input n) out)
    (space : A.SeedSpace W) (banks : A.MountedRange ss edges W)
    (src : A.SeedSources ss edges library suffix bits input)
    (limits : A.Limits u cur ss edges A.pairCapacity)
    (counterFit : A.control+3<2^W) (i : ℕ) (hi : i<A.seed) : out i=input i := by
  let m0:=A.mountedMemory ss edges library bits input
  let C : SlotImage.Columns:=⟨A.cursor.graph,A.axes*A.initialDegree,A.cursor.width⟩
  let m1:=InitialRelayBootstrap.image C A.axes A.initialDegree A.remainingLanes A.relayWidth m0
  have hgraph : i<C.graph := by have:=space.seedBefore;change i<A.cursor.graph;omega
  have hcur : i<A.control := by
    change i<A.cursor.graph at hgraph
    have:=space.graphBefore;have:=space.widthsBefore;omega
  have ct := Fin.val_cast_of_lt space.controlRoom
  have count := Fin.val_cast_of_lt counterFit
  have ch : i<A.cursor.header := by rw [limits.origin];omega
  have heap : i<A.cursor.heap := by
    have := limits.raw
    have := src.separated
    omega
  have upper : i<(c).heap := by rw [heap_finish];omega
  obtain ⟨mid,log,_,outside⟩:=closed_frame A B n rem X bits E closed
  have back := Journal.frame P rem X A.cursor _ log (by simpa only [ct] using hcur.ne : i≠(cur).val)
    (by rw [count];omega : i≠(ctr).val) ⟨.inl ch,.inl heap⟩
  have H:=space.relay_header (src.mounted space banks).1
  have low:=A.metadata_frame m1 space.toMetadataSpace H i (.inl (hcur.trans space.controlsBefore))
  have relay:=space.relay_frame m0 i (.inl hgraph)
  have boot:=src.before space i hi
  calc out i=mid i := outside i (.inl upper)
       _ = A.startedMemory ss edges library bits input n i := back
       _ = A.metadataMemory m1 i := by
         change writeMemory (writeMemory _ cur _) ctr _ i=_
         simp only [writeMemory,ct,count,hcur.ne,show i≠A.control+3 by omega,ite_false]; rfl
       _ = _ := low.trans (relay.trans boot)

/-- Static codewords packed at startup are still at S38 when the terminal guard returns. -/
theorem Closed.library {E : (R).Records} {bits : ℕ→Bool} {origin out : Memory W}
    (closed : A.Closed B n rem X bits E origin out) (room : A.TerminalRoom ss edges W)
    (cover : (c).heap+edges+1≤A.staticCodebook) (ctrHigh : (cur).val<(ctr).val)
    (library : List ℕ) (fit : A.staticCodebook+library.length≤(cur).val)
    (packed : ∀j : Fin library.length,origin (A.staticCodebook+j.val)=(library[j.val]?.getD 0:Word W)) :
    ∀j : Fin library.length,out (A.staticCodebook+j.val)=(library[j.val]?.getD 0:Word W) := by
  obtain ⟨mid,log,_,outside⟩:=closed_frame A B n rem X bits E closed
  intro j
  let a:=A.staticCodebook+j.val
  have below : a<(cur).val := (Nat.add_lt_add_left j.isLt _).trans_le fit
  have high : (x).prefixBase+(x).edges+1≤a := cover.trans (Nat.le_add_right ..)
  have past : (c).heap≤a := by change (c).heap+edges+1≤a at high;omega
  exact (outside a (.inr high)).trans ((Journal.frame P rem X A.cursor _ log below.ne (below.trans ctrHigh).ne
    ⟨.inr (room.header.le.trans past),.inr past⟩).trans (packed j))


end
end ThreeFlat.Diagonal.NavigationPass.Archive

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.TickStageSpec PhysicalStage NavigationDirectory
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F)
omit [Fintype F] in
private theorem active_seed_directory (a : Archive) (width blocks residual edges : ℕ)
    (ss : List Stage) (directory : (B.repeat blocks).directory residual a.axes=ss) :
    NavigationPass.active («W»:=width) a B blocks residual edges =
      a.seedThen ss edges blocks
        ((repeated (a.control : Word width) ((a.control+3 : ℕ) : Word width) a.K B).seq
          (TerminalWireArchive.program (a.terminal ss edges width))) := by
  subst ss
  rfl

omit [Fintype F] in
private theorem cursor_cast {i j low off cells : ℕ} (e : i=j) (hi : 2≤ i) (hj : 2≤j) :
    (e ▸ B.cursorState hi low off cells : State (2^B.exponent 0) j)=B.cursorState hj low off cells := by cases e;rfl

omit [Fintype F] in
private theorem seed_axes_cast {i j low off cells ww : ℕ} (a : Archive)
    (e : i=j) (hi : 2≤ i) (hj : 2≤j) (ax : i=a.axes) (ax' : j=a.axes)
    (de : 2^B.exponent 0=a.initialDegree) (m : Memory ww)
    («meta» : a.InitialNodeMetadata (B := Fin i) (t := i)
      (Archive.reseedDegree de (B.cursorState hi low off cells).graph) (finCongr ax) (fun _=>a.relayWidth) m) :
    a.InitialNodeMetadata (B := Fin j) (t := j)
      (Archive.reseedDegree de (B.cursorState hj low off cells).graph) (finCongr ax') (fun _=>a.relayWidth) m := by
  cases e
  exact «meta»

variable {u rem low stride cells tableOffset tariff e : ℕ} (shape : PhysicalPinsExpr.Shape)
local notation "p" => Parameters.cursor B u rem low stride cells shape tableOffset tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "d" => 2^B.exponent 0
local notation "P" => B.repeat n
local notation "k" => (P).charge+rem
local notation "off" => 1+((k+low)+(k+low))
local notation "A" => (p).archive d W
local notation "cur" => ((A).control:Word W)
variable (hk : 2 ≤ (B.repeat (u^8)).charge+rem)
local notation "X" => B.cursorState hk low off cells
local notation "R" => (P).run rem X
local notation "v" => Fintype.card (X).Base
local notation "steps" => (P).directory rem v
local notation "edges" => (P).finalEdges rem v

private theorem cursor_ready (hu : e+40≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (degree : d≤u) (slot : off*cells*3≤u^e)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (bits : ℕ→Bool) (library suffix : List ℕ) (input : Memory W)
    (sources : (A).SeedSources steps edges library suffix bits input) :
    let j:=k-1
    let hj : 2≤j+1 := by dsimp only [j];omega
    let e0 : j+1=(A).axes := by change k-1+1=k;omega
    (A).SeedReady steps edges B hj low off cells rfl e0 bits n input ((A).startedMemory steps edges library bits input n) := by
  intro j hj e0
  have hu0 : 0<u := by omega
  have ageBound : 40 ≤ u := (Nat.le_add_left 40 e).trans hu
  have axesBound : k ≤ u^10+2*u^6 := (Nat.le_add_right k low).trans depth
  have card : v=(p).axes := Fintype.card_fin k
  have banks : (A).MountedRange steps edges W := by
    rw [show steps=(P).directory rem (p).axes by rw [card]]
    exact (p).block_seed_mounted d B rem low edges ageBound alphabet levels score rfl half depth
  have unit := (p).initial_space d ageBound degree axesBound
  have space := (p).seed_space d ageBound degree axesBound
  have L : low≤u^10 := by omega
  have wireFit : (A).relayWidth<2^W := by
    have exp : u*e≤u^10 := (Nat.mul_le_mul_left u (by omega : e≤u)).trans
      (by rw [←pow_two];exact Nat.pow_le_pow_right hu0 (by decide : 2≤10))
    have poly : u^e≤2^(u^10) := (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _).trans
      (by rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) exp)
    calc (A).relayWidth=2^low*(off*cells*3) := rfl
         _ ≤ 2^(u^10)*2^(u^10) := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) L) (slot.trans poly)
         _ < _ := by rw [←pow_add];apply Nat.pow_lt_pow_right (by decide);have:=Nat.one_le_pow 10 u hu0;omega
  have q6 : u^6≤u^10 := Nat.pow_le_pow_right hu0 (by decide)
  have axisBits : k≤W := by omega
  have fitCount : n<2^W := (Nat.pow_le_pow_right hu0 (by decide : 8≤10)).trans_lt
    ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans_lt Nat.lt_two_pow_self)
  have e3 : (A).control+3<(A).initialRecords := by
    have gap:=TickWorkspace.apart (u:=u) (by decide : 40<49)
    have size : 4≤TickWorkspace.stride u := (by decide : 4≤(2^1)^4).trans
      (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (Nat.one_le_pow 10 u hu0)) _)
    change TickWorkspace.base u 40+3<TickWorkspace.base u 49;omega
  have laneCount : j+1 = (B.repeat (u^8)).charge+rem := by dsimp only [j]; omega
  have lanes : (A).remainingLanes=2^(j+1) := by change 2^k=_;rw [laneCount]
  exact (A).started_ready steps edges B hj low off cells rfl e0 lanes rfl library suffix bits input n
    space banks sources wireFit (by rw [e0];exact axisBits) unit.degreeWord
    (by rw [laneCount]; exact unit.laneWord) unit.eight (by rfl) e3 fitCount

/-- The actual startup image carries all three seed node records at their final physical
addresses, with the same cursor site numbering as the physical compression run. -/
theorem Parameters.cursor_started_nodes (hu : e+40≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (degree : d≤u) (slot : off*cells*3≤u^e)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (bits : ℕ→Bool) (library suffix : List ℕ) (input : Memory W)
    (sources : (A).SeedSources steps edges library suffix bits input) :
    (A).InitialNodeMetadata (X).graph (finCongr (show k=(A).axes from rfl)) (fun _=>(A).relayWidth)
      ((A).startedMemory steps edges library bits input n) := by
  have seed:=cursor_ready B shape hk hu half depth degree slot alphabet levels score bits library suffix input sources
  let j:=k-1
  have eq : j+1=k := by dsimp only [j];omega
  have hj : 2≤j+1 := by omega
  exact seed_axes_cast B A eq hj hk eq rfl rfl _ seed.nodes

/-- Canonical block history table for the instantiated native tick. Every stage,
terminal span and iteration parameter is here calculated from the actual cursor. -/
theorem Parameters.cursor_active (field : FieldCode F W) (hu : e+40≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (degree : d≤u) (slot : off*cells*3≤u^e)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (allocation : B.allocations.sum≤u) (moveWords : fixedMoveWords B≤u)
    (growth : B.widthBase≤u) (factor : B.repeatFactor≤u) (chunk : shape.bits=2^(u^10-u^4))
    (bits : ℕ→Bool) (library suffix : List ℕ) (input : Memory W)
    (sources : (A).SeedSources steps edges library suffix bits input) (window : (A).RawWindow steps bits input) :
    let word:=B.cursor_repeat_word hu (by omega : low≤u^10) growth factor slot hk
    let Q:=B.recordTable B.alphabetCap W n rem X le_rfl word
    let raw:=List.ofFn (fun j : Fin (A).pairCapacity=>bits j.val)
    let origin:=(A).startedMemory steps edges library bits input n
    let machine:=NavigationPass.active («W»:=W) A B n rem edges
    Admission field machine.block machine.publicData (fun m=>m=input)
      (fun _=>((R).plan.decodeShared Q.codes ((R).readTerminal (fun z=>z.widthSum)) (A).pairCapacity raw).isSome)
      (fun _ out=>(A).Closed B n rem X bits Q.records origin out)
      ((A).bootTime steps edges W+(A).seedTime+6+((A).loopTime (u:=u) B n rem X+Archive.terminalTime ((A).terminal steps edges W))) := by
  intro word Q raw origin machine
  have hu0 : 0<u := by omega
  have age40 : 40≤u := (Nat.le_add_left 40 e).trans hu
  have stageDepth : k≤u^10+2*u^6 := (Nat.le_add_right k low).trans depth
  have card : v=(p).axes := Fintype.card_fin k
  have limits : (A).Limits u cur steps edges (A).pairCapacity := by
    rw [show steps=(P).directory rem (p).axes by rw [card]]
    exact Parameters.cursor_limits B shape age40 levels allocation score alphabet half depth chunk edges
  have room : (A).TerminalRoom steps edges W := by
    have cs:=(p).terminal_space B n rem age40 degree stageDepth rfl
    rw [card] at limits ⊢
    exact (cs limits window.old window.fresh).1
  have banks : (A).MountedRange steps edges W := by
    rw [show steps=(P).directory rem (p).axes by rw [card]]
    exact (p).block_seed_mounted d B rem low edges age40 alphabet levels score rfl half depth
  have unit:=(p).initial_space d age40 degree stageDepth
  have space:=(p).seed_space d age40 degree stageDepth
  have L : low≤u^10 := by omega
  have good:=cursor_record_fits B hu L growth factor slot hk
  let z:=((X).maxWidth+1)*B.widthBase^n
  have fixed : ∀j∈wordConstants P,j≤u := fun j h=>(repeated_fixed B n h).trans moveWords
  have q6 : u^6≤u^10 := Nat.pow_le_pow_right hu0 (by decide)
  have axisBits : k≤W := by omega
  let j:=k-1
  have e0 : j+1=k := by dsimp only [j];omega
  have hj : 2≤j+1 := e0.symm ▸ hk
  have e3 : (A).control+3<(A).initialRecords := by
    have gap:=TickWorkspace.apart (u:=u) (by decide : 40<49)
    have size : 4≤TickWorkspace.stride u := (by decide : 4≤(2^1)^4).trans
      (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (Nat.one_le_pow 10 u hu0)) _)
    change TickWorkspace.base u 40+3<TickWorkspace.base u 49;omega
  have seed:=cursor_ready B shape hk hu half depth degree slot alphabet levels score bits library suffix input sources
  obtain ⟨v0,count⟩:=(p).seed_visit d seed unit
  have visit:=v0.cast e0
  rw [cursor_cast B e0 hj hk] at visit
  have counter : (A).control+3<2^W := e3.trans_le ((Nat.le_add_right ..).trans space.endFit.le)
  have text : NavigationPass.active («W»:=W) A B n rem edges =
      (A).seedThen steps edges n ((repeated cur (((A).control+3:ℕ):Word W) (A).K B).seq
        (TerminalWireArchive.program ((A).terminal steps edges W))) := by
    exact active_seed_directory B A W n rem edges steps
      (congrArg ((P).directory rem) (show (A).axes=v from card.symm))
  change Admission field (NavigationPass.active («W»:=W) A B n rem edges).block
    (NavigationPass.active («W»:=W) A B n rem edges).publicData _ _ _ _
  rw [text]
  exact Archive.boot_seed_admission field A steps edges n library suffix bits input space banks sources
    (Nat.two_pow_pos _) axisBits unit.eight _ _ _ _
    (fun {labels registers slots} m=>(A).run_initialized (u:=u) B n rem X bits field z
      good.2.2 good.1 good.2.1 fixed age40 alphabet limits room space counter origin input
      window visit count seed.low m)

set_option maxHeartbeats 1600000 in
/-- Time of the complete installed navigation program at the actual trace cursor. -/
theorem Parameters.cursor_active_time (age : 384000≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (degree : d≤u) (alphabet : B.alphabetCap≤u)
    (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (tables : RAM.HistoryStageBody.Physical.staticSize B+RAM.HistoryStageBody.Physical.gridSize B≤u)
    (coefficient : B.nativeCoefficient B.alphabetCap≤u) (chunk : shape.bits=2^(u^10-u^4)) :
    (A).bootTime steps edges W+(A).seedTime+6+((A).loopTime (u:=u) B n rem X+Archive.terminalTime ((A).terminal steps edges W))
      ≤u*2^(u^10-u^4) := by
  let mass:=2^(u^10-u^4)
  have age0 : 0<u := (by decide : 0<384000).trans_le age
  have wordFactor : 16≤u := (by decide : 16≤384000).trans age
  have positive : 0< mass:=Nat.two_pow_pos _
  have card : v=k:=Fintype.card_fin _
  have absorbed (j : ℕ) (small : j≤u) : u^j*2^k≤ mass := by
    have room := (register_exponents wordFactor small half depth).1
    change 8*(u^j*2^k)≤ mass at room
    exact (Nat.le_mul_of_pos_left _ (by decide : 0<8)).trans room
  have plain (j : ℕ) (small : j≤u) : u^j≤ mass :=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans (absorbed j small)
  have Wpos : 0<W := Nat.mul_pos (by decide : 0<16) (Nat.pow_pos age0)
  have Wcap : W≤u^11 := by
    exact (Nat.mul_le_mul_right (u^10) wordFactor).trans_eq (pow_succ' u 10).symm
  have kCap : k≤u^11 := by
    have h:=Nat.pow_le_pow_right age0 (by decide : 6≤10)
    have w:=Nat.mul_le_mul_left (u^10) (by omega : 3≤u)
    rw [←pow_succ u 10] at w
    omega
  have bookTime : W*(A).codebookWords≤ mass := by
    have fits:=navigation_parameter_bits B p rem age tables levels
    calc
      _ = W*(Parameters.gridWords B u).length := congrArg (fun z:ℕ=>W*z) (Parameters.gridWords_length B u).symm
      _ ≤ W*((Parameters.gridWords B u)++(p).staticWords B n rem W).length := Nat.mul_le_mul_left _ (by simp)
      _ ≤ u^57 := fits
      _ ≤ _ := plain _ (by omega)
  have count : (steps).length≤u^9 := by
    rw [Program.directory_length,program_length,B.repeat_effects_length]
    calc _ ≤ u*(u^8) := Nat.mul_le_mul_right _ levels
         _ = _ := by ring
  have len : ((A).directory steps edges W).length≤u^11 := by
    rw [Archive.directory_length]
    have small : (steps).length+2≤u^10 := by
      have pos : 0<u^9 := Nat.pow_pos age0
      calc
        (steps).length+2 ≤ u^9+2 := Nat.add_le_add_right count 2
        _ ≤ u^9*3 := by omega
        _ ≤ u^9*u := Nat.mul_le_mul_left _ (by omega)
        _ = u^10 := (pow_succ u 9).symm
    calc
      _ ≤ u*(u^10) := Nat.mul_le_mul (by omega) small
      _ = _ := by ring
  have dirTime : W*((A).directory steps edges W).length≤ mass := by
    calc
      _ ≤ u^11*u^11 := Nat.mul_le_mul Wcap len
      _ = u^22 := by ring
      _ ≤ _ := plain _ (by omega)
  have histTime : W*(A).histWords steps≤ mass := by
    have h:=B.cursor_histogram_space (K:=B.alphabetCap) (rem:=rem) (by omega) alphabet levels score half depth
    let rows:=(((P).directory rem k).map Stage.motifs).sum
    change 8*(rows*B.alphabetCap*W)≤ mass at h
    rw [card]
    change W*(B.alphabetCap*rows)≤ mass
    rw [show W*(B.alphabetCap*rows)=rows*B.alphabetCap*W by ring];omega
  have fee (a : ℕ) (fits : W*a≤ mass) : a*(5*W+6)≤11*mass := calc
    _ ≤ a*(11*W) := Nat.mul_le_mul_left _ (by omega)
    _ = 11*(W*a) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ fits
  have boot : (A).bootTime steps edges W≤33*mass+33 := by
    have b:=fee _ bookTime
    have c:=fee _ dirTime
    have h:=fee _ histTime
    unfold Archive.bootTime
    omega
  have fixed : 2028*d+6*d+Archive.metadataCoefficient d≤u^3 := by
    have d2:=Nat.pow_le_pow_left degree 2
    have d1:=degree.trans (Nat.le_self_pow (by decide : 2≠0) u)
    have up : 1≤u^2 := Nat.pow_pos age0
    unfold Archive.metadataCoefficient
    calc
      _ ≤ 24018*u^2 := by omega
      _ ≤ u*u^2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have seedBudget : (A).seedTime≤59+mass := by
    apply ((p).seed_time d).trans
    apply Nat.add_le_add_left
    change (2028*d+6*d+Archive.metadataCoefficient d)*(k*2^k)≤ mass
    calc
      _ ≤ u^3*(u^11*2^k) := Nat.mul_le_mul fixed (Nat.mul_le_mul_right _ kCap)
      _ = u^14*2^k := by ring
      _ ≤ _ := absorbed _ (by omega)
  have counted : (A).loopTime (u:=u) B n rem X≤ mass := by
    unfold Archive.loopTime;rw [card]
    exact B.counted_cursor_time B.alphabetCap cur (A).cursor (by omega) levels coefficient rfl half depth
  have edgeCap : edges≤ mass := by
    rw [card]
    calc
      _ ≤ 2^(P).terminalExponent*(k*2^k) := (P).finalEdges_le rem k
      _ ≤ u*(u^11*2^k) := by rw [B.terminalExponent_repeat];gcongr
      _ = u^12*2^k := by ring
      _ ≤ _ := absorbed _ (by omega)
  let x:=(A).terminal steps edges W
  have ec : x.edges≤ mass := edgeCap
  have cap : x.capacity≤ mass := by
    change shape.bits/2-W*(A).histWords steps≤ mass
    rw [chunk];dsimp only [mass];omega
  have pf : (TerminalWireArchive.prefixWord x).work≤1000 := by
    change 79≤1000
    decide
  have ck : (TerminalWireArchive.checkWord x).work≤1000 := by
    change 24≤1000
    decide
  have terminal : Archive.terminalTime x≤4010*mass+4100 := by
    have a := Nat.mul_le_mul (Nat.add_le_add_right ec 1) (by omega : 2*(TerminalWireArchive.prefixWord x).work+4≤2004)
    have b := Nat.mul_le_mul (Nat.add_le_add_right cap 1) (by omega : 2*(TerminalWireArchive.checkWord x).work+4≤2004)
    unfold Archive.terminalTime
    omega
  have target := Nat.mul_le_mul_right mass age
  dsimp only [x] at terminal
  change _≤u*mass
  omega



end
end ThreeFlat.Diagonal.NavigationPass

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM.NavigationNodeRows PhysicalStage NavigationDirectory
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

theorem finalEdges_last {s : ℕ} (P : Program F s) (rem v K : ℕ) (c : Cursor) (layer : Layer)
    (count : layer.count=v*2^(P.charge+rem)) :
    P.finalEdges rem v=(lastLayer K (P.directory rem v) c layer).count*2^P.terminalExponent := by
  induction P generalizing v c layer with
  | done s =>
    simp only [Program.charge,Nat.zero_add] at count
    rw [Program.finalEdges,Program.directory,lastLayer,Program.terminalExponent,count];ring
  | shrink s t G ok tail ih =>
    apply ih
    rfl
  | refresh s t h pad g γ C G hm hh sym rows zero conn degree tail ih =>
    apply ih
    rfl

theorem Parameters.root_edges (p : Parameters) (B : Block F) (n rem W : ℕ)
    (axes : (B.repeat n).charge+rem=p.axes) :
    let A:=p.archive (2^B.exponent 0) W
    let ss:=(B.repeat n).directory rem p.axes
    let N:=p.nodeArchive A ss W
    let R:=p.rootArchive A N ss W
    (B.repeat n).finalEdges rem p.axes=R.rootCount*A.initialDegree := by
  intro A ss N R
  have start : A.seedLayer.count=p.axes*2^((B.repeat n).charge+rem) := by rw [axes];rfl
  change (B.repeat n).finalEdges rem p.axes =
    (lastLayer A.K ((B.repeat n).directory rem p.axes) A.cursor A.seedLayer).count * 2^(B.exponent 0)
  simpa only [B.terminalExponent_repeat] using
    finalEdges_last (B.repeat n) rem p.axes A.K A.cursor A.seedLayer start

theorem Parameters.staticWords_directory (p : Parameters) (B : Block F) (n rem W : ℕ)
    (axes : (B.repeat n).charge+rem=p.axes) :
    let A:=p.archive (2^B.exponent 0) W
    let ss:=(B.repeat n).directory rem p.axes
    let N:=p.nodeArchive A ss W
    let R:=p.rootArchive A N ss W
    let layers:=nodeLayers A.K ss A.cursor A.seedLayer
    p.staticWords B n rem W=A.directory ss ((B.repeat n).finalEdges rem p.axes) W++
      (nodeTape N.banks N.headerBase layers++(List.ofFn (fun j : Fin 22=>R.word j)++stageTape layers)) := by
  intro A ss N R layers
  have edges : (B.repeat n).finalEdges rem p.axes=R.rootCount*A.initialDegree :=
    p.root_edges B n rem W axes
  change (((A.directory ss (R.rootCount*A.initialDegree) W ++ nodeTape N.banks N.headerBase layers) ++
    List.ofFn (fun j : Fin 22=>R.word j)) ++ stageTape layers) = _
  simp only [edges,List.append_assoc]


end
end ThreeFlat.Diagonal.NavigationPass

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM TickChronology PhysicalStage ApproximateImage
open scoped Fin.CommRing Classical
noncomputable section

/-- The admission interpreter starts at bit one of the phase-selected auxiliary vector. -/
def entryHistory {a : ℕ} (phase : Phase) (oa na : Fin a→Bool) (j : ℕ) :=
  if h : 1+j<a then (if phase=.opening then na else oa) ⟨1+j,h⟩ else false

theorem entryHistory_read {a : ℕ} (ph : Phase) (oa na : Fin a→Bool)
    (L : TickAuxiliary.Layout a) :
    List.ofFn (fun j : Fin (L.wiresEnd-1)=>entryHistory ph oa na j.val) =
      List.ofFn (TickAuxiliary.project L (if ph=.opening then na else oa)).history := by
  apply congrArg List.ofFn
  funext j
  have h : 1+j.val<a := by have:=L.ordered.trans L.fits;have:=j.isLt;omega
  simp only [entryHistory,dite_eq_left h,TickAuxiliary.project,TickAuxiliary.historyAt]

/-- Branch selection in the native interpreter uses the history decoded by
the projected mathematical tick, for every word at either endpoint. -/
theorem entryHistory_decode {F : Type*} [CommSemiring F] {S : HistoryContraction.Shape}
    (P : HistoryContraction.Plan F S) (E : P.Codes) (bits : P.History→ℕ)
    {a : ℕ} (R : TickAuxiliary.GroupRegister P E bits a) (ph : Phase) (oa na : Fin a→Bool) :
    P.decodeShared E bits R.capacity (List.ofFn (fun j : Fin R.capacity=>entryHistory ph oa na j.val)) =
      TickAuxiliary.decode P E bits R.base (if ph=.opening then na else oa) := by
  have h : R.base.wiresEnd-1=R.capacity := by
    change 1+R.capacity-1=R.capacity
    omega
  have eqn:=entryHistory_read ph oa na R.base
  change _ = P.decodeShared E bits (R.base.wiresEnd-1) _
  rw [←eqn,h]

/-- All row-major pin fields, including both boundary vectors, fit below S0 at
the dyadic seed scales. -/
theorem mounted_fields_low {u nt ns np e : ℕ} (age : 40≤u) (exp : e≤u)
    (small : 2+nt+ns+np≤u^e) :
    2+pinCount (2^(u^3)) nt ns np (2^(u^10-u^4))≤TickWorkspace.base u 0 := by
  have pos : 0<u:=by omega
  let v:=2^(u^10)
  have q : 2^(u^3)≤v:=Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right pos (by decide : 3≤10))
  have c : 2^(u^10-u^4)≤v:=Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  have «meta» : 2+nt+ns+np≤v:=small.trans ((width_pow_le_two_pow_sq exp).trans
    (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right pos (by decide : 2≤10))))
  have big : 6≤v := (by omega : 6≤u).trans ((Nat.le_self_pow (by decide : 10≠0) u).trans Nat.lt_two_pow_self.le)
  change 2+pinCount _ nt ns np _≤1*v^4
  rw [one_mul];unfold pinCount
  calc
    _ ≤ 6*v := by omega
    _ ≤ v*v := Nat.mul_le_mul_right _ big
    _ ≤ v^4 := by rw [←pow_two];exact Nat.pow_le_pow_right (by omega) (by decide)

theorem mounted_boundaries {W u q nt ns np a teams capacity : ℕ} (c : Clock)
    (D : Fin q→Bool) (team step : ℕ) (par : Fin np→Bool) (oa na oc nc : Fin a→Bool) :
    let A:=TickPhysicalABI.mounted u a teams capacity q nt ns np
    let m:=TickMountedPins.memory (w:=W) (fields D (digits team nt) (digits step ns) par oa na oc nc)
    let entry:=TickNavigationEntry.input A c team step m
    2+pinCount q nt ns np a≤A.control → A.control+4≤A.clockWords → A.clockWords+4<2^W →
    TickPhysicalABI.Inputs A c entry team step ∧
    (∀ i : Fin a,entry (A.oldAux+i.val)=TickBitRelation.bitWord W (oa i)) ∧
    (∀ i : Fin a,entry (A.newAux+i.val)=TickBitRelation.bitWord W (na i)) ∧
    (∀ i : Fin a,entry (A.oldChunk+i.val)=TickBitRelation.bitWord W (oc i)) ∧
    (∀ i : Fin a,entry (A.newChunk+i.val)=TickBitRelation.bitWord W (nc i)) ∧
    ∀ j,j<A.control→entry j=m j := by
  intro A m entry low order fits
  have frame j (h : j<A.control) : entry j=m j:=TickNavigationEntry.before_scratch A c team step m j h order (by omega)
  have bits (seg : TickBoundaryFields.Segment) (i : Fin a) :
      entry (TickBoundaryFields.base 2 q nt ns np a seg+i.val)=
        TickBitRelation.bitWord W ((seg.select oa na oc nc) i) := by
    have loc:=TickMountedPins.has_fields (w:=W) (nt:=nt) (ns:=ns) D par oa na oc nc team step
    have inside : TickBoundaryFields.base 2 q nt ns np a seg+i.val<A.control := by
      have lt:=i.isLt;cases seg <;> simp only [TickBoundaryFields.base,TickBoundaryFields.Segment.number,pinCount] at * <;> omega
    rw [frame _ inside]
    exact TickBoundaryFields.boundary_bit seg i loc le_rfl
  refine ⟨TickNavigationEntry.hydrated A c team step m order fits,?_,?_,?_,?_,frame⟩
  · intro i;simpa [A,TickPhysicalABI.mounted,TickPhysicalABI.layout,TickBoundaryFields.base,TickBoundaryFields.Segment.number,
      TickBoundaryFields.Segment.select] using bits .oldAux i
  · intro i;simpa [A,TickPhysicalABI.mounted,TickPhysicalABI.layout,TickBoundaryFields.base,TickBoundaryFields.Segment.number,
      TickBoundaryFields.Segment.select] using bits .newAux i
  · intro i;simpa [A,TickPhysicalABI.mounted,TickPhysicalABI.layout,TickBoundaryFields.base,TickBoundaryFields.Segment.number,
      TickBoundaryFields.Segment.select] using bits .oldChunk i
  · intro i;simpa [A,TickPhysicalABI.mounted,TickPhysicalABI.layout,TickBoundaryFields.base,TickBoundaryFields.Segment.number,
      TickBoundaryFields.Segment.select] using bits .newChunk i

/-- Read the public codebook, chronological directory and guessed history from the same
physical inputs as the installed tick instruction stream, after its four-word prologue. -/
theorem Parameters.cursor_source {F : Type} [Field F] [Fintype F] {u w nt ns a teams : ℕ}
    (B : Block F) (p : Parameters) (n rem : ℕ) (I : PhysicalPrelude.Image F w)
    (D : Fin I.advice→Bool) (team step : ℕ) (clock : Clock) (oa na oc nc : Fin a→Bool)
    (default : Fin I.parameters→Bool) (extraWords : List ℕ) (tmp : ℕ) (es : List (EffectStream.Record (16*u^10)))
    (age : 40≤u) (pAge : p.age=u) (axes : (B.repeat n).charge+rem=p.axes)
    (rawAt : p.rawTables=2+I.advice+nt+ns) (oldAt : p.oldAux=2+I.advice+nt+ns+I.parameters)
    (newAt : p.newAux=p.oldAux+a) (cap : p.historyCapacity=a/2)
    (book : p.codebookWords=(Parameters.gridWords B u).length) (degree : 2^B.exponent 0≤u)
    (axisPos : 0<p.axes) (depth : p.axes≤u^10+2*u^6) :
    let W:=16*u^10
    let A:=p.archive (2^B.exponent 0) W
    let steps:=(B.repeat n).directory rem p.axes
    let edges:=(B.repeat n).finalEdges rem p.axes
    let N:=p.nodeArchive A steps W
    let R:=p.rootArchive A N steps W
    let layers:=nodeLayers A.K steps A.cursor A.seedLayer
    let library:=Parameters.gridWords B u
    let suffix:=nodeTape N.banks N.headerBase layers++(List.ofFn (fun j : Fin 22=>R.word j)++stageTape layers)
    let words:=(library++p.staticWords B n rem W)++extraWords
    let word:=fun (i : ℕ)=>((words[i]?.getD 0 : ℕ) : Word W)
    let par:=TraceMountedParameters.parameters I 0 (words.length+2*es.length)
      (TraceMountedParameters.seedWords words.length tmp word es) default
    let pins:=fields D (digits team nt) (digits step ns) par oa na oc nc
    let layout:=TickPhysicalABI.mounted u a teams (a/2) I.advice nt ns I.parameters
    let entry:=TickNavigationEntry.input layout clock team step (TickMountedPins.memory (w:=W) pins)
    let bits:=entryHistory (clock.phase step) oa na
    W*(words.length+2*es.length)+w*FixedTraceImage.count I.G≤I.parameters →
    2+pinCount I.advice nt ns I.parameters a≤layout.control →
    A.Limits u (A.control:Word W) steps edges A.pairCapacity →
    A.SeedSources steps edges library suffix bits entry ∧ A.RawWindow steps bits entry := by
  intro W A steps edges N R layers library suffix words word par pins layout entry bits pubRoom low limits
  have pos : 0<u:=by omega
  have wpos : 0<W:=by dsimp [W];positivity
  have minW : 3≤W := by dsimp [W];have h:=Nat.pow_pos (n:=10) pos;omega
  have vBig : 40<2^(u^10) := age.trans_lt ((Nat.le_self_pow (by decide : 10≠0) u).trans_lt Nat.lt_two_pow_self)
  have stBig : 40<TickWorkspace.stride u := vBig.trans_le (Nat.le_self_pow (by decide : 4≠0) _)
  have clockGap : layout.control+4≤layout.clockWords := (by have h:=TickWorkspace.apart (u:=u) (by decide : 0<1)
                                                            change TickWorkspace.base u 0+4≤TickWorkspace.base u 1;omega)
  have clockFit : layout.clockWords+4<2^W :=
    (Nat.add_le_add_left (by omega : 4≤TickWorkspace.stride u) _).trans_lt
      (TickWorkspace.word_space (by omega) (by omega : 1<TickWorkspace.stride u))
  have hyd:=TickNavigationEntry.hydrated layout clock team step (TickMountedPins.memory (w:=W) pins) clockGap clockFit
  have phaseAt : entry A.phase=((clock.phase step).tag:Word W) := by
    have addr : A.phase=layout.control+2 := by
      change TickWorkspace.base p.age 0+2=TickWorkspace.base u 0+2
      rw [pAge]
    rw [addr]
    exact hyd.1 (2:Fin 4)
  have flag : entry A.phase=1 ↔ clock.phase step=.opening := by
    rw [phaseAt]
    have big : 7<2^W := (by decide : 7<2^3).trans_le (Nat.pow_le_pow_right (by decide) minW)
    cases ph : clock.phase step <;> simp [Phase.tag,←Fin.val_inj,Nat.mod_eq_of_lt (by omega : 1<2^W),
      Nat.mod_eq_of_lt (by omega : 2<2^W),Nat.mod_eq_of_lt (by omega : 3<2^W),Nat.mod_eq_of_lt (by omega : 4<2^W),
      Nat.mod_eq_of_lt (by omega : 5<2^W),Nat.mod_eq_of_lt (by omega : 6<2^W)]
  have seedHigh : layout.control+4≤A.seed := by
    change TickWorkspace.base u 0+4≤TickWorkspace.base p.age 20
    rw [pAge];exact (Nat.add_le_add_left (by omega : 4≤TickWorkspace.stride u) _).trans
      (TickWorkspace.apart (by decide : 0<20))
  have rawLow : p.newAux+a≤layout.control := by
    rw [newAt,oldAt]
    dsimp only [pinCount] at low;omega
  have phaseLow : A.phase<A.seed := by change TickWorkspace.base p.age 0+2 < _;rw [pAge];change layout.control+2<A.seed;omega
  have oldLo : A.oldHistory+A.pairCapacity≤A.seed := by change p.oldAux+1+p.historyCapacity≤_;rw [cap];omega
  have newLo : A.newHistory+A.pairCapacity≤A.seed := by change p.newAux+1+p.historyCapacity≤_;rw [cap];omega
  have boundary (seg : TickBoundaryFields.Segment) (i : Fin a) :
      TickMountedPins.memory (w:=W) pins (TickBoundaryFields.base 2 I.advice nt ns I.parameters a seg+i.val)=
      TickBitRelation.bitWord W ((seg.select oa na oc nc) i) :=
    TickBoundaryFields.boundary_bit seg i (TickMountedPins.has_fields D par oa na oc nc team step) le_rfl
  have frame (j : ℕ) (hj : j<layout.control) :
      entry j=TickMountedPins.memory (w:=W) pins j :=
    TickNavigationEntry.before_scratch layout clock team step _ _ hj clockGap (by omega)
  have bitWord (b : Bool) : TickBitRelation.bitWord W b=(b.toNat : Word W) := by cases b <;> rfl
  have window : A.RawWindow steps bits entry := by
    refine ⟨phaseLow,oldLo,newLo,?_⟩
    intro i hi
    change i<p.historyCapacity at hi
    rw [cap] at hi
    let j : Fin a:=⟨1+i,by omega⟩
    have oldBit : entry (A.oldHistory+i)=(oa j).toNat := by
      rw [frame _ (by change p.oldAux+1+i<_;omega)]
      simpa [A,Parameters.archive,oldAt,j,TickBoundaryFields.base,TickBoundaryFields.Segment.number,
        TickBoundaryFields.Segment.select,Nat.add_assoc,bitWord] using boundary .oldAux j
    have newBit : entry (A.newHistory+i)=(na j).toNat := by
      rw [frame _ (by change p.newAux+1+i<_;omega)]
      simpa [A,Parameters.archive,newAt,oldAt,j,TickBoundaryFields.base,TickBoundaryFields.Segment.number,
        TickBoundaryFields.Segment.select,Nat.add_assoc,bitWord] using boundary .newAux j
    by_cases h : clock.phase step=.opening
    · simpa [Archive.hist,PackedStageArchive.Layout.source,flag.mpr h,bits,entryHistory,h,j,show 1+i<a by omega] using newBit
    · simpa [Archive.hist,PackedStageArchive.Layout.source,mt flag.mp h,bits,entryHistory,h,j,show 1+i<a by omega] using oldBit
  have fits : ∀ v∈A.directory steps edges W,v<2^W := by
    subst u
    have bounds:=(p.terminal_space B n rem age degree depth axes limits oldLo newLo).1.bounds
    exact p.seed_directory_fits (2^B.exponent 0) (B.repeat n) age degree axisPos depth limits bounds
  have shape : words=(library++(A.directory steps edges W++suffix))++extraWords := by
    dsimp only [words];rw [p.staticWords_directory B n rem W axes]
  have wordRoom : W*words.length≤I.parameters :=
    (Nat.mul_le_mul_left W (Nat.le_add_right words.length (2*es.length))).trans (by omega)
  have bookBound : library.length≤TickWorkspace.stride u := by
    have l : library.length≤words.length := by dsimp only [words];simp
    have h := Nat.le_mul_of_pos_left words.length wpos
    change 2+(I.advice+(nt+(ns+(I.parameters+(a+(a+(a+a)))))))≤TickWorkspace.base u 0 at low
    have baseZero : TickWorkspace.base u 0=TickWorkspace.stride u := by simp [TickWorkspace.base]
    rw [baseZero] at low;omega
  have mountedSeed:=TraceMountedParameters.physical_seed I D (digits team nt) (digits step ns) default oa na oc nc
    0 words.length tmp 0 0 0 word es wpos (by simpa using pubRoom)
  obtain ⟨_,read,_⟩:=mountedSeed
  refine ⟨⟨book,?_,phaseLow,?_,?_,?_,?_,limits.tables,fits,?_,?_⟩,window⟩
  · change p.rawTables+W*p.codebookWords=p.rawTables+W*library.length
    rw [book]
  · change TickWorkspace.base p.age 20≤TickWorkspace.base p.age 38
    have:=TickWorkspace.apart (u:=p.age) (by decide : 20<38);omega
  · change TickWorkspace.base p.age 38+library.length<2^W
    rw [pAge];exact (Nat.add_le_add_left bookBound _).trans_lt (TickWorkspace.word_space (by omega) (by omega : 38<TickWorkspace.stride u))
  · have l : library.length+(A.directory steps edges W).length≤words.length := by rw [shape];simp
    have b:=Nat.mul_le_mul_left W l
    rw [Nat.mul_add] at b
    change p.rawTables+W*p.codebookWords+W*(A.directory steps edges W).length≤A.seed
    have bookLen : p.codebookWords=library.length := book
    have rawEnd : p.rawTables+I.parameters=p.oldAux := by rw [rawAt,oldAt]
    rw [bookLen,Nat.add_assoc]
    exact (Nat.add_le_add_left (b.trans wordRoom) p.rawTables).trans (by rw [rawEnd];omega)
  · have h : W*A.histWords steps≤A.pairCapacity := limits.capacity
    change (if entry A.phase=1 then A.newHistory else A.oldHistory)+W*A.histWords steps≤A.seed
    split <;> omega
  · intro visible i hi j hj
    have append : words=visible++extraWords := shape
    have hiAll : i<words.length := by rw [append,List.length_append]; omega
    change entry (p.rawTables+W*i+j)=_
    have endAt:=Nat.mul_le_mul_left W (show i+1≤words.length from hiAll)
    rw [Nat.mul_succ] at endAt
    rw [rawAt,frame _ (by dsimp only [pinCount] at low;omega)]
    have wordAt : words[i]?=visible[i]? := by rw [append,List.getElem?_append_left hi]
    simpa only [Nat.add_zero,word,wordAt] using read i hiAll j hj
  · intro i hi;exact window.bits i (lt_of_lt_of_le hi limits.capacity)


end
end ThreeFlat.Diagonal.NavigationPass

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage NavigationDirectory
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F)
variable {u rem low stride cells tableOffset tariff e : ℕ} (shape : PhysicalPinsExpr.Shape)
local notation "p" => Parameters.cursor B u rem low stride cells shape tableOffset tariff
local notation "W" => (16*u^10)
local notation "d" => 2^B.exponent 0
local notation "P" => B.repeat (u^8)
local notation "k" => (P).charge+rem
local notation "off" => 1+((k+low)+(k+low))
local notation "A" => (p).archive d W
local notation "cur" => ((A).control:Word W)
local notation "ctr" => (((A).control+3:ℕ):Word W)
variable (hk : 2 ≤ (B.repeat (u^8)).charge + rem)
local notation "X" => B.cursorState hk low off cells
local notation "ss" => (P).directory rem (Fintype.card (X).Base)
local notation "edges" => (P).finalEdges rem (Fintype.card (X).Base)
local notation "N" => (p).nodeArchive A ss W
local notation "finishAt" => finish (A).K ss (A).cursor

/-- Seed half-widths are read at their original S49 addresses after the entire
adaptive journal. The published row cap includes every initial incident slot. -/
theorem cursor_seed_contents (hu : e+40≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (degree : d≤u) (slot : off*cells*3≤u^e)
    (room : (A).TerminalRoom ss edges W) (raw : List Bool) {origin final : Memory W}
    (journal : (A).Journal u cur ctr P rem X (A).cursor raw origin final)
    («meta» : (A).InitialNodeMetadata (X).graph (finCongr (show k=(A).axes from rfl)) (fun _=>(A).relayWidth) origin) :
    RowContents (A).seedData (fun i=>i<(finishAt).heap ∨ (A).initialRecords≤ i ∧ i<(A).metadataEnd)
      (fun i=>(final i).val) (N).halfCap (N).motifCap := by
  have hu0 : 1≤u := by omega
  have ageBound : 40 ≤ u := by omega
  have axesBound : k ≤ u^10+2*u^6 := (Nat.le_add_right k low).trans depth
  have bounds := (p).initial_space d ageBound degree axesBound
  have wire : (A).relayWidth<2^W := by
    have exp : u*e≤u^10 := (Nat.mul_le_mul_left u (by omega : e≤u)).trans
      (by rw [←pow_two];exact Nat.pow_le_pow_right hu0 (by decide : 2≤10))
    have poly : u^e≤2^(u^10) := (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _).trans
      (by rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) exp)
    calc (A).relayWidth=2^low*(off*cells*3) := rfl
         _ ≤ 2^(u^10)*2^(u^10) :=
           Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega)) (slot.trans poly)
         _ < _ := by rw [←pow_add];apply Nat.pow_lt_pow_right (by decide);have:=Nat.one_le_pow 10 u hu0;omega
  have ctrLow : (A).control+3<(A).initialRecords := by
    have gap:=TickWorkspace.apart (u:=u) (by decide : 40<49)
    have size : 4≤TickWorkspace.stride u := (by decide : 4≤(2^1)^4).trans
      (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (Nat.one_le_pow 10 u hu0)) _)
    change TickWorkspace.base u 40+3<TickWorkspace.base u 49
    omega
  have cc : (ctr).val=(A).control+3 := Fin.val_cast_of_lt
    (ctrLow.trans_le ((Nat.le_add_right ..).trans bounds.records.endFit.le))
  have cp : (cur).val=(A).control := Fin.val_cast_of_lt bounds.records.controlRoom
  have seedRead := (Archive.InitialNodeMetadata.seedData A (X).graph _ origin «meta» rfl
    bounds.degreeWord wire bounds.records.endFit).1
  have fp := Archive.InitialNodeMetadata.seedFootprint A (X).graph _ origin «meta» rfl
    bounds.degreeWord wire bounds.records.endFit
  have eq (i : ℕ) (hi : (A).initialRecords≤ i ∧ i<(A).metadataEnd) : (final i).val=(origin i).val := by
    have hHeader:=room.header
    have hHeap:=room.control
    exact congrArg Fin.val (Archive.Journal.frame P rem X (A).cursor raw journal
      (by rw [cp];omega) (by rw [cc];omega) ⟨.inr (by omega),.inr (by omega)⟩)
  refine ⟨seedRead.of_footprint fp eq,(fp.transfer fp eq).mono (fun _ hi=>Or.inr hi),?_,?_⟩
  · intro j
    simp only [Archive.seedData,List.length_replicate]
    change 2*(A).initialDegree≤ maxRows stageHalves (2*(A).initialDegree) ss
    have base (rows : List Stage) : 2*(A).initialDegree≤ maxRows stageHalves (2*(A).initialDegree) rows := by
      induction rows with
      | nil => exact le_rfl
      | cons r rs ih => exact ih.trans (le_max_right _ _)
    exact base _
  · intro bad
    exact False.elim (bad rfl)


/-- At an admitted history, all seed incidence fields retained at S49 can be
read directly at the original cursor ordinals after the terminal-prefix writes. -/
theorem cursor_seed_half_rows (hu : e+40≤u) (half : low=u^10/2)
    (depth : k+low≤u^10+2*u^6) (degree : d≤u) (slot : off*cells*3≤u^e)
    (room : (A).TerminalRoom ss edges W) (bits : ℕ→Bool) (E : ((P).run rem X).Records)
    {origin final : Memory W} (closed : (A).Closed B (u^8) rem X bits E origin final)
    («meta» : (A).InitialNodeMetadata (X).graph (finCongr (show k=(A).axes from rfl)) (fun _=>(A).relayWidth) origin) :
    State.HalfRows ((A).cursorSeedSites B hk low off cells rfl rfl)
      (fun i=>TickWorkspace.base u 49≤ i ∧ i<TickWorkspace.base u 53) (fun i=>(final i).val) := by
  have hu0 : 1≤u:=by omega
  have ageBound : 40 ≤ u := by omega
  have axesBound : k ≤ u^10+2*u^6 := (Nat.le_add_right k low).trans depth
  have bounds := (p).initial_space d ageBound degree axesBound
  let raw:=List.ofFn (fun j : Fin (A).pairCapacity=>bits j.val)
  obtain ⟨mid,journal,_,after⟩:=Archive.closed_frame A B (u^8) rem X bits E closed
  have exp : u*e≤u^10 := (Nat.mul_le_mul_left u (by omega : e≤u)).trans
    (by rw [←pow_two];exact Nat.pow_le_pow_right hu0 (by decide : 2≤10))
  have poly : u^e≤2^(u^10) := (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _).trans
    (by rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) exp)
  have wsmall : (A).relayWidth≤2^(2*u^10) := by
    change 2^low*(off*cells*3)≤_
    calc
      _≤2^(u^10)*2^(u^10):=Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega)) (slot.trans poly)
      _=_:=by rw [←pow_add,two_mul]
  have wire : (A).relayWidth<2^W := wsmall.trans_lt (Nat.pow_lt_pow_right (by decide) (by have:=Nat.one_le_pow 10 u hu0;omega))
  have doubled : 2*d≤2^(u^10) := by
    have mm:=Nat.mul_le_mul_left u (show 2≤u by omega)
    have sq:=Nat.pow_le_pow_right hu0 (by decide : 2≤10)
    rw [pow_two] at sq
    exact (by omega : 2*d≤u^10).trans (Nat.lt_two_pow_self (n:=u^10)).le
  have all : 2*d*(A).relayWidth<2^W := by
    apply (Nat.mul_le_mul doubled wsmall).trans_lt
    rw [←pow_add];exact Nat.pow_lt_pow_right (by decide) (by have:=Nat.one_le_pow 10 u hu0;omega)
  have edge : (X).edgeCount≤2^W := by
    have lower:=bounds.widthsBeforeRecords
    change (A).cursor.width+k*d*2^k≤(A).initialRecords at lower
    have recordBound : (A).initialRecords≤(A).metadataEnd := Nat.le_add_right ..
    change Fintype.card (Fin k)*d*2^k≤_
    rw [Fintype.card_fin]
    exact (Nat.le_add_left ..).trans (lower.trans (recordBound.trans bounds.records.endFit.le))
  have src:=Archive.InitialNodeMetadata.cursorHalfRows A B hk low off cells rfl rfl rfl rfl origin «meta»
    bounds.records.endFit bounds.degreeWord edge wire all
  have ctrLow : (A).control+3<(A).initialRecords := by
    have gap:=TickWorkspace.apart (u:=u) (by decide : 40<49)
    have size : 4≤TickWorkspace.stride u := (by decide : 4≤(2^1)^4).trans
      (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (Nat.one_le_pow 10 u hu0)) _)
    change TickWorkspace.base u 40+3<TickWorkspace.base u 49
    omega
  have cc : (ctr).val=(A).control+3 := Fin.val_cast_of_lt
    (ctrLow.trans_le ((Nat.le_add_right ..).trans bounds.records.endFit.le))
  have cp : (cur).val=(A).control := Fin.val_cast_of_lt bounds.records.controlRoom
  have eq (i : ℕ) (hi : (A).initialRecords≤ i ∧ i<(A).metadataEnd) : (mid i).val=(origin i).val := by
    have hHeader:=room.header
    have hHeap:=room.control
    exact congrArg Fin.val (Archive.Journal.frame P rem X (A).cursor raw journal
      (by rw [cp];omega) (by rw [cc];omega) ⟨.inr (by omega),.inr (by omega)⟩)

  refine src.transfer ?_ ?_
  · intro i hi
    have limit:=room.control
    have below:=bounds.controlBeforeRecords
    have late:=after i (.inr (by change (finishAt).heap+edges+1≤ i;omega))
    exact (congrArg Fin.val late).trans (eq i hi)
  · intro i hi
    have head:=bounds.recordSpan
    have gap:=TickWorkspace.apart (u:=u) (by decide : 49<53)
    exact ⟨hi.1,hi.2.trans_le (head.trans gap)⟩

/-- The selected seed reads its kernel and incidence metadata from the completed navigation archive. -/
theorem cursor_seed_metadata (hu : e+40≤u)
    (depth : k+low≤u^10+2*u^6) (degree : d≤u)
    (room : (A).TerminalRoom ss edges W) (bits : ℕ→Bool) (E : ((P).run rem X).Records)
    {origin final : Memory W} (closed : (A).Closed B (u^8) rem X bits E origin final)
    («meta» : (A).InitialNodeMetadata (X).graph (finCongr (show k=(A).axes from rfl)) (fun _=>(A).relayWidth) origin) :
    (A).InitialNodeMetadata (X).graph (finCongr (show k=(A).axes from rfl)) (fun _=>(A).relayWidth) final := by
  have hu0 : 1≤u:=by omega
  have ageBound : 40 ≤ u := by omega
  have axesBound : k ≤ u^10+2*u^6 := (Nat.le_add_right k low).trans depth
  have bounds := (p).initial_space d ageBound degree axesBound
  let raw:=List.ofFn (fun j : Fin (A).pairCapacity=>bits j.val)
  obtain ⟨mid,journal,_,after⟩:=Archive.closed_frame A B (u^8) rem X bits E closed
  have ctrLow : (A).control+3<(A).initialRecords := by
    have gap:=TickWorkspace.apart (u:=u) (by decide : 40<49)
    have size : 4≤TickWorkspace.stride u := (by decide : 4≤(2^1)^4).trans
      (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (Nat.one_le_pow 10 u hu0)) _)
    change TickWorkspace.base u 40+3<TickWorkspace.base u 49
    omega
  have cc : (ctr).val=(A).control+3 := Fin.val_cast_of_lt
    (ctrLow.trans_le ((Nat.le_add_right ..).trans bounds.records.endFit.le))
  have cp : (cur).val=(A).control := Fin.val_cast_of_lt bounds.records.controlRoom
  have eq (i : ℕ) (hi : (A).initialRecords≤ i ∧ i<(A).metadataEnd) : (mid i).val=(origin i).val := by
    have hHeader:=room.header
    have hHeap:=room.control
    exact congrArg Fin.val (Archive.Journal.frame P rem X (A).cursor raw journal
      (by rw [cp];omega) (by rw [cc];omega) ⟨.inr (by omega),.inr (by omega)⟩)

  apply Archive.InitialNodeMetadata.transfer A (X).graph (finCongr (show k=(A).axes from rfl))
    (fun _=>(A).relayWidth) «meta» rfl
  intro i hi
  have limit:=room.control
  have below:=bounds.controlBeforeRecords
  have late:=after i (.inr (by change (finishAt).heap+edges+1≤ i;omega))
  exact late.trans (Fin.ext (eq i hi))

end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage TickChronology TickAuxiliary ApproximateImage
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F]
variable {u rem low stride cells tariff e nt ns inside teams period last paramBase templateBase : ℕ}
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "a" => (2^(u^10-u^4):ℕ)
variable (B : Block F) (I : PhysicalPrelude.Image F (16*u^10))
local notation "shape" => (⟨I.advice,nt,ns,I.parameters,a,inside,teams,period,last,paramBase,templateBase⟩ : PhysicalPinsExpr.Shape)
local notation "p" => Parameters.cursor B u rem low stride cells shape 0 tariff
local notation "d" => 2^(B.exponent 0)
local notation "A" => (p).archive d W
local notation "k" => (B.repeat n).charge+rem
local notation "steps" => (B.repeat n).directory rem (p).axes
local notation "edges" => (B.repeat n).finalEdges rem (p).axes
local notation "N" => (p).nodeArchive A steps W
local notation "root" => (p).rootArchive A N steps W
local notation "layers" => nodeLayers (A).K steps (A).cursor (A).seedLayer
local notation "lib" => Parameters.gridWords B u
local notation "tail" => nodeTape (N).banks (N).headerBase layers++(List.ofFn (fun j : Fin 22=>(root).word j)++stageTape layers)
local notation "words" => lib++(p).staticWords B n rem W
local notation "abi" => TickPhysicalABI.mounted u a teams (a/2) I.advice nt ns I.parameters
variable (D : Fin I.advice→Bool) (par : Fin I.parameters→Bool) (clock : Clock) (team t : ℕ)
    (oa na oc nc : Fin (2^(u^10-u^4))→Bool)
local notation "pin" => fields D (digits team nt) (digits t ns) par oa na oc nc
local notation "entry" => TickNavigationEntry.input abi clock team t (TickMountedPins.memory (w:=W) pin)
local notation "raw" => entryHistory (clock.phase t) oa na

set_option maxHeartbeats 1600000 in
/-- The actual mounted H parameter vector supplies the complete source used by both the
admitted and rejected native navigation procedures. Its tag, RAM frame and parser
all refer to this same decoded physical history. -/
theorem Parameters.mounted_cursor_source (extraWords : List ℕ) (tmp : ℕ) (es : List (EffectStream.Record W))
    (age : 40≤u) (half : low=u^10/2) (depth : k+low≤u^10+2*u^6) (hk : 2≤k)
    (degree : d≤u) (levels : B.levels+1≤u) (allocation : B.allocations.sum≤u)
    (score : B.costFactors.sum≤u) (alphabet : B.alphabetCap≤u)
    (adv : I.advice=2^(u^3)) (exp : e≤u) («meta» : 2+nt+ns+I.parameters≤u^e)
    (allFit : W*((words++extraWords).length+2*es.length)+W*FixedTraceImage.count I.G≤I.parameters)
    (mounted : TraceMountedParameters.parameters I 0 ((words++extraWords).length+2*es.length)
      (TraceMountedParameters.seedWords (words++extraWords).length tmp (fun i=>((words++extraWords)[i]?.getD 0 : Word W)) es)
      (fun _=>false)=par) :
    (A).SeedSources steps edges lib tail raw entry ∧ (A).RawWindow steps raw entry ∧
      2+pinCount I.advice nt ns I.parameters a≤(abi).control ∧
      W*(lib++(p).staticWords B n rem W).length≤I.parameters := by
  have lowPins : 2+pinCount I.advice nt ns I.parameters a≤(abi).control := by
    change 2+pinCount I.advice nt ns I.parameters a≤TickWorkspace.base u 0
    rw [adv]
    exact mounted_fields_low age exp «meta»
  have limit:=Parameters.cursor_limits (stride:=stride) (cells:=cells) (off:=0) (tariff:=tariff)
    B shape age levels allocation score alphabet half depth rfl edges
  have libSize : (p).codebookWords=(lib).length := (Parameters.gridWords_length B u).symm
  have axisPositive : 0 < (p).axes := Nat.lt_of_lt_of_le (by decide : 0 < 2) hk
  have axisDepth : (p).axes ≤ u^10+2*u^6 := (Nat.le_add_right k low).trans depth
  have rawTables : (p).rawTables = 2+I.advice+nt+ns := rfl
  let observed (params : Fin I.parameters → Bool) : Prop :=
    let inputPins := fields D (digits team nt) (digits t ns) params oa na oc nc
    let inputMem := TickNavigationEntry.input abi clock team t (TickMountedPins.memory (w:=W) inputPins)
    (A).SeedSources steps edges lib tail raw inputMem ∧ (A).RawWindow steps raw inputMem
  let imageWords := words++extraWords
  let imageWord := fun (i : ℕ) => ((imageWords[i]?.getD 0 : ℕ) : Word W)
  let decodedParams := TraceMountedParameters.parameters I 0 (imageWords.length+2*es.length)
    (TraceMountedParameters.seedWords imageWords.length tmp imageWord es) (fun _ => false)
  have nativeReads : observed decodedParams :=
    Parameters.cursor_source (u:=u) (w:=W) (nt:=nt) (ns:=ns) («a»:=a) (teams:=teams)
      B p n rem I D team t clock oa na oc nc (fun _=>false) extraWords tmp es age rfl rfl
      rawTables rfl rfl rfl libSize degree axisPositive axisDepth allFit lowPins limit
  have recorded : decodedParams = par := mounted
  have finalReads : observed par := (congrArg observed recorded).mp nativeReads
  refine ⟨finalReads.1,finalReads.2,lowPins,?_⟩
  have base : W*(words).length≤W*((words++extraWords).length+2*es.length) := Nat.mul_le_mul_left _ (by simp only [List.length_append];omega)
  exact base.trans ((Nat.le_add_right _ _).trans allFit)


end
end ThreeFlat.Diagonal.NavigationPass

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PhysicalStage NavigationDirectory
noncomputable section
variable {F : Type} [Field F]

/-- The header, heap and true terminal prefix of an admitted history lie in the retained navigation banks. -/
theorem Parameters.terminal_half_ranges (pars : Parameters) (degree W : ℕ) {s : ℕ}
    (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem)) (card : Fintype.card X.Base=pars.axes)
    (h : (P.run rem X).plan.History)
    (room : (pars.archive degree W).TerminalRoom (P.directory rem pars.axes) (P.finalEdges rem pars.axes) W) :
    let A:=pars.archive degree W
    let steps:=P.directory rem pars.axes
    let edges:=P.finalEdges rem pars.axes
    let stop:=finish A.K steps A.cursor
    let wire:=A.terminal steps edges W
    TickWorkspace.base pars.age 20≤ stop.header ∧ stop.heap≤TickWorkspace.base pars.age 40 ∧
      TickWorkspace.base pars.age 20≤wire.prefixBase ∧
      wire.prefixBase+((P.run rem X).terminalLayer h).state.edgeCount≤TickWorkspace.base pars.age 40 := by
  intro A steps edges stop wire
  have count : ((P.run rem X).terminalLayer h).state.edgeCount=edges :=
    (P.finalEdges_eq rem X h).trans (congrArg (P.finalEdges rem) card)
  have upper : stop.heap+edges<TickWorkspace.base pars.age 40:=room.control
  have lower : TickWorkspace.base pars.age 20≤ stop.heap:=room.seed
  have head : stop.header=TickWorkspace.base pars.age 20+64+64*steps.length:=header_finish A.K steps A.cursor
  change TickWorkspace.base pars.age 20≤ stop.header ∧ stop.heap≤TickWorkspace.base pars.age 40 ∧
    TickWorkspace.base pars.age 20≤ stop.heap ∧
    stop.heap+((P.run rem X).terminalLayer h).state.edgeCount≤TickWorkspace.base pars.age 40
  rw [count]
  omega


end
end ThreeFlat.Diagonal.NavigationPass

end OAI
