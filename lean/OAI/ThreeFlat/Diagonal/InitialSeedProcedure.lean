import OAI.ThreeFlat.Diagonal.InitialMetadataActual
import OAI.ThreeFlat.Diagonal.TraceCursorBootstrap

namespace OAI
/-! # Five seed scans preserve the mounted history and publish every initial node -/
namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalProcedure
open CompressorPacking.Native
open scoped Classical Fin.CommRing
noncomputable section
variable {W t : ℕ} {B : Type} (A : Archive)
set_option quotPrecheck false
local notation "C" => (⟨A.cursor.graph,A.axes*A.initialDegree,A.cursor.width⟩ : SlotImage.Columns)
local notation "cur" => (A.control : Word W)
local notation "R" => A.axes*A.initialDegree
local notation "z" => InitialRelayBootstrap.image C A.axes A.initialDegree A.remainingLanes A.relayWidth

structure SeedSpace (W : ℕ) : Prop extends A.MetadataSpace W where
  seedBefore : A.seed+64≤A.cursor.graph
  graphBefore : A.cursor.graph+6*(A.axes*A.initialDegree)≤A.cursor.width
  widthsBefore : A.cursor.width+(A.axes*A.initialDegree)*A.remainingLanes≤A.control
  controlsBefore : A.control<A.initialRecords

/-- Separation needed by the two cursor graph scans, independently of where
the later metadata scans place their output relative to the control cell. -/
structure RelayWindow (W : ℕ) : Prop where
  controlRoom : A.control<2^W
  seedBefore : A.seed+64≤A.cursor.graph
  graphBefore : A.cursor.graph+6*(A.axes*A.initialDegree)≤A.cursor.width
  widthsBefore : A.cursor.width+(A.axes*A.initialDegree)*A.remainingLanes≤A.control

theorem SeedSpace.window {A : Archive} {W : ℕ} (s : A.SeedSpace W) : A.RelayWindow W :=
  ⟨s.controlRoom,s.seedBefore,s.graphBefore,s.widthsBefore⟩

def seedProgram : Procedure W :=
  (InitialRelayBootstrap.procedure cur C A.axes A.initialDegree A.relayWidth).seq A.initialMetadata

def seedTime :=
  59+2028*(A.axes*A.initialDegree)+6*((A.axes*A.initialDegree)*A.remainingLanes)+
    metadataCoefficient A.initialDegree*A.initialSites

def seedKeep (a : ℕ) : Prop := a<A.cursor.graph ∨ a=A.control

structure MountedRange (steps : List NavigationDirectory.Stage) (edges W : ℕ) : Prop where
  headers : A.seed+(A.directory steps edges W).length≤A.cursor.graph
  counts : A.cursor.dense+A.histWords steps≤A.cursor.graph

variable {A}
private theorem seedWindow (s : A.SeedSpace W) : (C).graph≤(C).widths ∧ (C).widths≤A.control :=
  ⟨(Nat.le_add_right ..).trans s.graphBefore,(Nat.le_add_right ..).trans s.widthsBefore⟩

private theorem seed_read {m : Memory W} (H : Scans.Header cur m A.seed 63 A.seedWords) (i : ℕ) (hi : i≤63) :
    m (m (cur).val+(i:Word W)).val=(A.seedWords i:Word W) := by
  have v:=congrArg (fun a : ℕ => (a:Word W)) (H.get i hi)
  simpa only [Fin.cast_val_eq_self,RAM.HeaderScan.headerWord] using v

private theorem seed_header_addr {m : Memory W} (H : Scans.Header cur m A.seed 63 A.seedWords) (i : ℕ) (hi : i≤63) :
    (m (cur).val+(i:Word W)).val=A.seed+i := by
  rw [←Fin.cast_val_eq_self (m (cur).val),←Nat.cast_add,Fin.val_cast_of_lt (by rw [H.pointer];have:=H.fit;omega),H.pointer]

theorem RelayWindow.columns (s : A.RelayWindow W) : (C).graph≤(C).widths ∧ (C).widths≤A.control :=
  ⟨(Nat.le_add_right ..).trans s.graphBefore,(Nat.le_add_right ..).trans s.widthsBefore⟩

theorem RelayWindow.loaded (s : A.RelayWindow W) {m : Memory W} (H : Scans.Header cur m A.seed 63 A.seedWords) :
    InitialRelayBootstrap.loaded cur C A.axes A.initialDegree A.remainingLanes m := by
  apply InitialRelayBootstrap.loaded_of_frame
  · exact ⟨seed_read H 0 (by decide),seed_read H 1 (by decide)⟩
  · exact ⟨seed_read H 2 (by decide),seed_read H 3 (by decide)⟩
  · rintro a (rfl|rfl|rfl)
    · right; rw [Fin.val_cast_of_lt s.controlRoom];exact s.graphBefore.trans (s.columns).2
    · left
      change (m (cur).val+((2:ℕ):Word W)).val < A.cursor.graph
      rw [seed_header_addr H 2 (by decide)]
      have := s.seedBefore
      omega
    · left
      change (m (cur).val+((3:ℕ):Word W)).val < A.cursor.graph
      rw [seed_header_addr H 3 (by decide)]
      have := s.seedBefore
      omega

theorem RelayWindow.relay_frame (s : A.RelayWindow W) (m : Memory W) (i : ℕ) (keep : A.seedKeep i) :
    z m i=m i := by
  have g : i<(C).graph ∨ (C).graph+6*R≤ i := keep.elim Or.inl (fun h=>.inr (by rw [h];exact s.graphBefore.trans (s.columns).2))
  have w : i<(C).widths ∨ (C).widths+R*A.remainingLanes≤ i :=
    keep.elim (fun h=>.inl (h.trans_le (s.columns).1)) (fun h=>.inr (by rw [h];exact s.widthsBefore))
  rw [InitialRelayBootstrap.image,InitialRelayWidth.image_outside _ _ _ _ _ w]
  simp [InitialRelayGraph.image,fillSegment,show ¬((C).graph≤ i ∧ i<(C).graph+6*R) by omega]

theorem RelayWindow.relay_header (s : A.RelayWindow W) {m : Memory W} (H : Scans.Header cur m A.seed 63 A.seedWords) :
    Scans.Header cur (z m) A.seed 63 A.seedWords := by
  refine ⟨?_,H.fit,?_⟩
  · rw [s.relay_frame m _ (.inr (Fin.val_cast_of_lt s.controlRoom))];exact H.pointer
  · intro i hi
    rw [s.relay_frame m _ (.inl (by have:=s.seedBefore;omega))];exact H.values i hi

theorem SeedSpace.loaded (s : A.SeedSpace W) {m : Memory W} (H : Scans.Header cur m A.seed 63 A.seedWords) :
    InitialRelayBootstrap.loaded cur C A.axes A.initialDegree A.remainingLanes m :=
  s.window.loaded H

theorem SeedSpace.relay_frame (s : A.SeedSpace W) (m : Memory W) (i : ℕ) (keep : A.seedKeep i) :
    z m i=m i :=
  s.window.relay_frame m i keep

theorem SeedSpace.relay_header (s : A.SeedSpace W) {m : Memory W} (H : Scans.Header cur m A.seed 63 A.seedWords) :
    Scans.Header cur (z m) A.seed 63 A.seedWords :=
  s.window.relay_header H

theorem Live.seed_frame {steps : List NavigationDirectory.Stage} {e : ℕ} {raw : ℕ→Bool} {m out : Memory W}
    {c0 c1 : NavigationDirectory.Cursor} (S : A.MountedRange steps e W)
    (L : A.Live steps e raw cur c0 m) (monotone : c0.header≤c1.header)
    (pointer : (out (cur).val).val=c1.header) (low : ∀i,i<A.cursor.graph → out i=m i) :
    A.Live steps e raw cur c1 out := by
  refine ⟨pointer,?_,?_⟩
  · intro i v h get
    have bound : i<(A.directory steps e W).length := by
      by_contra! large
      simp [List.getElem?_eq_none large] at get
    rw [low _ ((Nat.add_lt_add_left bound _).trans_le S.headers)]
    exact L.headers i v (monotone.trans h) get
  · intro j hj
    rw [low _ ((Nat.add_lt_add_left hj _).trans_le S.counts)]
    exact L.counts j hj

variable (A)
theorem seed_spec {G : LiftedSlots B A.initialDegree (BitWord t)} (base : B ≃ Fin A.axes)
    (width : SlotImage.Edge B (BitWord t) A.initialDegree→ℕ) (m : Memory W) (s : A.SeedSpace W)
    (H : Scans.Header cur m A.seed 63 A.seedWords) (laneCount : A.remainingLanes=2^t)
    (degree : 0<A.initialDegree) (axes : A.axes≤W) (degFits : 2*A.initialDegree<2^W)
    (laneFits : 2^t<2^W) (wide : 8<2^W)
    (graph : SlotImage.Stored G base (tagOrdinal t) C (fun i=>(z m i).val) width) :
    A.seedProgram.Spec (fun mem=>mem=m)
      (fun _ out=>A.InitialNodeMetadata G base width out ∧
        SlotImage.Stored G base (tagOrdinal t) C (fun i=>(out i).val) width ∧
        ∀i,A.seedKeep i → out i=m i) A.seedTime := by
  have wf:=s.widthsBefore.trans_lt s.controlRoom
  have gStrict:=s.graphBefore.trans_lt ((seedWindow s).2.trans_lt s.controlRoom)
  have graphLow:=s.graphBefore.trans ((seedWindow s).2.trans s.controlsBefore.le)
  have widthLow := s.widthsBefore.trans s.controlsBefore.le
  rw [laneCount] at widthLow
  have L : (InitialRelayBootstrap.procedure cur C A.axes A.initialDegree A.relayWidth).Spec
      (fun mem=>mem=m) (fun _ out=>out=z m)
      (InitialRelayBootstrap.budget W C A.axes A.initialDegree A.remainingLanes) := by
    intro programCount registerCount wordCount M pc reg pub exit installed table c input start same
    subst input
    exact InitialRelayBootstrap.spec cur C A.axes A.initialDegree A.remainingLanes A.relayWidth
      gStrict wf degree axes (by omega) M pc reg pub exit installed table c m start (s.loaded H)
  intro programs registers words machine
  apply Procedure.Spec.mono (A := A.seedProgram)
    (Procedure.Spec.seq (A := InitialRelayBootstrap.procedure cur C A.axes A.initialDegree A.relayWidth)
      (B := A.initialMetadata) L
      (A.initialMetadata_spec G base width (z m) s.toMetadataSpace (s.relay_header H) graph
        laneCount graphLow widthLow degFits laneFits wide) (fun _ _ h => h))
    (fun _ h => h) _ _ machine
  · rintro _ out ⟨_,rfl,data,img,frame⟩
    refine ⟨data,img,fun i keep=>?_⟩
    have lo : i<A.initialRecords := (keep.elim (fun h=>h.le.trans ((seedWindow s).1.trans (seedWindow s).2)) (fun e=>e.le)).trans_lt s.controlsBefore
    exact (frame i (.inl lo)).trans (s.relay_frame m i keep)
  · rw [InitialRelayBootstrap.budget_eq,seedTime];omega

/-- The seed scans leave the full mounted header and histogram live at the seed cursor. -/
theorem seed_live {steps : List NavigationDirectory.Stage} {e : ℕ} {raw : ℕ→Bool}
    {m out : Memory W} {c0 : NavigationDirectory.Cursor} (s : A.SeedSpace W) (space : A.MountedRange steps e W)
    (L : A.Live steps e raw cur c0 m) (frame : ∀i,A.seedKeep i → out i=m i) :
    A.Live steps e raw cur c0 out := by
  apply Live.seed_frame space L le_rfl _ (fun i hi=>frame i (.inl hi))
  rw [frame _ (.inr (Fin.val_cast_of_lt s.controlRoom))];exact L.pointer

/-- Transport the slot count while retaining the same graph and lane displacements. -/
def reseedDegree {V U : Type*} {d e : ℕ} (degree : d=e) (G : LiftedSlots V d U) : LiftedSlots V e U :=
  Eq.rec (motive := fun j _ => LiftedSlots V j U) G degree

private theorem retarget {v n d e L : ℕ} {U : Type} [AddCommGroup U] {G : LiftedSlots (Fin v) d U}
    {cols : SlotImage.Columns} {lane : U≃Fin L} {mem : ℕ→ℕ} {w : ℕ}
    (degree : d=e) (axes : v=n) (h : SlotImage.Stored G (Equiv.refl _) lane cols mem (fun _=>w)) :
    SlotImage.Stored (reseedDegree degree G) (finCongr axes) lane cols mem (fun _=>w) := by
  subst e;subst n;exact h

theorem stateImage {v n d e L : ℕ} {U : Type} [AddCommGroup U] {G : LiftedSlots (Fin v) d U}
    {cols : SlotImage.Columns} {lane : U≃Fin L} {mem : ℕ→ℕ} {w : ℕ}
    (degree : d=e) (axes : v=n) (h : SlotImage.Stored (reseedDegree degree G) (finCongr axes) lane cols mem (fun _=>w)) :
    SlotImage.Stored G (finCongr (Fintype.card_fin v).symm) lane cols mem (fun _=>w) := by
  subst e;subst n
  refine ⟨?_,fun p b i=>h.graph p b i,fun x=>h.widthWord x⟩
  simpa only [Fintype.card_fin] using h.rowCount

/-- The graph evidence for the five-scan procedure comes directly from the cyclic
cursor's six-column generator and its native constant width scan. -/
theorem cursorImage_of_window {F : Type} [Field F] (P : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k+1)
    (low offsets slots : ℕ) (de : 2^(P.exponent 0)=A.initialDegree) (ax : k+1=A.axes)
    (lanes : A.remainingLanes=2^(k+1)) (m : Memory W) (s : A.RelayWindow W)
    (bits : A.relayWidth<2^W) (axesWord : k+1≤W) :
    SlotImage.Stored (reseedDegree de (P.cursorState hk low offsets slots).graph) (finCongr ax) (tagOrdinal (k+1)) C
      (fun i=>(z m i).val) (fun _=>A.relayWidth) := by
  let r:=P.cursorCopies+1
  have degree : r*2=A.initialDegree := P.cursor_degree.trans de
  have rows : (C).rows=(k+1)*(r*2) := by change A.axes*A.initialDegree=_;rw [ax,degree]
  have gfit:=s.graphBefore.trans_lt (s.columns.2.trans_lt s.controlRoom)
  have raw := InitialRelayWidth.stored (LaneCursor.graph hk r) (Equiv.refl _) (tagOrdinal _) C
    (InitialRelayGraph.image (C).graph (k+1) (r*2) m) A.relayWidth bits rows
    (InitialRelayGraph.image_fields hk C m rows axesWord gfit) (Or.inl s.graphBefore)
  have old : SlotImage.Stored (LaneCursor.graph hk r) (Equiv.refl _) (tagOrdinal _) C
      (fun i=>(z m i).val) (fun _=>A.relayWidth) := by
    unfold InitialRelayBootstrap.image
    simpa only [←ax,←degree,lanes] using raw
  have pre : SlotImage.Stored (P.cursorState hk low offsets slots).graph (Equiv.refl _)
      (tagOrdinal _) C (fun i=>(z m i).val) (fun _=>A.relayWidth) :=
    retarget P.cursor_degree rfl old
  exact retarget de ax pre

theorem cursorImage {F : Type} [Field F] (P : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k+1)
    (low offsets slots : ℕ) (de : 2^(P.exponent 0)=A.initialDegree) (ax : k+1=A.axes)
    (lanes : A.remainingLanes=2^(k+1)) (m : Memory W) (s : A.SeedSpace W)
    (bits : A.relayWidth<2^W) (axesWord : k+1≤W) :
    SlotImage.Stored (reseedDegree de (P.cursorState hk low offsets slots).graph) (finCongr ax) (tagOrdinal (k+1)) C
      (fun i=>(z m i).val) (fun _=>A.relayWidth) :=
  A.cursorImage_of_window P hk low offsets slots de ax lanes m s.window bits axesWord

theorem block_seed_spec {F : Type} [Field F] (P : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k+1)
    (low offsets slots : ℕ) (de : 2^(P.exponent 0)=A.initialDegree) (ax : k+1=A.axes)
    (lanes : A.remainingLanes=2^(k+1)) (relay : A.relayWidth=2^low*(offsets*slots*3))
    (m : Memory W) (s : A.SeedSpace W) (H : Scans.Header cur m A.seed 63 A.seedWords)
    (bits : A.relayWidth<2^W) (axesWord : k+1≤W) (degFits : 2*A.initialDegree<2^W)
    (laneFits : 2^(k+1)<2^W) (wide : 8<2^W) :
    let X:=P.cursorState hk low offsets slots
    A.seedProgram.Spec (fun mem=>mem=m)
      (fun _ out=>A.InitialNodeMetadata (reseedDegree de X.graph) (finCongr ax) (fun _=>A.relayWidth) out ∧
        SlotImage.Stored X.graph X.order (tagOrdinal _) C (fun i=>(out i).val) X.width ∧
        ∀i,A.seedKeep i → out i=m i) A.seedTime := by
  dsimp only
  have native:=A.cursorImage P hk low offsets slots de ax lanes m s bits axesWord
  intro programs registers words machine
  apply Procedure.Spec.mono (A := A.seedProgram)
    (A.seed_spec (finCongr ax) (fun _=>A.relayWidth) m s H lanes
      (by rw [← de]; exact Nat.two_pow_pos _) (by rw [← ax]; exact axesWord)
      degFits laneFits wide native) (fun _ h => h) _ le_rfl machine
  rintro _ out ⟨«meta»,graph,keep⟩
  refine ⟨«meta»,?_,keep⟩
  have original:=stateImage (G:=(P.cursorState hk low offsets slots).graph) de ax graph
  have widths : (P.cursorState hk low offsets slots).width = fun _ => A.relayWidth := by
    funext edge
    rw [P.cursorState_width, relay]
  rw [widths]
  exact original

theorem InitialNodeMetadata.frame {G : LiftedSlots B A.initialDegree (BitWord t)} {base : B≃Fin A.axes}
    {width : SlotImage.Edge B (BitWord t) A.initialDegree→ℕ} {m out : Memory W}
    (h : A.InitialNodeMetadata G base width m) (same : ∀i,A.initialRecords≤ i → out i=m i) :
    A.InitialNodeMetadata G base width out := by
  refine ⟨?_,?_,?_⟩
  · intro r j
    exact (same (A.seedWords 7+(r.val*5+j.val)) (Nat.le_add_right A.initialRecords _)).trans (h.kernel r j)
  · intro r j
    rw [same _ (by change A.initialRecords≤A.initialRecords+5*A.initialSites+_;omega)];exact h.halfHeader r j
  · intro u j col
    rw [same _ (by change A.initialRecords≤A.initialRecords+7*A.initialSites+_;omega)];exact h.half u j col

/-- The literal subsequent three-instruction pointer write changes the live cursor
to the first chronological stage. Every word subscript of the real initial state,
both archives, and all initialized node records remain available. -/
theorem block_seed_start_spec {F : Type} [Field F] (P : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k+1)
    (low offsets slots : ℕ) (de : 2^(P.exponent 0)=A.initialDegree) (ax : k+1=A.axes)
    (lanes : A.remainingLanes=2^(k+1)) (relay : A.relayWidth=2^low*(offsets*slots*3))
    (m : Memory W) (s : A.SeedSpace W) (H : Scans.Header cur m A.seed 63 A.seedWords)
    (bits : A.relayWidth<2^W) (axesWord : k+1≤W) (degFits : 2*A.initialDegree<2^W)
    (laneFits : 2^(k+1)<2^W) (wide : 8<2^W)
    (steps : List NavigationDirectory.Stage) (edges : ℕ) (raw : ℕ→Bool)
    (L : A.Live steps edges raw cur {A.cursor with header:=A.seed} m)
    (space : A.MountedRange steps edges W) (first : A.cursor.header=A.seed+64) :
    let X:=P.cursorState hk low offsets slots
    (A.seedProgram.seq (start cur A.cursor.header)).Spec (fun mem=>mem=m)
      (fun _ out=>A.InitialNodeMetadata (reseedDegree de X.graph) (finCongr ax) (fun _=>A.relayWidth) out ∧
        SlotImage.Stored X.graph X.order (tagOrdinal _) C (fun i=>(out i).val) X.width ∧
        A.Live steps edges raw cur A.cursor out ∧ ∀i,i<(C).graph → out i=m i) (A.seedTime+3) := by
  dsimp only
  intro programs registers words machine
  apply Procedure.Spec.mono (A := A.seedProgram.seq (start cur A.cursor.header))
    (Procedure.Spec.seq (A := A.seedProgram) (B := start cur A.cursor.header)
      (A.block_seed_spec P hk low offsets slots de ax lanes relay m s H bits axesWord degFits laneFits wide)
      (NavigationPass.start_spec cur (A.cursor.header:Word W)) (fun _ _ _ => trivial))
    (fun _ h => h) _ le_rfl machine
  rintro _ out ⟨mid,⟨«meta»,img,frame⟩,rfl⟩
  let result:=writeMemory mid cur (A.cursor.header:Word W)
  have cell : (cur).val=A.control := Fin.val_cast_of_lt s.controlRoom
  have same (i : ℕ) (h : i≠A.control) : result i=mid i := by simp [result,writeMemory,cell,h]
  have low (i : ℕ) (h : i<(C).graph) : result i=m i := by
    rw [same i (ne_of_lt (h.trans_le ((seedWindow s).1.trans (seedWindow s).2)))]
    exact frame i (.inl h)
  have newHead : (result (cur).val).val=A.cursor.header := by
    have headFit : A.cursor.header < 2^W := by
      rw [first]
      exact s.seedBefore.trans_lt (((seedWindow s).1.trans (seedWindow s).2).trans_lt s.controlRoom)
    simp only [result, writeMemory, eq_self, ite_true, Fin.val_cast_of_lt headFit]
  have graphHigh := s.graphBefore.trans (seedWindow s).2
  have widthHigh : (C).widths+(C).rows*2^(k+1)≤A.control := by simpa only [lanes] using s.widthsBefore
  refine ⟨InitialNodeMetadata.frame A «meta» (fun i hi=>same i (ne_of_gt (s.controlsBefore.trans_le hi))),?_,?_,low⟩
  · apply img.frame
    · intro i _ hi
      exact congrArg Fin.val (same i (ne_of_lt (hi.trans_le graphHigh)))
    · intro i _ hi
      rw [←img.rowCount] at hi
      exact congrArg Fin.val (same i (ne_of_lt (hi.trans_le widthHigh)))
  · exact Live.seed_frame space L (by change A.seed≤A.cursor.header;rw [first];omega) newHead low


end
end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
