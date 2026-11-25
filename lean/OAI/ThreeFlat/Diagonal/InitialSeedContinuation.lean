import OAI.ThreeFlat.Diagonal.SeedNodeRows
import OAI.ThreeFlat.Diagonal.CursorSeedSites
import OAI.ThreeFlat.Diagonal.InitialSeedMount
import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.Diagonal.PhysicalIndividualCharge

namespace OAI
/-! # Real archive mounting and all native starts preceding the chronological loop -/
namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalProcedure
open CompressorPacking.Native
open scoped Classical Fin.CommRing
noncomputable section
variable {W : ℕ} (A : Archive) (ss : List NavigationDirectory.Stage) (edges : ℕ)
local notation "cur" => (A.control:Word W)
local notation "ctr" => ((A.control+3:ℕ):Word W)
set_option quotPrecheck false in
local notation "C" => (⟨A.cursor.graph,A.axes*A.initialDegree,A.cursor.width⟩ : SlotImage.Columns)
local notation "R" => A.axes*A.initialDegree
local notation "IB" => InitialRelayBootstrap.procedure cur C A.axes A.initialDegree A.relayWidth
local notation "relay" => InitialRelayBootstrap.image C A.axes A.initialDegree A.remainingLanes A.relayWidth

def seedThen (blocks : ℕ) (tail : Procedure W) : Procedure W :=
  (A.boot ss edges).seq ((IB).seq (A.initialMetadata.seq ((start cur A.cursor.header).seq ((start ctr blocks).seq tail))))

def startedMemory (library : List ℕ) (raw : ℕ→Bool) (input : Memory W) (blocks : ℕ) : Memory W :=
  let mount:=A.mountedMemory ss edges library raw input
  let data:=A.metadataMemory (relay mount)
  writeMemory (writeMemory data cur (A.cursor.header:Word W)) ctr (blocks:Word W)

variable {F : Type} [Field F] (P : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k+1) (low off slots : ℕ)
local notation "X" => P.cursorState hk low off slots

structure SeedReady (de : 2^(P.exponent 0)=A.initialDegree) (ax : k+1=A.axes)
    (raw : ℕ→Bool) (blocks : ℕ) (input out : Memory W) : Prop where
  nodes : A.InitialNodeMetadata (reseedDegree de (X).graph) (finCongr ax) (fun _=>A.relayWidth) out
  slots : SlotImage.Stored (X).graph (X).order (tagOrdinal _) C (fun i=>(out i).val) (X).width
  live : A.Live ss edges raw cur A.cursor out
  counter : (out (ctr).val).val=blocks
  low : ∀i,i<A.seed→ out i=input i

theorem started_ready (de : 2^(P.exponent 0)=A.initialDegree) (ax : k+1=A.axes)
    (lanes : A.remainingLanes=2^(k+1)) (wire : A.relayWidth=2^low*(off*slots*3))
    (library suffix : List ℕ) (raw : ℕ→Bool) (input : Memory W) (blocks : ℕ) (s : A.SeedSpace W)
    (banks : A.MountedRange ss edges W) (src : A.SeedSources ss edges library suffix raw input)
    (bits : A.relayWidth<2^W) (axesWord : k+1≤W) (degreeWord : 2*A.initialDegree<2^W)
    (laneWord : 2^(k+1)<2^W) (wide : 8<2^W) (first : A.cursor.header=A.seed+64)
    (counterRoom : A.control+3<A.initialRecords) (countFit : blocks<2^W) :
    A.SeedReady ss edges P hk low off slots de ax raw blocks input (A.startedMemory ss edges library raw input blocks) := by
  let m0:=A.mountedMemory ss edges library raw input
  let m1:=relay m0
  let m2:=A.metadataMemory m1
  let out:=A.startedMemory ss edges library raw input blocks
  have mounted:=src.mounted s banks
  have H:=s.relay_header mounted.1
  have gr : (C).graph+6*(C).rows≤A.control := s.graphBefore.trans ((Nat.le_add_right ..).trans s.widthsBefore)
  have below : (C).graph≤A.control := (Nat.le_add_right ..).trans gr
  have wr : (C).widths+(C).rows*2^(k+1)≤A.control := by simpa only [lanes] using s.widthsBefore
  have typed:=A.cursorImage P hk low off slots de ax lanes m0 s bits axesWord
  have rows:= A.metadata_actual (reseedDegree de (X).graph) (finCongr ax) (fun _=>A.relayWidth) m1 s.toMetadataSpace H typed
    lanes (gr.trans s.controlsBefore.le) (wr.trans s.controlsBefore.le) degreeWord laneWord wide
  have physical : SlotImage.Stored (X).graph (X).order (tagOrdinal _) C (fun i=>(m2 i).val) (X).width := by
    have eqWidth : (X).width = (fun _ => A.relayWidth) := by
      funext j
      rw [P.cursorState_width,wire]
    rw [eqWidth]
    exact stateImage (G := (X).graph) de ax rows.2
  have keep:= A.metadata_frame m1 s.toMetadataSpace H
  have cf : A.control+3<2^W := counterRoom.trans_le ((Nat.le_add_right ..).trans s.endFit.le)
  have current : (cur).val=A.control := Fin.val_cast_of_lt s.controlRoom
  have countCell : (ctr).val=A.control+3 := Fin.val_cast_of_lt cf
  have headFit : A.cursor.header<2^W := by rw [first];exact (s.seedBefore.trans below).trans_lt s.controlRoom
  have same (i : ℕ) (avoid : i<A.control ∨ A.control+3< i) : out i=m2 i := by
    change (if i=(ctr).val then (blocks : Word W) else
      if i=(cur).val then (A.cursor.header : Word W) else m2 i)=m2 i
    rw [current,countCell,ite_eq_right (by omega : i≠A.control+3),ite_eq_right (by omega : i≠A.control)]
  have lowFrame (i : ℕ) (h : i<(C).graph) : out i=m0 i :=
    (same i (.inl (h.trans_le below))).trans ((keep i (.inl ((h.trans_le below).trans s.controlsBefore))).trans
      (s.relay_frame m0 i (.inl h)))
  have head : (out (cur).val).val=A.cursor.header := by
    change (if (cur).val=(ctr).val then (blocks : Word W) else
      if (cur).val=(cur).val then (A.cursor.header : Word W) else m2 (cur).val).val=A.cursor.header
    rw [current,countCell,ite_eq_right (by omega : A.control≠A.control+3),ite_eq_left rfl,Fin.val_cast_of_lt headFit]
  refine ⟨InitialNodeMetadata.frame A rows.1 (fun i h=>same i (.inr (counterRoom.trans_le h))),?_,?_,?_,?_⟩
  · apply physical.frame
    · intro i _ hi;exact congrArg Fin.val (same i (.inl (hi.trans_le gr)))
    · intro i _ hi;rw [←physical.rowCount] at hi;exact congrArg Fin.val (same i (.inl (hi.trans_le wr)))
  · exact Live.seed_frame banks mounted.2 (by change A.seed≤A.cursor.header;rw [first];omega) head lowFrame
  · change (if (ctr).val=(ctr).val then (blocks : Word W) else
      writeMemory m2 (cur) (A.cursor.header : Word W) (ctr).val).val=blocks
    rw [ite_eq_left rfl,Fin.val_cast_of_lt countFit]
  · intro i hi
    exact (lowFrame i (hi.trans_le ((Nat.le_add_right ..).trans s.seedBefore))).trans (src.before s i hi)

variable {A ss edges}

/-- Specialization of an exact deterministic memory transition to a fixed input.
The actual executed program and its bound are retained. -/
private theorem fixedInput {p : Procedure W} {pre : Memory W→Prop} {f : Memory W→Memory W} {n : ℕ}
    (run : p.Spec pre (fun m out=>out=f m) n) {m : Memory W} (take : pre m) :
    p.Spec (fun input=>input=m) (fun _ out=>out=f m) n := by
  intro n r k M pc reg pub exit inst rom c input entry same
  subst input
  exact run M pc reg pub exit inst rom c m entry take

/-- This association is the literal one in `NavigationPass.active`. The time of an
arbitrary continuation is added to the mounted prefix's measured bounded cost. -/
theorem boot_seed_continue (de : 2^(P.exponent 0)=A.initialDegree) (ax : k+1=A.axes)
    (lanes : A.remainingLanes=2^(k+1)) (wire : A.relayWidth=2^low*(off*slots*3))
    (library suffix : List ℕ) (raw : ℕ→Bool) (input : Memory W) (blocks : ℕ) (s : A.SeedSpace W)
    (banks : A.MountedRange ss edges W) (src : A.SeedSources ss edges library suffix raw input)
    (bits : A.relayWidth<2^W) (axesWord : k+1≤W) (degreeWord : 2*A.initialDegree<2^W)
    (laneWord : 2^(k+1)<2^W) (wide : 8<2^W) (first : A.cursor.header=A.seed+64)
    (counterRoom : A.control+3<A.initialRecords) (countFit : blocks<2^W)
    (tail : Procedure W) (post : Memory W→Prop) (time : ℕ)
    (finish : ∀m,A.SeedReady ss edges P hk low off slots de ax raw blocks input m →
      tail.Spec (fun z=>z=m) (fun _ out=>post out) time) :
    (A.seedThen ss edges blocks tail).Spec (fun m=>m=input) (fun _ out=>post out)
      (A.bootTime ss edges W+A.seedTime+6+time) := by
  let m0:=A.mountedMemory ss edges library raw input
  let m1:=relay m0
  let m2:=A.metadataMemory m1
  let m3:=writeMemory m2 cur (A.cursor.header:Word W)
  let m4:=A.startedMemory ss edges library raw input blocks
  have data:=A.started_ready ss edges P hk low off slots de ax lanes wire library suffix raw input blocks s banks src
    bits axesWord degreeWord laneWord wide first counterRoom countFit
  have a : (A.boot ss edges).Spec (·=input) (fun _ out=>out=m0) (A.bootTime ss edges W) :=
    src.boot (s:=s) banks
  have mounted:=src.mounted s banks
  have graphTop : (C).graph+6*R<2^W :=
    (s.graphBefore.trans ((Nat.le_add_right ..).trans s.widthsBefore)).trans_lt s.controlRoom
  have degree : 0<A.initialDegree := de ▸ Nat.two_pow_pos _
  have b : (IB).Spec (·=m0) (fun _ out=>out=m1)
      (InitialRelayBootstrap.budget W C A.axes A.initialDegree A.remainingLanes) := by
    intro programCount registerCount wordCount machine
    exact fixedInput (m:=m0) (InitialRelayBootstrap.spec cur C A.axes A.initialDegree A.remainingLanes A.relayWidth
      graphTop (s.widthsBefore.trans_lt s.controlRoom) degree (ax ▸ axesWord) (by omega))
      (s.loaded mounted.1) machine
  have c : (A.initialMetadata : Procedure W).Spec (fun z=>z=m1) (fun _ out=>out=m2)
      (33+A.metadataUnit*A.initialSites) := by
    intro programCount registerCount wordCount machine
    exact Procedure.Spec.mono (A:=A.initialMetadata)
      (A.metadata_spec m1 s.toMetadataSpace (s.relay_header mounted.1))
      (fun _ h=>h) (fun _ _ h=>h.1) le_rfl machine
  have f : (start cur (A.cursor.header:Word W)).Spec (·=m2) (fun _ out=>out=m3) 3 := by
    intro programCount registerCount wordCount machine
    exact fixedInput (m:=m2) (start_spec cur (A.cursor.header:Word W)) trivial machine
  have g : (start ctr (blocks:Word W)).Spec (·=m3) (fun _ out=>out=m4) 3 := by
    intro programCount registerCount wordCount machine
    exact fixedInput (m:=m3) (start_spec ctr (blocks:Word W)) trivial machine
  have before (left right : Procedure W) (fromMem nextMem : Memory W) {leftTime rightTime : ℕ}
      (runLeft : left.Spec (·=fromMem) (fun _ out => out=nextMem) leftTime)
      (runRight : right.Spec (·=nextMem) (fun _ out => post out) rightTime) :
      (left.seq right).Spec (·=fromMem) (fun _ out => post out) (leftTime+rightTime) := by
    intro pc regs slots machine
    exact Procedure.Spec.mono (A := left.seq right)
      (post := fun _ out => ∃ mid : Memory W, mid=nextMem ∧ post out)
      (Procedure.Spec.seq (A := left) (B := right) runLeft runRight (fun _ _ h => h))
      (fun _ h => h) (fun _ _ reached => reached.choose_spec.2) le_rfl machine
  let counter := start ctr (blocks : Word W)
  let pointer := start cur (A.cursor.header : Word W)
  let starts := pointer.seq (counter.seq tail)
  let afterRelay := (A.initialMetadata : Procedure W).seq starts
  have cost : A.bootTime ss edges W +
      (InitialRelayBootstrap.budget W C A.axes A.initialDegree A.remainingLanes +
        ((33+A.metadataUnit*A.initialSites)+(3+(3+time)))) = A.bootTime ss edges W+A.seedTime+6+time := by
    rw [InitialRelayBootstrap.budget_eq,A.metadataUnit_eq,seedTime]
    omega
  rw [←cost]
  intro pc regs slots machine
  exact before (A.boot ss edges) ((IB).seq afterRelay) input m0 a
    (before (IB) afterRelay m0 m1 b
      (before A.initialMetadata starts m1 m2 c
        (before pointer (counter.seq tail) m2 m3 f
          (before counter tail m3 m4 g (finish m4 data))))) machine


end
end ThreeFlat.Diagonal.NavigationPass.Archive

namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM RAM.NavigationNodeRows PhysicalStage
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] (A : Archive) (B : PhysicalStage.Block F)
  {k : ℕ} (hk : 2≤k) (low off slots : ℕ)

/-- The two columns are the actual tariff-scaled seed work and the number of
external pairs at that cursor. The scheduler uses the original row ordinal for
the clipped tail, including empty intervals past the last paired input. -/
theorem cursor_seedRows (ax : k=A.axes) (lanes : A.remainingLanes=2^k)
    (degree : 2^(B.exponent 0)=A.initialDegree) (wire : A.relayWidth=2^low*(off*slots*3))
    (b : Banks) (total copies depth stride cells : ℕ)
    (bankLanes : b.lanes=2^k) (perLane : b.perLanePairs=2^low) (allPairs : b.totalPairs=total)
    (trace : b.traceWork=TraceBitHeader.seedTraceWork low stride cells copies depth) :
    State.SeedRows (A.cursorSeedSites B hk low off slots ax lanes) A.seedData b
      (B.seedWork hk low off slots total copies depth stride cells) (B.clippedPairs hk low off slots total) := by
  intro prior v col
  let r := (A.cursorSeedSites B hk low off slots ax lanes).ord v
  change A.seedData.cost b prior r col=_
  have row : r.val=B.cursorOrdinal hk low off slots v.1 v.2 := A.cursorSeedSites_ord B hk low off slots ax lanes v
  have sumWidth : (A.seedData.halfWidth r).sum=(B.cursorState hk low off slots).incidentWidth v := by
    change (List.replicate (2*A.initialDegree) A.relayWidth).sum=_
    simp only [List.sum_replicate,nsmul_eq_mul,State.incidentWidth,B.cursorState_width,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,degree,wire,Nat.cast_id]
    ring
  have empty : (∑ i, prior (A.seedData.child r i) col)=0 := by
    change (∑ i : Fin 0, prior (A.seedData.child r i) col)=0
    simp
  by_cases leaf : B.cursorOrdinal hk low off slots v.1 v.2<2^k <;>
    by_cases z : col.val=0 <;>
    simp [LayerData.cost,show A.seedLayer.kind=0 from rfl,empty,row,sumWidth,bankLanes,allPairs,
      perLane,trace,PhysicalStage.Block.seedWork,PhysicalStage.Block.clippedPairs,leaf,z,Nat.add_assoc]


end
end ThreeFlat.Diagonal.NavigationPass.Archive

namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows PhysicalStage CompressorPacking.Native
open CompressorPacking.Native.ShrinkStage.Halves
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W k : ℕ} (A : Archive) (B : Block F) (hk : 2≤k) (low off cells : ℕ)
local notation "d" => (2^(B.exponent 0):ℕ)
local notation "X" => B.cursorState hk low off cells

private theorem seed_half_at_degree {n l : ℕ} {U : Type}
    (graph : Computability.VPVNP.Compression.LiftedSlots U n (Computability.VPVNP.Compression.BitWord l))
    (number : U ≃ Fin A.axes) (degree : A.initialDegree=n) (m : Memory W)
    (stored : A.InitialNodeMetadata
      (cast (congrArg (fun a => Computability.VPVNP.Compression.LiftedSlots U a (Computability.VPVNP.Compression.BitWord l))
        degree.symm) graph) number (fun _=>A.relayWidth) m)
    (v : U × Computability.VPVNP.Compression.BitWord l) (i : Fin (2*n)) (col : Fin 4) :
    m (A.seedWords 11+((siteNumber number v*(2*n)+i.val)*4+col.val)) =
      ((![edgeNumber number (sourceHalf graph v i),if i.val<n then 0 else 1,A.relayWidth,
        prefixValue graph (fun _=>A.relayWidth) v i] : Fin 4→ℕ) col : Word W) := by
  subst n
  exact stored.half v i col

/-- The original cursor seed contains all four graph-half fields at the real
S49 row addresses, in precisely the same numbering used by the selected roots. -/
theorem InitialNodeMetadata.cursorHalfRows (ax : k=A.axes) (lanes : A.remainingLanes=2^k)
    (deg : A.initialDegree=d) (relay : A.relayWidth=2^low*(off*cells*3)) (m : Memory W)
    («meta» : A.InitialNodeMetadata
      (cast (congrArg (fun a => Computability.VPVNP.Compression.LiftedSlots (Fin k) a (Computability.VPVNP.Compression.BitWord k))
        deg.symm) (X).graph) (finCongr ax) (fun _=>A.relayWidth) m)
    (endFit : A.metadataEnd<2^W) (degreeWord : 2*d<2^W)
    (edgeWord : (X).edgeCount≤2^W) (wireWord : A.relayWidth<2^W) (sumWord : 2*d*A.relayWidth<2^W) :
    State.HalfRows (A.cursorSeedSites B hk low off cells ax lanes)
      (fun i=>A.initialRecords≤ i ∧ i<A.metadataEnd) (fun i=>(m i).val) := by
  let O:=A.cursorSeedSites B hk low off cells ax lanes
  let num:=finCongr ax
  let atSite (v : (X).Site):=O.ord v
  let rowStart (v : (X).Site):=A.seedWords 11+8*d*(atSite v).val
  have rank (v : (X).Site) : siteNumber num ((X).chart.symm v)=(atSite v).val :=
    (A.seedRowEquiv_val num lanes v).symm
  have early (v : (X).Site) : rowStart v<2^W := by
    have site : (atSite v).val≤A.initialSites := (atSite v).isLt.le
    have next:=Nat.mul_le_mul_left (8*d) site
    change A.initialRecords+(7+8*A.initialDegree)*A.initialSites<2^W at endFit
    change A.initialRecords+7*A.initialSites+8*d*(atSite v).val<_
    rw [deg,Nat.add_mul] at endFit
    omega
  have ptr (v : (X).Site) : (m (O.layer.incident+(O.ord v).val*2+1)).val=rowStart v := by
    have eq:=congrArg Fin.val («meta».halfHeader (atSite v) 1)
    change (m (A.seedWords 9+((atSite v).val*2+1))).val=
      (((A.seedWords 11+8*A.initialDegree*(atSite v).val : ℕ):Word W)).val at eq
    rw [deg] at eq
    change (m (A.seedWords 9+((atSite v).val*2+1))).val=((rowStart v:Word W)).val at eq
    change (m (A.seedWords 9+(atSite v).val*2+1)).val=rowStart v
    simpa only [Nat.add_assoc,Fin.val_cast_of_lt (early v)] using eq
  have fields (v : (X).Site) (i : Fin (2*d)) (col : Fin 4) :
      m (rowStart v+4*i.val+col.val)=
        ((![edgeNumber num (sourceHalf (X).graph ((X).chart.symm v) i),if i.val<d then 0 else 1,
          A.relayWidth,prefixValue (X).graph (fun _=>A.relayWidth) ((X).chart.symm v) i] : Fin 4→ℕ) col:Word W) := by
    have eq:=seed_half_at_degree A (X).graph num deg m «meta» ((X).chart.symm v) i col
    have addr : rowStart v+4*i.val+col.val=A.seedWords 11+(((atSite v).val*(2*d)+i.val)*4+col.val) := by
      dsimp only [rowStart];ring
    exact (congrArg m (addr.trans (congrArg (fun x : ℕ => A.seedWords 11+((x*(2*d)+i.val)*4+col.val))
      (rank v).symm))).trans eq
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro v
    have eq:=congrArg Fin.val («meta».halfHeader (atSite v) 0)
    change (m (A.seedWords 9+((atSite v).val*2+0))).val=(((2*A.initialDegree:ℕ):Word W)).val at eq
    rw [deg] at eq
    change (m (A.seedWords 9+(atSite v).val*2)).val=2*d
    simpa only [Nat.add_zero,Fin.val_cast_of_lt degreeWord] using eq
  · intro v i
    rw [ptr]
    let e:=sourceHalf (X).graph ((X).chart.symm v) i
    have eq:=congrArg Fin.val (fields v i 0)
    have id (a : (X).shape.Edge) : edgeNumber num a=((X).wireOrder a).val := by
      obtain ⟨⟨z,j⟩,w⟩:=a
      exact ((X).wireOrder_val z j w).symm
    have fit : edgeNumber num e<2^W := (id e).trans_lt (((X).wireOrder e).isLt.trans_le edgeWord)
    change (m (rowStart v+4*i.val+0)).val=((edgeNumber num e:Word W)).val at eq
    have same : edgeNumber num e=edgeNumber (X).order e := by rfl
    exact (by simpa only [Nat.add_zero] using eq :
      (m (rowStart v+4*i.val)).val=((edgeNumber num e:Word W)).val).trans
      ((Fin.val_cast_of_lt fit).trans same)
  · intro v i
    rw [ptr]
    have eq:=congrArg Fin.val (fields v i 2)
    change (m (rowStart v+4*i.val+2)).val=((A.relayWidth:Word W)).val at eq
    rw [Fin.val_cast_of_lt wireWord,relay] at eq
    exact eq
  · intro v i
    rw [ptr]
    let f:=prefixValue (X).graph (fun _=>A.relayWidth) ((X).chart.symm v) i
    have small : f≤(∑ _ : Fin (2*d),A.relayWidth) := by
      exact Finset.sum_le_sum fun j _=>by dsimp;split <;> omega
    have fFit : f<2^W := (by simpa [Nat.mul_comm] using small : f≤2*d*A.relayWidth).trans_lt sumWord
    have eq:=congrArg Fin.val (fields v i 3)
    change (m (rowStart v+4*i.val+3)).val=((f:Word W)).val at eq
    rw [Fin.val_cast_of_lt fFit] at eq
    have width : (X).width=(fun _=>A.relayWidth) := by
      funext j
      exact (B.cursorState_width hk low off cells j).trans relay.symm
    rw [width]
    exact eq
  · intro v j
    have h:= (atSite v).isLt
    have hj:=j.isLt
    change (atSite v).val<A.initialSites at h
    change A.initialRecords≤A.initialRecords+5*A.initialSites+(atSite v).val*2+j.val ∧
      A.initialRecords+5*A.initialSites+(atSite v).val*2+j.val<A.initialRecords+(7+8*A.initialDegree)*A.initialSites
    rw [Nat.add_mul];omega
  · intro v i j
    rw [ptr]
    have h:=(atSite v).isLt
    change (atSite v).val<A.initialSites at h
    have big:=Nat.mul_le_mul_left (8*d) h
    have lim:=i.isLt
    have hj:=j.isLt
    change A.initialRecords≤A.initialRecords+7*A.initialSites+8*d*(atSite v).val+4*i.val+j.val ∧
      A.initialRecords+7*A.initialSites+8*d*(atSite v).val+4*i.val+j.val<A.initialRecords+(7+8*A.initialDegree)*A.initialSites
    rw [Nat.mul_succ] at big
    rw [deg,Nat.add_mul]
    omega


end
end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
