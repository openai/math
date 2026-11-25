import OAI.ThreeFlat.Diagonal.TraceEndpointInterval
import OAI.ThreeFlat.Diagonal.SchedulingBounds
import OAI.ThreeFlat.Diagonal.InitialSeedVisit
import OAI.ThreeFlat.Diagonal.PhysicalNodeArchiveBounds
import OAI.ThreeFlat.Diagonal.NavigationTraversal
import OAI.ThreeFlat.Diagonal.TraceVolumePins
import OAI.ThreeFlat.Diagonal.TickScheduledInput
import OAI.ThreeFlat.RAM.TickScanHydration
import OAI.ThreeFlat.Diagonal.PhysicalIndividualCharge
import OAI.ThreeFlat.Diagonal.NavigationRootBranches
import OAI.ThreeFlat.RAM.HistoryBucketPack
import OAI.ThreeFlat.RAM.TerminalWireArchive

namespace OAI
set_option maxErrors 600

/-! # Publishing the chronological root charges and packed group intervals in the native tick -/

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive

open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open HistoryContraction RAM.PhysicalPinsExpr RAM.DescriptorExpr
open scoped BigOperators Fin.CommRing

variable {W : ℕ}

section ActualPhysicalRun

open PhysicalStage
open scoped Classical
variable {F : Type} [Field F] {d l : ℕ} {A : State d l}
variable (a : RootArchive) (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O)

noncomputable def runRootSite (card : a.rootCount=(r.finalArchive h C O p).1.count) (i : Fin a.rootCount) :
    (r.plan.finish h).Site :=
  r.finalSite h ((r.finalArchive h C O p).2.symm (finCongr card i))

variable (m : Memory W) (rows : r.ArchiveRowsStored a.nodeBank (fun u => (m u).val) h C O p)
    (zero : O.layer.first=0) (first : a.firstFinal=(r.finalArchive h C O p).1.first)
    (card : a.rootCount=(r.finalArchive h C O p).1.count)
    (start pairs : A.Site→ℕ)

/-- S43 carries the scaled node cost and the inherited clipped-pair mass. S44 stores
the consecutive parent IDs from the same physical branch. -/
noncomputable def nodesOfRun : Nodes a where
  chronology := r.archiveDirectory h C O p a.nodeBank (fun z => (m z).val) rows zero
    a.firstFinal a.rootCount first card
  first := rfl
  work i := a.nodeBank.unitWork*r.chargeAt h C start (runRootSite a r h C O p card i)
  pairs i := ∑ x : {x // r.plan.destination h x=runRootSite a r h C O p card i}, pairs x.val

theorem nodesOfRun_stored (seed : O.Charged a.nodeBank (fun u => (m u).val) start pairs) :
    (nodesOfRun a r h C O p m rows zero first card start pairs).Stored m := by
  constructor
  · intro i
    let v := runRootSite a r h C O p card i
    let last := r.finalArchive h C O p
    have id : last.1.first+(last.2 ((r.finalSite h).symm v)).val = a.firstFinal+i.val := by
      dsimp only [last,v,runRootSite]
      simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,← first]; rfl
    have truth := r.archive_charges h C O p a.nodeBank (fun u => (m u).val) rows start pairs seed v
    change PhysicalStage.archiveColumn a.nodeBank (fun u => (m u).val) _ 0 = _ ∧
      PhysicalStage.archiveColumn a.nodeBank (fun u => (m u).val) _ 1 = _ at truth
    rw [id] at truth
    have up (z : Word W) (k : ℕ) (hk : z.val=k) : z=(k:Word W) :=
      (Fin.cast_val_eq_self z).symm.trans (congrArg (fun x : ℕ => (x:Word W)) hk)
    constructor
    · exact up _ _ truth.1
    · exact up _ _ truth.2
  · intro i hi
    have hv := r.archiveDirectory_parent h C O p a.nodeBank (fun z => (m z).val) rows zero
      a.firstFinal a.rootCount first card i hi
    exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun z : ℕ => (z:Word W)) hv.symm)

theorem nodesOfRun_root (x : A.Site) (i : Fin (a.firstFinal+a.rootCount)) (initial : i.val=O.id x) :
    (nodesOfRun a r h C O p m rows zero first card start pairs).chronology.root i =
      ((r.finalArchive h C O p).2 ((r.finalSite h).symm (r.plan.destination h x))).val := by
  rw [←r.finalSite_rawDestination h x,Equiv.symm_apply_apply]
  apply Run.root_of_archive _ a.nodeBank (fun z => (m z).val) _ r h C O p rows first x i initial
  exact r.archiveDirectory_parent h C O p a.nodeBank (fun z => (m z).val) rows zero
    a.firstFinal a.rootCount first card

end ActualPhysicalRun



open RAM.HistoryRowLoop

def sources (a : RootArchive) (m : Memory W) :=
  ∀ i : Fin a.initialLanes,m (a.sourceRows+3*i.val)=((4*i.val:ℕ):Word W) ∧
    m (a.sourceRows+3*i.val+1)=(clipped a i.val:Word W) ∧
    m (a.sourceRows+3*i.val+2)=(clipped a (i.val+1):Word W)

def packedRows (a : RootArchive) (groups : Fin a.initialLanes→Fin a.groups) :=
  BucketRows.pack groups (fun _=>0) (List.ofFn a.lane)

def packedRow (a : RootArchive) (groups : Fin a.initialLanes→Fin a.groups)
    (i : Fin a.initialLanes) : BucketRow (Fin a.groups) :=
  (packedRows a groups)[i.val]'(by simpa only [packedRows,BucketRows.pack_length,List.length_ofFn] using i.isLt)

theorem packed_rows (a : RootArchive) (groups : Fin a.initialLanes→Fin a.groups) :
    a.packedRows groups=List.ofFn (a.packedRow groups) := by
  apply List.ext_getElem
  · simp [packedRows,BucketRows.pack_length]
  · intro i hi hi'
    simp [packedRow]

def bucketData (a : RootArchive) (z : ℕ) : Word W :=
  let t:=z-a.sourceRows
  let i:=t/3
  if t%3=0 then ((4*i:ℕ):Word W)
  else if t%3=1 then (clipped a i:Word W) else (clipped a (i+1):Word W)

def groupData (a : RootArchive) (groups : Fin a.initialLanes→Fin a.groups) (z : ℕ) : Word W :=
  let t:=z-a.groupRows
  if h : t/4<a.initialLanes then if t%4=0 then ((groups ⟨t/4,h⟩).val:Word W) else 0 else 0

private theorem bucket_read (a : RootArchive) (m : Memory W) (i : ℕ) (hi : i<3*a.initialLanes)
    (room : a.sourceRows+3*a.initialLanes<2^W) (small : 4<2^W)
    (outFit : TickWorkspace.base a.age 5+4*a.initialLanes<2^W)
    (mulFit : a.initialLanes*a.pairsPerLane<2^W) (pairsFit : a.totalPairs<2^W) :
    (HeaderScan.closed a.bucket : Term W 0 1).eval Fin.elim0 m (fun _=>((a.sourceRows+i:ℕ):Word W))=
      a.bucketData (a.sourceRows+i) := by
  have h1 : (i/3+1)*a.pairsPerLane<2^W :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (show i/3+1≤a.initialLanes by omega)) mulFit
  have h0 : i/3*a.pairsPerLane<2^W :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (show i/3≤a.initialLanes by omega)) mulFit
  have scaleFit : a.pairsPerLane<2^W :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.succ_pos (i / 3))) h1
  have fourFit : 4*(i/3)<2^W := by omega
  have arith : a.sourceRows+i-a.sourceRows=i := by omega
  have res : i%3<3 := Nat.mod_lt _ (by decide)
  rw [readNatural]
  · have sel (x y : ℕ) : (if x<y then x else y)=min x y := by split <;> omega
    rcases (show i%3=0 ∨ i%3=1 ∨ i%3=2 by omega) with h|h|h <;>
      simp [bucket,pick,List.zipIdx,Formula.natural,MotifRows.plus,natOp,natTest,bucketData,
        clipped,arith,h,sel]
  · have registerFits : a.sourceRows+i<2^W := by omega
    have sourceFits : a.sourceRows<2^W := by omega
    have offsetFits : i<2^W := by omega
    have modFits : i%3<2^W := by omega
    have constantFits (v : ℕ) (hv : v≤4) : v<2^W := hv.trans_lt small
    rcases (show i%3=0 ∨ i%3=1 ∨ i%3=2 by omega) with digit|digit|digit <;>
      simp [bucket,pick,List.zipIdx,Formula.Fits,Formula.natural,MotifRows.plus,natOp,opFits,
        natTest,arith,digit,registerFits,sourceFits,offsetFits,h0,h1,pairsFit,
        constantFits 0 (by decide),constantFits 1 (by decide),constantFits 2 (by decide),
        constantFits 3 (by decide)]

private theorem group_read (a : RootArchive) (m : Memory W)
    (root : Fin a.initialLanes→Fin a.rootCount) (assign : Fin a.rootCount→Fin a.groups)
    (cache : ∀ i : Fin a.initialLanes,m (a.rootCache+i.val)=((root i).val:Word W))
    (owners : ∀ r : Fin a.rootCount,m (directory a.age 1+2*r.val)=((assign r).val:Word W))
    (i : ℕ) (hi : i<4*a.initialLanes) (room : a.groupRows+4*a.initialLanes<2^W)
    (bound : a.rootCache+a.initialLanes≤2^W) (ownerRoom : directory a.age 1+2*a.rootCount≤2^W)
    (small : 4<2^W) (_count : a.rootCount<2^W) :
    (HeaderScan.closed a.groupRow : Term W 0 1).eval Fin.elim0 m (fun _=>((a.groupRows+i:ℕ):Word W))=
      a.groupData (assign ∘ root) (a.groupRows+i) := by
  let j : Fin a.initialLanes:=⟨i/4,by omega⟩
  have hr:= (root j).isLt
  have rc : (m (a.rootCache+i/4)).val=(root j).val := by
    rw [cache j,Fin.val_cast_of_lt (by omega)]
  have ra : m (directory a.age 1+(2*(root j).val))=((assign (root j)).val:Word W) := owners _
  have arith : a.groupRows+i-a.groupRows=i := by omega
  have fit : a.groupRow.Fits W (fun _=>0) (fun z=>(m z).val) (fun _=>a.groupRows+i) := by
    simp [groupRow,Formula.Fits,Formula.natural,ix,MotifRows.plus,natOp,natTest,opFits,arith,rc,
      Nat.mul_comm (root j).val 2]; omega
  rw [readNatural _ _ _ fit]
  by_cases h : i%4=0 <;>
    simp [groupRow,Formula.natural,ix,MotifRows.plus,natOp,natTest,groupData,arith,rc,h,j.isLt,
      Function.comp_apply,
      Nat.mul_comm (root j).val 2,ra,j]; apply Fin.ext; simp

def outputAfter (a : RootArchive) (groups : Fin a.initialLanes→Fin a.groups) (m : Memory W) :=
  fillSegment (TickWorkspace.base a.age 7) a.chunkBits (fun _=>0)
    (fillSegment (TickWorkspace.base a.age 8) a.groups (fun _=>0)
      (fillSegment a.groupRows (4*a.initialLanes) (a.groupData groups)
        (fillSegment a.sourceRows (3*a.initialLanes) a.bucketData m)))

structure PackRoom (a : RootArchive) (W : ℕ) : Prop where
  headers : a.header+22<2^W
  output : TickWorkspace.base a.age 5+4*a.initialLanes<2^W
  source : a.sourceRows+3*a.initialLanes<2^W
  groups : a.groupRows+4*a.initialLanes≤2^W
  counters : TickWorkspace.base a.age 8+a.groups≤2^W
  outBeforeCounters : TickWorkspace.base a.age 5+4*a.initialLanes≤TickWorkspace.base a.age 8
  countBeforeSource : TickWorkspace.base a.age 8+a.groups≤a.sourceRows
  countBeforeGroups : TickWorkspace.base a.age 8+a.groups≤a.groupRows

def packedPost (a : RootArchive) (groups : Fin a.initialLanes→Fin a.groups) (m out : Memory W) :=
  (∀ i : Fin a.initialLanes,∀ j : Fin 4,out (TickWorkspace.base a.age 5+4*i.val+j.val)=
    (BucketRegisters.rowColumn (a.packedRow groups i) j:Word W)) ∧
  (∀ g : Fin a.groups,out (TickWorkspace.base a.age 8+g.val)=
    (BucketRows.count groups (List.ofFn a.lane) g:Word W)) ∧
  ∀ z,(z<TickWorkspace.base a.age 5 ∨ TickWorkspace.base a.age 5+4*a.initialLanes≤z) →
    (z<TickWorkspace.base a.age 8 ∨ TickWorkspace.base a.age 8+a.groups≤z) → out z=m z

/-- The 33 physical rows boot from the mounted navigation header. The S5
row offsets and S8 group counts refer to the same chronological interval fold. -/
theorem pack_spec (a : RootArchive) (groups : Fin a.initialLanes→Fin a.groups) (m : Memory W)
    (room : PackRoom a W) (head : ∀ i : Fin 22,m (a.header+i.val)=(a.word i.val:Word W))
    (rows : a.sources m) (groupsAt : ∀ i : Fin a.initialLanes, m (a.groupRows+4*i.val)=(groups i).val)
    (zero : ∀ g : Fin a.groups,m (TickWorkspace.base a.age 8+g.val)=0) :
    (a.pack (W:=W)).Spec (·=m) (fun _ out=>a.packedPost groups m out) (11+23*a.initialLanes) := by
  intro P R K M pc reg pub exit installed data c mem enter eq
  subst mem
  let b (i : Fin 10) := pc (i.castAdd 23)
  let s (i : Fin 23) := pc (Fin.natAdd 10 i)
  let bootRow : Fin 10 → PrivateRAM.Instr W P R K :=
    BucketScanROM.bootEmit reg pub b (s (Fin.last 22)) exit
  let loopRow : Fin 23 → PrivateRAM.Instr W P R K := BucketScanROM.emit reg s exit exit
  have codeAt (i : Fin (10+23)) : M.code (pc i) =
      Fin.addCases (motive := fun _ => PrivateRAM.Instr W P R K) bootRow loopRow i :=
    installed i
  have boot (i) : M.code (b i)=BucketScanROM.bootEmit reg pub b (s (Fin.last 22)) exit i := by
    exact (codeAt (i.castAdd 23)).trans (Fin.addCases_left ..)
  have loop (i) : M.code (s i)=BucketScanROM.emit reg s exit exit i := by
    exact (codeAt (Fin.natAdd 10 i)).trans (Fin.addCases_right ..)
  have addr (i : Fin 5) : (M.publicData (pub i)).val=a.header+17+i.val := by
    have word : M.publicData (pub i)=((a.header+17+i.val:ℕ):Word W) := data i
    refine (congrArg Fin.val word).trans (Fin.val_cast_of_lt ?_)
    have := room.headers
    have := i.isLt
    omega
  let src:=a.sourceRows
  let gr:=a.groupRows
  let cnt:=TickWorkspace.base a.age 8
  let dst:=TickWorkspace.base a.age 5
  let stop:=src+3*a.initialLanes
  have hs : BucketScanROM.headers pub M.publicData m=
      (⟨src,gr,cnt,dst,stop⟩:BucketRegisters W) := by
    have read (i : Fin 5) : m (M.publicData (pub i)).val=(a.word (17+i.val):Word W) := by
      rw [addr,Nat.add_assoc]
      exact head ⟨17+i.val,by have:=i.isLt;omega⟩
    simp only [BucketScanROM.headers,read]; rfl
  have bound1 : src<2^W := by have:=room.source;dsimp [src];omega
  have bound2 : stop<2^W:=room.source
  obtain ⟨rs,run⟩ := BucketScanROM.advance_from_headers M reg pub b s exit exit boot loop a.initialLanes
    c.persistent c.reg c.privateMem m (by rw [hs];simp only [Fin.val_cast_of_lt bound1,Fin.val_cast_of_lt bound2];dsimp [stop];omega)
  rw [hs] at run
  have ce : c=⟨b 0,c.persistent,c.reg,c.privateMem⟩ := by cases c; congr 1
  rw [←ce] at run
  refine ⟨_,by omega,_,_,run,rfl,?_⟩
  have o1:=room.outBeforeCounters
  have o2:=room.countBeforeSource
  have o3:=room.countBeforeGroups
  have order (i : Fin a.initialLanes) : (a.lane i).lo≤(a.lane i).hi := by
    exact min_le_min_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
  have spec:=BucketRegisters.walk_rows_separated m src gr cnt dst (stop:Word W) groups
    (fun _=>0) a.lane (a.packedRow groups) (a.packed_rows groups) room.output room.source
    room.groups room.counters (.inr o2) (.inr (by dsimp [src,dst];omega)) (.inr o3)
    (.inr (by dsimp [gr,dst];omega)) (.inr o1) order rows groupsAt (by simpa using zero)
  refine ⟨spec.1,?_,fun z hz hc=>spec.2 z hc hz⟩
  intro g
  simpa only [Nat.zero_add] using BucketRegisters.walk_counts_separated m src gr cnt dst (stop:Word W)
    groups (fun _=>0) a.lane room.output room.source room.groups room.counters (.inr o2)
    (.inr (by dsimp [src,dst];omega)) (.inr o3) (.inr (by dsimp [gr,dst];omega)) (.inr o1)
    order rows groupsAt (by simpa using zero) g

/-- The output rows are built in S46 and S47 above the count banks, which
are in turn above the temporary chunk map S7 and below the lookup archives. -/
structure OutputRoom (a : RootArchive) (W : ℕ) : Prop extends PackRoom a W where
  small : 4<2^W
  current : a.current<2^W
  groupEnd : a.groupRows+4*a.initialLanes<2^W
  countersEnd : TickWorkspace.base a.age 8+a.groups<2^W
  laneWidth : a.initialLanes*a.pairsPerLane<2^W
  pairCount : a.totalPairs<2^W
  rootCount : a.rootCount<2^W
  ownerEnd : directory a.age 1+2*a.rootCount≤a.sourceRows
  cacheEnd : a.rootCache+a.initialLanes≤a.sourceRows
  sourcesEnd : a.sourceRows+3*a.initialLanes≤a.groupRows
  chunkEnd : TickWorkspace.base a.age 7+a.chunkBits≤TickWorkspace.base a.age 8
  currentBelow : a.current<TickWorkspace.base a.age 7 ∨
    (TickWorkspace.base a.age 8+a.groups≤a.current ∧ a.current<a.sourceRows)
  headerBetween : TickWorkspace.base a.age 8+a.groups≤a.header ∧ a.header+22≤a.sourceRows

def afterOwners (a : RootArchive) : Procedure W :=
  (a.scan 9 a.bucket).seq ((a.scan 11 a.groupRow).seq
    ((a.scan 13 (.lit 0)).seq ((a.scan 15 (.lit 0)).seq a.pack)))

def afterCost (a : RootArchive) :=
  scanCost a.bucket (3*a.initialLanes)+(scanCost a.groupRow (4*a.initialLanes)+
    (scanCost (.lit 0) a.groups+(scanCost (.lit 0) a.chunkBits+(11+23*a.initialLanes))))

open private runThen from OAI.ThreeFlat.Diagonal.NavigationRootBranches

theorem output_spec (a : RootArchive) (m : Memory W)
    (root : Fin a.initialLanes→Fin a.rootCount) (assign : Fin a.rootCount→Fin a.groups)
    (h : a.outHeader m) (room : OutputRoom a W)
    (cache : ∀ i : Fin a.initialLanes,m (a.rootCache+i.val)=((root i).val:Word W))
    (owners : ∀ r : Fin a.rootCount,m (directory a.age 1+2*r.val)=((assign r).val:Word W)) :
    (a.afterOwners (W:=W)).Spec (·=m)
      (fun _ out=>a.packedPost (assign ∘ root) (a.outputAfter (assign ∘ root) m) out) a.afterCost := by
  let g:=assign ∘ root
  let src:=fillSegment a.sourceRows (3*a.initialLanes) (a.bucketData (W:=W)) m
  let gr:=fillSegment a.groupRows (4*a.initialLanes) (a.groupData g) src
  let cnt:=TickWorkspace.base a.age 8
  let chunk:=TickWorkspace.base a.age 7
  let c0:=fillSegment cnt a.groups (fun _=>0) gr
  let c1:=fillSegment chunk a.chunkBits (fun _=>0) c0
  have sourceBound:=room.source
  have groupBound:=room.groupEnd
  have cntBound:=room.countersEnd
  have ce:=room.chunkEnd
  have cs:=room.countBeforeSource
  have se:=room.sourcesEnd
  have hc:=room.currentBelow
  have hh:=room.headerBetween
  have hSrc : a.outHeader src := fill_header a m _ _ _ h (by dsimp [outside];omega) (.inl hh.2)
  have hGr : a.outHeader gr:=fill_header a src _ _ _ hSrc (by dsimp [outside];omega) (.inl (by omega))
  have h0 : a.outHeader c0:=fill_header a gr _ _ _ hGr (by dsimp [outside,cnt];omega) (.inr hh.1)
  have h1 : a.outHeader c1:=fill_header a c0 _ _ _ h0 (by dsimp [outside,chunk];omega) (.inr (by dsimp [chunk];omega))
  have s1 : (a.scan (W:=W) 9 a.bucket).Spec (·=m) (fun _ o=>o=src)
      (scanCost a.bucket (3*a.initialLanes)) :=
    scan_spec a a.bucket 9 (3*a.initialLanes) a.sourceRows m a.bucketData rfl rfl (by decide)
    h room.headers room.current sourceBound (fun i hi=>bucket_read a _ i hi sourceBound room.small room.output room.laneWidth room.pairCount)
  have before {z : ℕ} (hz : z<a.sourceRows) {i : ℕ} :
      fillSegment a.groupRows i (a.groupData g) src z=m z := by
    rw [fill_frame _ _ _ _ _ (.inl (by omega))]
    exact fill_frame _ _ _ _ _ (.inl hz)
  have s2 : (a.scan (W:=W) 11 a.groupRow).Spec (·=src) (fun _ o=>o=gr)
      (scanCost a.groupRow (4*a.initialLanes)) :=
    scan_spec a a.groupRow 11 (4*a.initialLanes) a.groupRows src (a.groupData g) rfl rfl
    (by decide) hSrc room.headers room.current groupBound (fun i hi=>
      group_read a _ root assign (fun j=>by rw [before (by have:=j.isLt;have:=room.cacheEnd;omega)]; exact cache j)
        (fun r=>by rw [before (by have:=r.isLt;have:=room.ownerEnd;omega)];exact owners r)
        i hi groupBound (by have:=room.cacheEnd;omega) (by have:=room.ownerEnd;omega) room.small room.rootCount)
  have s3 : (a.scan (W:=W) 13 (.lit 0)).Spec (·=gr) (fun _ o=>o=c0)
      (scanCost (.lit 0) a.groups) :=
    scan_spec a (.lit 0) 13 a.groups cnt gr (fun _=>0) rfl rfl (by decide) hGr
    room.headers room.current cntBound (fun _ _=>rfl)
  have s4 : (a.scan (W:=W) 15 (.lit 0)).Spec (·=c0) (fun _ o=>o=c1)
      (scanCost (.lit 0) a.chunkBits) :=
    scan_spec a (.lit 0) 15 a.chunkBits chunk c0 (fun _=>0) rfl rfl (by decide) h0
    room.headers room.current (by dsimp [chunk];omega) (fun _ _=>rfl)
  have upper (z : ℕ) (hz : a.sourceRows≤z) : c1 z=gr z := by
    dsimp only [c1,c0]
    rw [fill_frame _ _ _ _ _ (.inr (by dsimp [chunk];omega)),fill_frame _ _ _ _ _ (.inr (by dsimp [cnt];omega))]
  have read (i : Fin a.initialLanes) (j : Fin 3) :
      c1 (a.sourceRows+3*i.val+j.val)=a.bucketData (a.sourceRows+3*i.val+j.val) := by
    have hi:=i.isLt
    have hj:=j.isLt
    rw [upper _ (by omega)]
    dsimp only [gr]
    rw [fill_frame _ _ _ _ _ (.inl (by omega))]
    exact ite_eq_left (show a.sourceRows≤a.sourceRows+3*i.val+j.val ∧
      a.sourceRows+3*i.val+j.val<a.sourceRows+3*a.initialLanes by omega)
  have digit (i : Fin a.initialLanes) (j : Fin 3) :
      c1 (a.sourceRows+3*i.val+j.val)=
        (if j.val=0 then ((4*i.val:ℕ):Word W)
         else if j.val=1 then (a.clipped i.val:Word W) else (a.clipped (i.val+1):Word W)) := by
    rw [read i j]
    have smallDigit:=j.isLt
    have delta : a.sourceRows+3*i.val+j.val-a.sourceRows=3*i.val+j.val := by omega
    have row : (3*i.val+j.val)/3=i.val := by omega
    have field : (3*i.val+j.val)%3=j.val := by omega
    simp only [bucketData,delta,row,field]
  have sources : a.sources c1 := by
    intro i
    exact ⟨digit i 0,digit i 1,digit i 2⟩
  have groups (i : Fin a.initialLanes) : c1 (a.groupRows+4*i.val)=(g i).val := by
    rw [upper _ (by omega)]
    have hi:=i.isLt
    have inside : a.groupRows≤a.groupRows+4*i.val ∧
        a.groupRows+4*i.val<a.groupRows+4*a.initialLanes := by omega
    have addr : a.groupRows+4*i.val-a.groupRows=4*i.val := by omega
    have row : (4*i.val)/4=i.val := by omega
    have field : (4*i.val)%4=0 := by omega
    simp only [gr,fillSegment,ite_eq_left inside,groupData,addr,row,field,dite_eq_left hi,ite_true]
  have zero (i : Fin a.groups) : c1 (cnt+i.val)=0 := by
    have hi:=i.isLt
    dsimp only [c1]
    rw [fill_frame _ _ _ _ _ (.inr (by dsimp [cnt,chunk];omega))]
    exact ite_eq_left (show cnt≤cnt+i.val ∧ cnt+i.val<cnt+a.groups by omega)
  let post := a.packedPost g c1
  let writeChunk : Procedure W := (a.scan 15 (.lit 0)).seq a.pack
  let writeCounts : Procedure W := (a.scan 13 (.lit 0)).seq writeChunk
  let writeGroups : Procedure W := (a.scan 11 a.groupRow).seq writeCounts
  unfold afterOwners afterCost
  intro p₁ r₁ k₁ M₁
  refine runThen (A:=a.scan 9 a.bucket) (B:=writeGroups) (P:=post) (t:=src) s1 ?_ M₁
  intro p₂ r₂ k₂ M₂
  refine runThen (A:=a.scan 11 a.groupRow) (B:=writeCounts) (P:=post) (t:=gr) s2 ?_ M₂
  intro p₃ r₃ k₃ M₃
  refine runThen (A:=a.scan 13 (.lit 0)) (B:=writeChunk) (P:=post) (t:=c0) s3 ?_ M₃
  intro p₄ r₄ k₄ M₄
  refine runThen (A:=a.scan 15 (.lit 0)) (B:=a.pack) (P:=post) (t:=c1) s4 ?_ M₄
  exact a.pack_spec g c1 room.toPackRoom h1.2 sources groups zero

def headerImage (a : RootArchive) : PackedStageArchive.Layout :=
  ⟨a.phase,a.headerRaw,a.headerRaw,a.header,22⟩

def stageImage (a : RootArchive) : PackedStageArchive.Layout :=
  ⟨a.phase,a.stageRaw,a.stageRaw,directory a.age 2,4*a.stageCount⟩

def headerData (a : RootArchive) (z : ℕ) : Word W := (a.word (z-a.header):Word W)

def stageData (a : RootArchive) (ls : List Layers) (z : ℕ) : Word W :=
  (((stageTape ls)[z-directory a.age 2]?).getD 0:ℕ)

def mounted (a : RootArchive) (ls : List Layers) (m : Memory W) : Memory W :=
  writeMemory (fillSegment (directory a.age 2) (4*a.stageCount) (a.stageData ls)
    (fillSegment a.header 22 a.headerData m)) (a.current:Word W) (a.header:Word W)

/-- Both statically mounted arrays use the actual public input bits with a
big-endian word per field. Each array is read before the native schedule runs. -/
theorem mount_then (a : RootArchive) (ls : List Layers) (m : Memory W)
    (body : Procedure W) (post : Memory W→Prop) (ticks : ℕ)
    (headers : Mount a.headerImage a.headerData m) (stages : Mount a.stageImage (a.stageData ls) m)
    (_phase : a.phase<a.header) (separate : a.stageRaw+W*(4*a.stageCount)≤a.header)
    (tail : body.Spec (·=a.mounted ls m) (fun _ out=>post out) ticks) :
    ((PackedStageArchive.procedure a.headerImage).seq ((PackedStageArchive.procedure a.stageImage).seq
      ((start (a.current:Word W) a.header).seq body))).Spec (·=m) (fun _ out=>post out)
      ((22*(5*W+6)+10)+((4*a.stageCount*(5*W+6)+10)+(3+ticks))) := by
  let t:=fillSegment a.header 22 (a.headerData (W:=W)) m
  have raw (mem : Memory W) : a.stageImage.source mem=a.stageRaw := by
    change (if mem a.phase=1 then a.stageRaw else a.stageRaw)=a.stageRaw
    split <;> rfl
  have staged : Mount a.stageImage (a.stageData ls) t := by
    obtain ⟨pf,apart,fit,word⟩:=stages
    refine ⟨pf,by simpa only [raw] using apart,fit,?_⟩
    intro i hi j hj
    have beforeHeader : a.stageRaw+W*i+j<a.header := by
      change i<4*a.stageCount at hi
      have z:=Nat.mul_le_mul_left W (Nat.succ_le_of_lt hi)
      rw [Nat.mul_succ] at z
      omega
    rw [raw t]
    exact (fill_frame m a.headerData a.header 22 _ (.inl beforeHeader)).trans
      (by simpa only [raw m] using word i hi j hj)
  let image:=fillSegment (directory a.age 2) (4*a.stageCount) (a.stageData ls) t
  let setCursor:=start (a.current:Word W) (a.header:Word W)
  have started : setCursor.Spec (·=image) (fun _ out=>out=a.mounted ls m) 3 :=
    Procedure.Spec.atMemory (A:=setCursor) (start_spec _ _) image trivial
  intro p r k M
  refine runThen (A:=PackedStageArchive.procedure a.headerImage)
    (B:=(PackedStageArchive.procedure a.stageImage).seq (setCursor.seq body)) (P:=post) (t:=t)
    (mount_spec a.headerImage a.headerData m headers) ?_ M
  intro p₂ r₂ k₂ M₂
  refine runThen (A:=PackedStageArchive.procedure a.stageImage) (B:=setCursor.seq body)
    (P:=post) (t:=image) (mount_spec a.stageImage (a.stageData ls) t staged) ?_ M₂
  intro p₃ r₃ k₃ M₃
  exact runThen (A:=setCursor) (B:=body) (P:=post) (t:=a.mounted ls m) started tail M₃

theorem mounted_header (a : RootArchive) (ls : List Layers) (m : Memory W)
    (current : a.current<2^W) (separate : directory a.age 2+4*a.stageCount≤a.header)
    (startPosition : a.current<a.header ∨ a.header+22≤a.current) :
    a.outHeader (a.mounted ls m) := by
  refine ⟨by simp [mounted,writeMemory,Fin.val_cast_of_lt current],?_⟩
  intro i
  have ii:=i.isLt
  have distinct : a.header+i.val≠a.current := by omega
  have afterStage : directory a.age 2+4*a.stageCount ≤ a.header+i.val := by omega
  have inHeader : a.header ≤ a.header+i.val ∧ a.header+i.val < a.header+22 := by omega
  simp only [mounted,writeMemory,Fin.val_cast_of_lt current,ite_eq_right distinct]
  rw [fill_frame _ _ _ _ _ (Or.inr afterStage)]
  simp only [fillSegment,ite_eq_left inHeader,headerData,Nat.add_sub_cancel_left]

theorem mounted_stage (a : RootArchive) (ls : List Layers) (m : Memory W)
    (length : ls.length=a.stageCount) (current : a.current<2^W)
    (off : a.current<directory a.age 2 ∨ directory a.age 2+4*a.stageCount≤a.current)
    (i : Fin (stageTape ls).length) :
    a.mounted ls m (directory a.age 2+i.val)=((stageTape ls)[i.val]:Word W) := by
  have ii : i.val < 4*a.stageCount := calc
    i.val < (stageTape ls).length := i.isLt
    _ = 4*ls.length := stageTape_length ls
    _ = 4*a.stageCount := congrArg (4 * ·) length
  have distinct : directory a.age 2+i.val≠a.current := by omega
  have inStage : directory a.age 2 ≤ directory a.age 2+i.val ∧
      directory a.age 2+i.val < directory a.age 2+4*a.stageCount := by omega
  simp only [mounted,writeMemory,Fin.val_cast_of_lt current,ite_eq_right distinct,fillSegment,
    ite_eq_left inStage,stageData,Nat.add_sub_cancel_left,List.getElem?_eq_getElem i.isLt,Option.getD_some]

/-- All IDs below the terminal layer have a later parent; the root rank of a
trace-bearing input lane is therefore in the exact final interval. -/
def Nodes.laneRoot {a : RootArchive} (N : Nodes a) (lanes : a.initialLanes≤a.firstFinal+a.rootCount)
    (i : Fin a.initialLanes) : Fin a.rootCount :=
  let k : Fin (a.firstFinal+a.rootCount):=⟨i.val,lt_of_lt_of_le i.isLt lanes⟩
  ⟨N.chronology.root k,by have h:=N.chronology.root_lt k;rw [N.first] at h;omega⟩

section RootRanks

open PhysicalStage

variable {F : Type} [Field F] {d l : ℕ} {A : State d l}
variable (a : RootArchive) (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O)
    (card : a.rootCount=(r.finalArchive h C O p).1.count)

def runRootId (v : (r.plan.finish h).Site) : Fin a.rootCount :=
  finCongr card.symm ((r.finalArchive h C O p).2 ((r.finalSite h).symm v))

theorem rootSite_rank (v : (r.plan.finish h).Site) :
    runRootSite a r h C O p card (runRootId a r h C O p card v)=v := by
  simp [runRootSite,runRootId]

/-- A trace-bearing input is assigned the actual scheduled group of the same
terminal site reached through every physical shrink/refresh transition. -/
theorem group_of_destination (m : Memory W)
    (rows : r.ArchiveRowsStored a.nodeBank (fun u=>(m u).val) h C O p)
    (zero : O.layer.first=0) (first : a.firstFinal=(r.finalArchive h C O p).1.first)
    (start pairs : A.Site→ℕ) (site : Fin a.initialLanes→A.Site)
    (initial : ∀ i : Fin a.initialLanes,O.id (site i)=i.val)
    (lanes : a.initialLanes≤a.firstFinal+a.rootCount)
    (assign : Fin a.rootCount→Fin a.groups) (i : Fin a.initialLanes) :
    let N:=nodesOfRun a r h C O p m rows zero first card start pairs
    assign (N.laneRoot lanes i)=assign (a.runRootId r h C O p card (r.plan.destination h (site i))) := by
  apply congrArg assign
  apply Fin.ext
  exact nodesOfRun_root a r h C O p m rows zero first card start pairs (site i)
    ⟨i.val,lt_of_lt_of_le i.isLt lanes⟩ (initial i).symm

end RootRanks

def rootsTotal (a : RootArchive) := a.firstFinal+a.rootCount

/-- These remaining memory inequalities compare the fixed scratch banks S11,
S42, S43, S44 and S45. Raw pin, archive and selected-site readbacks use the
same final memory. -/
structure PublishRoom (a : RootArchive) (W : ℕ) : Prop where
  output : OutputRoom a W
  branches : BranchRoom a W
  partition : PartitionRoom a W
  ancestors : AncestorRoom a W a.rootsTotal
  ownerFrame : OwnerFrame a a.rootsTotal
  summary : a.summaryApart
  lanes : a.initialLanes≤a.rootsTotal
  staticHeader : directory a.age 2+4*a.stageCount≤a.header
  raw : a.stageRaw+W*(4*a.stageCount)≤a.header
  phase : a.phase<a.header
  control : a.current<a.header
  chargeAfter : a.header+22≤a.nodeBank.charges
  nodesAfter : a.header+22≤a.nodeBank.nodes
  ownerHeader : outside a.ownerBase (2*a.rootCount) a.current ∧
    (a.header+22≤a.ownerBase ∨ a.ownerBase+2*a.rootCount≤a.header)
  cacheHeader : outside a.rootCache a.rootsTotal a.current ∧
    (a.header+22≤a.rootCache ∨ a.rootCache+a.rootsTotal≤a.header)

theorem mounted_nodes (a : RootArchive) (ls : List Layers) (m : Memory W) (N : Nodes a)
    (room : PublishRoom a W) (input : N.Stored m) : N.Stored (a.mounted ls m) := by
  have after (z : ℕ) (hz : a.header+22≤z) : a.mounted ls m z=m z := by
    have d:=room.staticHeader
    have c:=room.control
    have ne : z≠a.current := by omega
    simp only [mounted,writeMemory,Fin.val_cast_of_lt room.branches.current,ite_eq_right ne]
    rw [fill_frame _ _ _ _ _ (.inr (by omega)),fill_frame _ _ _ _ _ (.inr hz)]
  refine ⟨fun i=>?_,fun i hi=>?_⟩
  · have fit:=room.chargeAfter
    rw [after _ (by omega),after _ (by omega)]
    exact input.1 i
  · rw [after _ (by have:=room.nodesAfter;omega)]
    exact input.2 i hi

private theorem head_after_branches (a : RootArchive) (N : Nodes a) (teams : ℕ)
    (m out : Memory W) (room : PublishRoom a W) (h : a.outHeader m)
    (b : a.branchPost N teams m out) : a.outHeader out := by
  have frame:=b.2.2.2
  refine ⟨(frame a.current room.branches.cursorFree room.ownerHeader.1 room.cacheHeader.1).trans h.1,?_⟩
  intro i
  have hi:=i.isLt
  have stable := frame (a.header+i.val) (fun bank=>by
    have:=room.branches.headerFree bank
    dsimp [outside];omega) (by have:=room.ownerHeader.2;dsimp [outside];omega)
    (by have:=room.cacheHeader.2;dsimp [outside,rootsTotal] at *;omega)
  exact stable.trans (h.2 i)

def publishCost (a : RootArchive) (W : ℕ) :=
  (22*(5*W+6)+10)+((4*a.stageCount*(5*W+6)+10)+(3+(a.branchCost+a.afterCost)))

/-- The complete native publication on a genuine chronological parent table.
The two starting bit ranges hold the fixed root header and stage-directory
words. The returned memory supplies both scheduled owners and packed rows. -/
theorem publish_spec (a : RootArchive) (N : Nodes a) (teams : ℕ) (ls : List Layers)
    (m : Memory W) (room : PublishRoom a W)
    (schedule : ScheduleFacts a W teams N.work N.pairs a.ids)
    (headers : Mount a.headerImage a.headerData m) (stages : Mount a.stageImage (a.stageData ls) m)
    (input : N.Stored m) :
    (a.publish (W:=W)).Spec (·=m) (fun _ out=>∃ branch,
      a.branchPost N teams (a.mounted ls m) branch ∧
      a.packedPost ((a.groupOf N teams schedule (by have:=room.output.countersEnd;omega)) ∘ N.laneRoot room.lanes)
        (a.outputAfter ((a.groupOf N teams schedule (by have:=room.output.countersEnd;omega)) ∘ N.laneRoot room.lanes) branch) out) (a.publishCost W) := by
  let startMem:=a.mounted ls m
  have groupFit : a.groups<2^W := by have:=room.output.countersEnd;omega
  let assign:=a.groupOf N teams schedule groupFit
  let g:=assign ∘ N.laneRoot room.lanes
  have sh:=a.mounted_header ls m room.branches.current room.staticHeader (.inl room.control)
  have left : (a.branchROM (W:=W)).Spec (·=startMem)
      (fun _ out=>a.branchPost N teams startMem out) a.branchCost := by
    intro nPC nRegs nPub M
    exact a.branches_spec N room.branches room.partition room.ancestors room.ownerFrame
      room.summary teams schedule startMem sh (a.mounted_nodes ls m N room input) M
  have right : (a.afterOwners (W:=W)).Spec (fun v=>a.branchPost N teams startMem v)
      (fun v out=>a.packedPost g (a.outputAfter g v) out) a.afterCost := by
    intro p r k M pc reg pub exit install data cfg v head bv
    have loaded:=head_after_branches a N teams startMem v room sh bv
    have cache (i : Fin a.initialLanes) : v (a.rootCache+i.val)=((N.laneRoot room.lanes i).val:Word W) :=
      bv.1.2.2.1 ⟨i.val,lt_of_lt_of_le i.isLt room.lanes⟩
    have owner (i : Fin a.rootCount) : v (directory a.age 1+2*i.val)=((assign i).val:Word W) :=
      a.branch_group N teams schedule groupFit startMem v bv i
    exact a.output_spec v (N.laneRoot room.lanes) assign loaded room.output cache owner
      M pc reg pub exit install data cfg v head rfl
  let result := fun out=>∃ branch,a.branchPost N teams startMem branch ∧
    a.packedPost g (a.outputAfter g branch) out
  have both : ((a.branchROM (W:=W)).seq (a.afterOwners (W:=W))).Spec (·=startMem)
      (fun _ out=>result out) (a.branchCost+a.afterCost) := by
    intro nPC nRegs nPub M
    exact Procedure.Spec.seq (A:=a.branchROM) (B:=a.afterOwners)
      (left:=fun _ out=>a.branchPost N teams startMem out)
      (right:=fun v out=>a.packedPost g (a.outputAfter g v) out)
      left right (fun _ _ b=>b) M
  intro nPC nRegs nPub M
  exact a.mount_then ls m ((a.branchROM (W:=W)).seq a.afterOwners) result _
    headers stages room.phase room.raw both M

/-- Reading any word other than the six output banks yields the original
branch memory. In particular the stage/motif descriptors and raw bits survive. -/
theorem output_frame (a : RootArchive) (g : Fin a.initialLanes→Fin a.groups) (m out : Memory W)
    (done : a.packedPost g (a.outputAfter g m) out) (z : ℕ)
    (s5 : outside (TickWorkspace.base a.age 5) (4*a.initialLanes) z)
    (s7 : outside (TickWorkspace.base a.age 7) a.chunkBits z)
    (s8 : outside (TickWorkspace.base a.age 8) a.groups z)
    (s46 : outside a.sourceRows (3*a.initialLanes) z)
    (s47 : outside a.groupRows (4*a.initialLanes) z) : out z=m z := by
  rw [done.2.2 z s5 s8]
  unfold outputAfter
  rw [fill_frame _ _ _ _ _ s7,fill_frame _ _ _ _ _ s8,fill_frame _ _ _ _ _ s47,fill_frame _ _ _ _ _ s46]

theorem output_zero (a : RootArchive) (g : Fin a.initialLanes→Fin a.groups) (m out : Memory W)
    (done : a.packedPost g (a.outputAfter g m) out) (room : OutputRoom a W)
    (below : TickWorkspace.base a.age 5+4*a.initialLanes≤TickWorkspace.base a.age 7)
    (j : ℕ) (hj : j<a.chunkBits) : out (TickWorkspace.base a.age 7+j)=0 := by
  have c:=room.chunkEnd
  rw [done.2.2 _ (.inr (by omega)) (.inl (by omega))]
  simp [outputAfter,fillSegment,hj]

theorem output_selected (a : RootArchive) (g : Fin a.initialLanes→Fin a.groups) (m out : Memory W)
    (done : a.packedPost g (a.outputAfter g m) out) (room : OutputRoom a W)
    (clockAddr group : ℕ) (clk : clockAddr<2^W) (groupFit : group<2^W)
    (readGroup : out clockAddr=(group:Word W)) :
    TickPairHeader.selected out (clockAddr:Word W) (TickWorkspace.base a.age 8:Word W) (a.groups:Word W)=
      if hh : group<a.groups then (BucketRows.count g (List.ofFn a.lane) ⟨group,hh⟩:Word W) else 0 := by
  have cap:=room.countersEnd
  have groupsFit : a.groups<2^W := by omega
  unfold TickPairHeader.selected
  rw [Fin.val_cast_of_lt clk,readGroup]
  by_cases hh : group<a.groups
  · have lt : (group:Word W)<(a.groups:Word W) := by
      change (group:Word W).val<(a.groups:Word W).val
      rwa [Fin.val_cast_of_lt groupFit,Fin.val_cast_of_lt groupsFit]
    rw [ite_eq_left lt,dite_eq_left hh,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    exact done.2.1 ⟨group,hh⟩
  · have no : ¬(group:Word W)<(a.groups:Word W) := by
      change ¬(group:Word W).val<(a.groups:Word W).val
      rwa [Fin.val_cast_of_lt groupFit,Fin.val_cast_of_lt groupsFit]
    rw [ite_eq_right no,dite_eq_right hh]

private def relabel {n : ℕ} {I : Type*} (site : Fin n→I) (b : Bucket (Fin n)) : Bucket I :=
  ⟨site b.site,b.lo,b.hi⟩

private theorem packed_relabel {n : ℕ} {I G : Type*} [DecidableEq G] (site : Fin n→I) (group : I→G)
    (bs : List (Bucket (Fin n))) (acc : G→ℕ) :
    BucketRows.pack group acc (bs.map (relabel site))=BucketRows.pack (group ∘ site) acc bs := by
  induction bs generalizing acc with
  | nil=>rfl
  | cons b bs ih=> simp only [List.map_cons,BucketRows.pack]; exact congrArg _ (ih _)

private theorem count_relabel {n : ℕ} {I G : Type*} [DecidableEq G] (site : Fin n→I) (group : I→G)
    (bs : List (Bucket (Fin n))) (g : G) :
    BucketRows.count group (bs.map (relabel site)) g=BucketRows.count (group ∘ site) bs g := by
  unfold BucketRows.count
  rw [List.map_map]
  apply congrArg (fun xs : List ℕ => xs.sum)
  apply List.map_congr_left
  intro b _
  by_cases hit : group (site b.site) = g <;>
    simp [relabel,Bucket.size,hit]

/-- Exact instruction charge for the closed formulae in the root publisher.
The reverse pass visits every node in the chronological archive. -/
theorem publishCost_eq (a : RootArchive) (W : ℕ) :
    a.publishCost W = 1613 + 110*W + 24*a.stageCount + 20*(W*a.stageCount) +
      142*a.rootCount + 11*a.rootsTotal + 765*a.initialLanes + 6*a.groups + 6*a.chunkBits := by
  have c : a.rootCharges.work=8 := rfl
  have p : a.prefix.work=37 := rfl
  have m : a.meta.work=66 := rfl
  have r : a.rootFormula.work=25 := rfl
  have b : a.bucket.work=83 := rfl
  have g : a.groupRow.work=27 := rfl
  simp only [publishCost,branchCost,afterCost,scanCost,c,p,m,r,b,g,Formula.work,rootsTotal]
  ring

theorem publishCost_bound (a : RootArchive) (W : ℕ) :
    a.publishCost W ≤ 1613*((W+1)*(a.stageCount+1) + a.rootsTotal + a.initialLanes +
      a.groups + a.chunkBits) := by
  rw [publishCost_eq]
  simp only [rootsTotal,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
  omega

/-- The scalar size and word-representability obligations of the physical
root archive. The eight-word node rows occupy one entire scratch region. -/
structure PublishSizes (a : RootArchive) (W : ℕ) : Prop where
  fixed : 128 ≤ TickWorkspace.stride a.age
  address : TickWorkspace.base a.age 50 < 2^W
  nodes : 8*a.rootsTotal ≤ TickWorkspace.stride a.age
  lanes : a.initialLanes ≤ a.rootsTotal
  stages : 16*a.stageCount ≤ TickWorkspace.stride a.age
  groups : a.groups ≤ TickWorkspace.stride a.age
  chunks : a.chunkBits ≤ TickWorkspace.stride a.age
  laneProduct : a.initialLanes*a.pairsPerLane < 2^W
  pairs : a.totalPairs < 2^W
  raw : a.stageRaw+W*(4*a.stageCount) ≤ a.header

private structure PhysicalSites (a : RootArchive) : Prop where
  current : a.current=TickWorkspace.base a.age 40
  phase : a.phase=TickWorkspace.base a.age 0+2
  header : a.header=TickWorkspace.base a.age 42
  charges : a.nodeBank.charges=TickWorkspace.base a.age 43
  nodes : a.nodeBank.nodes=TickWorkspace.base a.age 44
  cache : a.rootCache=TickWorkspace.base a.age 45
  source : a.sourceRows=TickWorkspace.base a.age 46
  groupRows : a.groupRows=TickWorkspace.base a.age 47
  sums : a.prefixes=TickWorkspace.base a.age 48

local macro "bank_arith" : tactic => `(tactic|
  ((try dsimp only [lower,extent,outside,rootsTotal] at *) <;> omega))

set_option maxHeartbeats 3000000 in
private theorem room_at_sites (a : RootArchive) (W : ℕ) (whereAt : PhysicalSites a)
    (sizes : PublishSizes a W) : PublishRoom a W := by
  rcases whereAt with ⟨hc,hp,hh,hcharge,hnode,hcache,hsrc,hgroup,hprefix⟩
  rcases sizes with ⟨small,word,nodes,lanes,stages,ng,nc,lp,total,raw⟩
  let s:=TickWorkspace.stride a.age
  have b5 : TickWorkspace.base a.age 5=6*s := rfl
  have b7 : TickWorkspace.base a.age 7=8*s := rfl
  have b8 : TickWorkspace.base a.age 8=9*s := rfl
  have bs : a.statsBase=7*s := rfl
  have d0 : a.chargeBase=12*s := by change 12*s+0*(s/4)=12*s; omega
  have d1 : a.ownerBase=12*s+s/4 := by change 12*s+1*(s/4)=12*s+s/4; omega
  have d1' : directory a.age 1=12*s+s/4 := d1
  have d2 : directory a.age 2=12*s+2*(s/4) := rfl
  have d3 : a.descBase=12*s+3*(s/4) := rfl
  change 51*s<2^W at word
  change a.current=41*s at hc
  change a.phase=1*s+2 at hp
  change a.header=43*s at hh
  change a.nodeBank.charges=44*s at hcharge
  change a.nodeBank.nodes=45*s at hnode
  change a.rootCache=46*s at hcache
  change a.sourceRows=47*s at hsrc
  change a.groupRows=48*s at hgroup
  change a.prefixes=49*s at hprefix
  change 128≤ s at small
  change 8*(a.firstFinal+a.rootCount)≤ s at nodes
  change a.initialLanes≤a.firstFinal+a.rootCount at lanes
  change 16*a.stageCount≤ s at stages
  change a.groups≤ s at ng
  change a.chunkBits≤ s at nc
  have pack : PackRoom a W := by constructor <;> bank_arith
  have output : OutputRoom a W := by
    refine ⟨pack,?_,?_,?_,?_,lp,total,?_,?_,?_,?_,?_,?_,?_⟩ <;> bank_arith
  have branches : BranchRoom a W := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro b; cases b <;> bank_arith
    · bank_arith
    · bank_arith
    · bank_arith
    · intro b c ne
      cases b <;> cases c <;> first | exact (ne rfl).elim | bank_arith
    · intro b; cases b <;> bank_arith
    · intro b; cases b <;> bank_arith
    · intro b z live; cases b <;> bank_arith
  have partition : PartitionRoom a W := by constructor <;> bank_arith
  have ancestors : AncestorRoom a W a.rootsTotal := by constructor <;> bank_arith
  have frame : OwnerFrame a a.rootsTotal := by constructor <;> bank_arith
  have summary : a.summaryApart := by intro z hz; bank_arith
  exact ⟨output,branches,partition,ancestors,frame,summary,lanes,by bank_arith,
    raw,by bank_arith,by bank_arith,by bank_arith,by bank_arith,by bank_arith,by bank_arith⟩

/-- The same archive construction used by Parameters.machine. -/
abbrev parameterArchive (p : Parameters) (degree : ℕ) (ss : List NavigationDirectory.Stage) (W : ℕ) :=
  let A:=p.archive degree W
  p.rootArchive A (p.nodeArchive A ss W) ss W

theorem physical_publish_room (p : Parameters) (degree : ℕ) (ss : List NavigationDirectory.Stage)
    (W : ℕ) (sizes : PublishSizes (parameterArchive p degree ss W) W) :
    PublishRoom (parameterArchive p degree ss W) W :=
  room_at_sites _ _ ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ sizes

/-- The bit immediately past the published stage directory is the exact end
of the grid library and all four consecutive static tables. -/
theorem parameterArchive_rawEnd (p : Parameters) (degree : ℕ) (ss : List NavigationDirectory.Stage)
    (W : ℕ) :
    (parameterArchive p degree ss W).stageRaw+W*(4*(parameterArchive p degree ss W).stageCount) =
      p.rawTables+W*(p.codebookWords+(84*(ss.length+1)+86)) := by
  change p.rawTables+W*p.codebookWords+W*(64*(ss.length+2))+W*(16*(ss.length+1))+22*W+
    W*(4*(ss.length+1))=_
  ring

theorem cursor_raw_end {F : Type} [Field F] [Fintype F] (B : PhysicalStage.Block F)
    (u rem low stride cells : ℕ) (shape : RAM.PhysicalPinsExpr.Shape) (offset unitWork degree : ℕ) :
    let p:=Parameters.cursor B u rem low stride cells shape offset unitWork
    let W:=16*u^10
    let ss:=(B.repeat (u^8)).directory rem p.axes
    let R:=parameterArchive p degree ss W
    R.stageRaw+W*(4*R.stageCount) = 2+shape.advice+shape.teamBits+shape.timeBits+offset+
      W*((Parameters.gridWords B u)++p.staticWords B (u^8) rem W).length := by
  intro p W ss R
  change (parameterArchive p degree ss W).stageRaw+W*(4*(parameterArchive p degree ss W).stageCount)=_
  rw [parameterArchive_rawEnd,List.length_append,Parameters.gridWords_length,Parameters.staticWords_length]
  have length : ss.length=(B.repeat (u^8)).length := PhysicalStage.Program.directory_length _ _ _
  rw [length]; rfl

/-- Scalar consequence of the same parameter fit used by the mounted trace.
At paper scale the raw suffix is already below the first scratch region. -/
theorem cursor_raw_room {F : Type} [Field F] [Fintype F] (B : PhysicalStage.Block F)
    (u rem low stride cells : ℕ) (shape : RAM.PhysicalPinsExpr.Shape) (offset unitWork degree : ℕ)
    (fit : offset+(16*u^10)*((Parameters.gridWords B u)++
      (Parameters.cursor B u rem low stride cells shape offset unitWork).staticWords B (u^8) rem (16*u^10)).length
        ≤ shape.parameterBits)
    (rawLow : 2+shape.advice+shape.teamBits+shape.timeBits+shape.parameterBits≤TickWorkspace.stride u) :
    let p:=Parameters.cursor B u rem low stride cells shape offset unitWork
    let W:=16*u^10
    let R:=parameterArchive p degree ((B.repeat (u^8)).directory rem p.axes) W
    R.stageRaw+W*(4*R.stageCount)≤R.header := by
  intro p W R
  have endAt:=cursor_raw_end B u rem low stride cells shape offset unitWork degree
  change R.stageRaw+W*(4*R.stageCount)=2+shape.advice+shape.teamBits+shape.timeBits+offset+
    W*((Parameters.gridWords B u)++p.staticWords B (u^8) rem W).length at endAt
  change offset+W*((Parameters.gridWords B u)++p.staticWords B (u^8) rem W).length≤ shape.parameterBits at fit
  change R.stageRaw+W*(4*R.stageCount)≤43*TickWorkspace.stride u
  omega

theorem cursor_raw_low {u e : ℕ} (shape : RAM.PhysicalPinsExpr.Shape)
    (age : TraceVolume.cm≤u) (exp : e≤u) (advice : shape.advice=2^(u^3))
    (params : 2+shape.teamBits+shape.timeBits+shape.parameterBits≤u^e) :
    2+shape.advice+shape.teamBits+shape.timeBits+shape.parameterBits≤TickWorkspace.stride u := by
  have h := (TraceVolume.pins_at_scale age exp params).2
  have v : 2^(u^10-2*u)≤2^(u^10) := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  have s : 2^(u^10)≤TickWorkspace.stride u := Nat.le_self_pow (by decide : 4≠0) _
  rw [advice]
  omega

/-- Root and stage bits are the literal tail of the same public table mounted
at the native tick parameters, after the fixed library, stage and node tapes. -/
theorem mount_table_tail (a : RootArchive) (ls : List Layers) (preceding : List ℕ) (base : ℕ)
    (m : Memory W) (addr : a.headerRaw=base+W*preceding.length) (next : a.stageRaw=a.headerRaw+W*22)
    (len : ls.length=a.stageCount) (phase : a.phase<2^W)
    (low : a.stageRaw+W*(4*a.stageCount)≤ min a.header (directory a.age 2))
    (headFit : a.header+22<2^W) (stageFit : directory a.age 2+4*a.stageCount<2^W)
    (raw : let words:=preceding++(List.ofFn (fun i : Fin 22=>a.word i.val)++stageTape ls)
      ∀ i<words.length,∀ j<W,m (base+W*i+j)=
        ((((words[i]?.getD 0:ℕ):Word W).val.testBit (W-1-j)).toNat:Word W)) :
    Mount a.headerImage a.headerData m ∧ Mount a.stageImage (a.stageData ls) m := by
  let hwords:=List.ofFn (fun i : Fin 22=>a.word i.val)
  let st:=stageTape ls
  let words:=preceding++(hwords++st)
  have size : st.length=4*a.stageCount := by rw [show st=stageTape ls from rfl,stageTape_length,len]
  have nh : hwords.length=22:=List.length_ofFn
  have bits (k : ℕ) (hk : k<(hwords++st).length) (j : ℕ) (hj : j<W) :
      m (a.headerRaw+W*k+j)=(((((hwords++st)[k]?.getD 0:ℕ):Word W).val.testBit (W-1-j)).toNat:Word W) := by
    have inside : preceding.length+k < (preceding++(hwords++st)).length := by
      rw [List.length_append]
      exact Nat.add_lt_add_left hk preceding.length
    have r:=raw (preceding.length+k) inside j hj
    rw [List.getElem?_append_right (by omega),show preceding.length+k-preceding.length=k by omega] at r
    simpa only [addr,Nat.mul_add,Nat.add_assoc,hwords,st] using r
  have atHead : a.headerImage.source m=a.headerRaw := by
    change (if m a.phase = 1 then a.headerRaw else a.headerRaw) = a.headerRaw
    split <;> rfl
  have atStage : a.stageImage.source m=a.stageRaw := by
    change (if m a.phase = 1 then a.stageRaw else a.stageRaw) = a.stageRaw
    split <;> rfl
  have lowH:=le_trans low (Nat.min_le_left ..)
  have lowS:=le_trans low (Nat.min_le_right ..)
  refine ⟨⟨phase,by rw [atHead];change a.headerRaw+W*22≤a.header;omega,headFit,?_⟩,
    ⟨phase,by rw [atStage];exact lowS,stageFit,?_⟩⟩
  · intro i hi j hj
    change i<22 at hi
    rw [atHead]
    have r:=bits i (by rw [List.length_append,nh];omega) j hj
    have inside : i < hwords.length := by rwa [nh]
    have fetch : hwords[i]? = some (a.word i) := by
      rw [List.getElem?_eq_getElem inside]
      simp only [hwords,List.getElem_ofFn]
    rw [List.getElem?_append_left inside,fetch] at r
    simpa [headerData,headerImage] using r
  · intro i hi j hj
    change i<4*a.stageCount at hi
    rw [atStage,next]
    have r:=bits (22+i) (by rw [List.length_append,nh,size];omega) j hj
    rw [List.getElem?_append_right (by rw [nh];omega),nh,show 22+i-22=i by omega] at r
    simpa [stageImage,stageData,st,Nat.add_assoc,Nat.mul_add] using r

theorem parameter_mounts {F : Type} [Field F] (p : Parameters) (B : PhysicalStage.Block F)
    (blocks rem W : ℕ) (library : List ℕ) (m : Memory W)
    (equalLen : library.length=p.codebookWords) :
    let A:=p.archive (2^(B.exponent 0)) W
    let ss:=(B.repeat blocks).directory rem A.axes
    let n:=p.nodeArchive A ss W
    let a:=p.rootArchive A n ss W
    let ls:=nodeLayers A.K ss A.cursor A.seedLayer
    let words:=library++p.staticWords B blocks rem W
    a.phase<2^W → a.stageRaw+W*(4*a.stageCount)≤ min a.header (directory a.age 2) →
    a.header+22<2^W → directory a.age 2+4*a.stageCount<2^W →
    (∀ i<words.length,∀ j<W,m (p.rawTables+W*i+j)=
      ((((words[i]?.getD 0:ℕ):Word W).val.testBit (W-1-j)).toNat:Word W)) →
    Mount a.headerImage a.headerData m ∧ Mount a.stageImage (a.stageData ls) m := by
  intro A ss n a ls words phase low headFit stageFit raw
  let data:=A.directory ss (a.rootCount*A.initialDegree) W
  let nodes:=nodeTape n.banks n.headerBase ls
  let preceding:=library++data++nodes
  have count : ls.length=a.stageCount := by simp [ls,nodeLayers_length,a,Parameters.rootArchive]
  have addr : a.headerRaw=p.rawTables+W*preceding.length := by
    simp only [preceding,List.length_append,data,nodes,Archive.directory_length,nodeTape_length,
      ls,nodeLayers_length,equalLen]
    dsimp only [a,n,A,Parameters.rootArchive,Parameters.nodeArchive,Parameters.archive]
    ring
  have stageOffset : a.stageRaw = a.headerRaw + W * 22 := by
    change a.headerRaw + 22 * W = a.headerRaw + W * 22
    rw [Nat.mul_comm 22 W]
  apply mount_table_tail a ls preceding p.rawTables m addr stageOffset count phase low headFit stageFit
  simpa only [words,preceding,data,nodes,Parameters.staticWords,List.append_assoc] using raw

section ClippedInput

open TickPhaseModel TickChronology TickGroupIntervals

variable {F : Type*} [Field F] [Fintype F] {S : HistoryContraction.Shape} {P : Plan F S}
    {bits : P.History→ℕ} {c : Clock} {span : ℕ} {A₀ : RAM.TickActiveROM.Layout}
    (a : RootArchive) (T : Buckets P bits c A₀.bits a.initialLanes span)
    (v : Plan.Terminal P bits) (total : a.totalPairs=c.chunks*A₀.bits) (width : a.pairsPerLane=span)

include total width in
omit [Fintype F] in
private theorem same_lanes : T.rows=(List.ofFn a.lane).map (relabel T.site) := by
  rw [List.map_ofFn]
  unfold Buckets.rows ClippedPairBuckets.rows
  apply congrArg List.ofFn
  funext i
  simp [ClippedPairBuckets.row,relabel,lane,clipped,total,width,Nat.min_comm]

include total width in
omit [Fintype F] in
theorem groups_rows (n : a.groups=c.groups) (g : Fin a.initialLanes→Fin a.groups)
    (home : ∀ i,finCongr n (g i)=T.group v.1 (P.destination v.1 (T.site i))) :
    T.finiteRows (A:=A₀) v=(a.packedRows g).map BucketFiniteLabels.decode := by
  rw [T.finite_values (A:=A₀),packedRows,BucketFiniteLabels.canonical]
  unfold BucketIntervalCodes.intervals
  rw [same_lanes a T total width,packed_relabel]
  have groups : T.home v.1 ∘ T.site=fun i=>(g i).val :=
    funext fun i=>(congrArg Fin.val (home i)).symm
  rw [groups]

include total width in
omit [Fintype F] in
theorem group_count (n : a.groups=c.groups) (g : Fin a.initialLanes→Fin a.groups)
    (home : ∀ i,finCongr n (g i)=T.group v.1 (P.destination v.1 (T.site i))) (ix : Fin a.groups) :
    T.length v ix.val=BucketRows.count g (List.ofFn a.lane) ix := by
  have groups : T.home v.1 ∘ T.site=fun i=>(g i).val :=
    funext fun i=>(congrArg Fin.val (home i)).symm
  rw [Buckets.length,same_lanes a T total width,count_relabel,groups,BucketFiniteLabels.count]

include total width in
omit [Fintype F] in
/-- Every four-word source interval in S5 is the interval used by the
phase model. The physical cursor and the matrix entry use the same lane order. -/
theorem interval_words (n : a.groups=c.groups) (g : Fin a.initialLanes→Fin a.groups)
    (home : ∀ i,finCongr n (g i)=T.group v.1 (P.destination v.1 (T.site i)))
    (m out : Memory W) (post : a.packedPost g (a.outputAfter g m) out) :
    ∀ i : Fin (T.finiteRows (A:=A₀) v).length,∀ k : Fin 4,
      out (TickWorkspace.base a.age 5+4*i.val+k.val)=
        (TickIntervalCursor.intervalColumn ((T.finiteRows (A:=A₀) v)[i.val]'i.isLt) k : Word W) := by
  have r:=groups_rows a T v total width n g home
  have e : (T.finiteRows (A:=A₀) v).length=a.initialLanes := by
    rw [r]
    simp [packedRows,BucketRows.pack_length]
  intro i k
  let j : Fin a.initialLanes:=⟨i.val,lt_of_lt_of_eq i.isLt e⟩
  have index : (T.finiteRows (A:=A₀) v)[i.val]'i.isLt=BucketFiniteLabels.decode (a.packedRow g j) := by
    simpa only [List.getElem_map,packedRow] using getElem_congr r (rfl : i.val = i.val) i.isLt
  rw [index]
  exact post.1 j k

include total in
open private BucketIntervalCodes.source from OAI.ThreeFlat.Diagonal.BucketIntervalCodes in
omit [Fintype F] in
theorem finite_rows_fit (groupsFit : c.groups<2^W) (pairsFit : a.totalPairs<2^W)
    (e : TickGroupIntervals.Interval) (he : e ∈ T.finiteRows (A := A₀) v) : TickIntervalCursor.FitsRow e W := by
  rw [T.finite_values (A := A₀)] at he
  obtain ⟨b, hb, group, first, stop⟩ :=
    BucketIntervalCodes.source (T.home v.1) (fun _ => 0) T.rows e he
  have bounds : b.lo ≤ a.totalPairs ∧ b.hi ≤ a.totalPairs := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    rw [total]
    exact ⟨Nat.min_le_left .., Nat.min_le_left ..⟩
  change e.group < 2^W ∧ e.first < 2^W ∧ e.stop < 2^W
  rw [← group, ← first, ← stop]
  exact ⟨(T.group v.1 (P.destination v.1 b.site)).isLt.trans groupsFit,
    bounds.1.trans_lt pairsFit, bounds.2.trans_lt pairsFit⟩

omit [Fintype F] in
/-- The S5/S7 row initializer supplies all schedule-dependent columns of the
native scan guard, including the compatibility and bound of its packed codes. -/
theorem finite_rows_disjoint :
    (T.finiteRows (A := A₀) v).Pairwise TickGroupIntervals.Compatible := by
  rw [T.finite_values (A := A₀)]
  exact BucketIntervalCodes.compatible (T.home v.1) (fun _ => 0) T.rows
    (ClippedPairBuckets.disjoint T.site (c.chunks * A₀.bits) span (T.home v.1))

end ClippedInput

/-- The addresses below this number never serve as a destination in any of
the native archive/scheduler or interval publication passes. -/
def protectedBelow (a : RootArchive) := min (TickWorkspace.base a.age 5)
  (min (TickWorkspace.base a.age 7) (min (TickWorkspace.base a.age 8)
    (min a.sourceRows (min a.groupRows (min a.current (min a.header
      (min (directory a.age 2) (min a.chargeBase (min a.prefixes (min a.statsBase
        (min a.descBase (min a.ownerBase a.rootCache))))))))))))

theorem read_low (a : RootArchive) (N : Nodes a) (teams : ℕ) (ls : List Layers)
    (g : Fin a.initialLanes→Fin a.groups) (m b out : Memory W)
    (branch : a.branchPost N teams (a.mounted ls m) b)
    (done : a.packedPost g (a.outputAfter g b) out) (fit : a.current<2^W) (z : ℕ)
    (hz : z<a.protectedBelow) : out z=m z := by
  simp only [protectedBelow,lt_min_iff] at hz
  rcases hz with ⟨b5,b7,b8,src,grp,cur,hdr,stages,costs,sums,stats,desc,owners,cache⟩
  rw [output_frame a g b out done z (.inl b5) (.inl b7) (.inl b8) (.inl src) (.inl grp),
    branch.2.2.2 z (fun bank=>Or.inl (by cases bank <;> assumption)) (.inl owners) (.inl cache)]
  simp only [mounted,writeMemory,Fin.val_cast_of_lt fit]
  rw [fill_frame _ _ _ _ _ (.inl stages),fill_frame _ _ _ _ _ (.inl hdr),ite_eq_right cur.ne]

theorem parameter_protected (p : Parameters) (degree W : ℕ) (ss : List NavigationDirectory.Stage) :
    let A:=p.archive degree W
    let a:=p.rootArchive A (p.nodeArchive A ss W) ss W
    protectedBelow a=TickWorkspace.base p.age 5 := by
  dsimp only
  simp only [protectedBelow,Parameters.rootArchive,Parameters.nodeArchive,Parameters.archive,Parameters.banks,
    chargeBase,statsBase,descBase,ownerBase,directory,TickWorkspace.base]
  omega

/-- Scratch addresses whose contents survive every native write of the root publisher. -/
structure Retained (a : RootArchive) (z : ℕ) : Prop where
  current : z≠a.current
  header : outside a.header 22 z
  stages : outside (directory a.age 2) (4*a.stageCount) z
  summary : ∀ b : StageBank,outside (a.lower b) (a.extent b) z
  owners : outside a.ownerBase (2*a.rootCount) z
  cache : outside a.rootCache a.rootsTotal z
  intervals : outside (TickWorkspace.base a.age 5) (4*a.initialLanes) z
  chunk : outside (TickWorkspace.base a.age 7) a.chunkBits z
  counts : outside (TickWorkspace.base a.age 8) a.groups z
  sources : outside a.sourceRows (3*a.initialLanes) z
  labels : outside a.groupRows (4*a.initialLanes) z

theorem read_retained (a : RootArchive) (N : Nodes a) (teams : ℕ) (ls : List Layers)
    (g : Fin a.initialLanes→Fin a.groups) (m b out : Memory W)
    (branch : a.branchPost N teams (a.mounted ls m) b)
    (done : a.packedPost g (a.outputAfter g b) out) (fit : a.current<2^W) (z : ℕ)
    (keep : Retained a z) : out z=m z := by
  rw [output_frame a g b out done z keep.intervals keep.chunk keep.counts keep.sources keep.labels,
    branch.2.2.2 z keep.summary keep.owners keep.cache]
  simp only [mounted,writeMemory,Fin.val_cast_of_lt fit]
  rw [fill_frame _ _ _ _ _ keep.stages,fill_frame _ _ _ _ _ keep.header,ite_eq_right keep.current]

/-- S20..S39 store chronological graph/width/motif archives and the S38 codebook.
The S43/S44 charge and parent tables and the S49 initial metadata are likewise
fully retained across every root read, prefix, ancestry and bucket write. -/
theorem parameter_retained (p : Parameters) (degree : ℕ) (ss : List NavigationDirectory.Stage)
    (W : ℕ) (sizes : PublishSizes (parameterArchive p degree ss W) W) (z : ℕ)
    (zone : (TickWorkspace.base p.age 20≤z ∧ z<TickWorkspace.base p.age 40) ∨
      (TickWorkspace.base p.age 43≤z ∧ z<TickWorkspace.base p.age 45) ∨ TickWorkspace.base p.age 49≤z) :
    Retained (parameterArchive p degree ss W) z := by
  let a:=parameterArchive p degree ss W
  let s:=TickWorkspace.stride p.age
  have unit : 128≤ s:=sizes.fixed
  have nodes : 8*a.rootsTotal≤ s:=sizes.nodes
  have lanes : a.initialLanes≤a.rootsTotal:=sizes.lanes
  have stages : 16*a.stageCount≤ s:=sizes.stages
  have groups : a.groups≤ s:=sizes.groups
  have chunks : a.chunkBits≤ s:=sizes.chunks
  have width : a.rootCount≤a.rootsTotal := by dsimp only [rootsTotal];omega
  change (21*s≤z ∧ z<41*s) ∨ (44*s≤z ∧ z<46*s) ∨ 50*s≤z at zone
  have zc : outside (47*s) (3*a.initialLanes) z := by dsimp [outside];omega
  change Retained a z
  constructor
  · change z≠41*s;omega
  · change outside (43*s) 22 z;dsimp [outside];omega
  · change outside (12*s+2*(s/4)) (4*a.stageCount) z;dsimp [outside];omega
  · intro b
    cases b with
    | charges=>change outside (12*s+0*(s/4)) (2*a.rootCount) z;dsimp [outside];omega
    | sums=>change outside (49*s) (a.rootCount+1) z;dsimp [outside];omega
    | stats=>change outside (7*s) 8 z;dsimp [outside];omega
    | desc=>change outside (12*s+3*(s/4)) 3 z;dsimp [outside];omega
  · change outside (12*s+1*(s/4)) (2*a.rootCount) z;dsimp [outside];omega
  · change outside (46*s) a.rootsTotal z;dsimp [outside];omega
  · change outside (6*s) (4*a.initialLanes) z;dsimp [outside];omega
  · change outside (8*s) a.chunkBits z;dsimp [outside];omega
  · change outside (9*s) a.groups z;dsimp [outside];omega
  · exact zc
  · change outside (48*s) (4*a.initialLanes) z;dsimp [outside];omega

theorem filled_high {F : Type*} [Field F] [Fintype F] {B : TickActiveROM.Layout} {p H J : ℕ}
    {fit : RAM.Contraction.Fits (TickWeightedBank.shape F p H J) W} {clock : TickChronology.Clock}
    (x : TickActiveROM.CellInput B clock fit) (out : Memory W) (ph : TickChronology.Phase)
    (z : ℕ) (bounds : B.bounds+4≤2^W) (endBounds : B.bounds+4≤z) (endRequests : B.auxRequest+8*B.bits≤z) :
    x.filled ph out z=out z := by
  exact (fill_frame _ _ _ _ _ (.inr endRequests)).trans (TickActiveROM.bounds_high B clock out z endBounds bounds)

/-- The two-word [group,slot] owner record consumed by both selected-node
scans. Only genuine indices below the root count are ever looked up. -/
def scheduledOwner (a : RootArchive) (N : Nodes a) (teams : ℕ) (i : ℕ) : Word W × Word W :=
  ((a.scheduled (W:=W) teams N.work N.pairs a.ids)[i]?).getD (0,0)

theorem directory_read {F : Type*} [Field F] [Fintype F] {B : TickActiveROM.Layout} {p H J : ℕ}
    {fit : RAM.Contraction.Fits (TickWeightedBank.shape F p H J) W} {clock : TickChronology.Clock}
    (x : TickActiveROM.CellInput B clock fit) (a : RootArchive) (N : Nodes a) (teams : ℕ)
    (g : Fin a.initialLanes→Fin a.groups) (m b out : Memory W)
    (branch : a.branchPost N teams m b) (done : a.packedPost g (a.outputAfter g b) out)
    (sched : ScheduleFacts a W teams N.work N.pairs a.ids) (r : OutputRoom a W)
    (s5 : TickWorkspace.base a.age 5+4*a.initialLanes≤a.statsBase)
    (s6 : a.statsBase+8≤TickWorkspace.base a.age 7)
    (s8 : TickWorkspace.base a.age 8+a.groups≤a.ownerBase)
    (space : B.bounds+4≤2^W) (boundsBefore : B.bounds+4≤a.statsBase)
    (requestsBefore : B.auxRequest+8*B.bits≤a.statsBase) :
    let prepared:=x.filled .evaluate out
    (a.summaryHeader N).stored a.age prepared ∧ ∀ i<a.rootCount,
      prepared (directory a.age 1+2*i)=(a.scheduledOwner N teams i).1 ∧
      prepared (directory a.age 1+2*i+1)=(a.scheduledOwner N teams i).2 := by
  have st:=r.sourcesEnd
  have sc:=r.countBeforeSource
  have sg:=r.countBeforeGroups
  have chunk:=r.chunkEnd
  have ow : a.ownerBase+2*a.rootCount≤a.sourceRows := r.ownerEnd
  have keep (z) (within : a.statsBase≤z ∧ z<a.statsBase+8 ∨ a.ownerBase≤z ∧ z<a.ownerBase+2*a.rootCount) :
      x.filled .evaluate out z=b z := by
    rw [filled_high x out .evaluate z space (by omega) (by omega)]
    exact output_frame a g b out done z (Or.inr (by omega))
      (by dsimp [outside];omega) (by dsimp [outside];omega) (Or.inl (by omega)) (Or.inl (by omega))
  refine ⟨fun i=>?_,fun i hi=>?_⟩
  · have hk:=i.isLt
    exact (keep _ (.inl ⟨Nat.le_add_right ..,by omega⟩)).trans (branch.2.1 i)
  · have nl : (a.scheduled (W:=W) teams N.work N.pairs a.ids).length=a.rootCount := by
      rw [scheduled_length a teams N.work N.pairs a.ids sched];simp [ids]
    let j : Fin (a.scheduled (W:=W) teams N.work N.pairs a.ids).length:=⟨i,by rwa [nl]⟩
    have rd:=branch.1.2.1 j
    have l:=keep (a.ownerBase+2*i) (.inr ⟨by omega,by omega⟩)
    have u:=keep (a.ownerBase+2*i+1) (.inr ⟨by omega,by omega⟩)
    simpa [scheduledOwner,List.getElem?_eq_getElem j.isLt,j,ownerBase] using And.intro (l.trans rd.1) (u.trans rd.2)

section PhysicalInput

open RAM.TickActiveROM RAM.TickBitRelation RAM.TickIntervalCursor TickChronology TickPhaseModel TickAuxiliary
open RAM.HistoryFactors RAM.Contraction RAM.BitLayout

variable {F : Type*} [Field F] [Fintype F] {S : HistoryContraction.Shape} {P : Plan F S} {bits : P.History→ℕ}
    {c : Clock} {A : RAM.TickActiveROM.Layout} {span p H J : ℕ}
    {fit : Fits (TickWeightedBank.shape F p H J) W} (a : RootArchive) (T : Buckets P bits c A.bits a.initialLanes span)
    (v : Plan.Terminal P bits) (t : ℕ) (oa : Aux A.bits)
    (pairFit : 1+A.capacity+2*T.length v (c.group t)≤A.bits) (N : BitNetwork F p)
    (L : Library N) (hh : N.internal≤H) (hj : N.cells+(H-N.internal)≤J)
    (lut : A.lut+8*(L.count+2)≤2^W)

local notation "cell" => T.cellInput (fit:=fit) v t oa pairFit N L hh hj lut

/-- All row and map premises of the scan branch come from the real publisher.
Only the read-only tick clock and the incoming boundary register are read
from the other banks. -/
theorem scanWords (sCount : A.intervalCount=TickWorkspace.base a.age 6)
    (sTable : A.intervalTable=TickWorkspace.base a.age 5) (sMap : A.intervalMap=TickWorkspace.base a.age 7)
    (chunkBits : a.chunkBits=A.bits) (total : a.totalPairs=c.chunks*A.bits) (width : a.pairsPerLane=span)
    (ng : a.groups=c.groups) (g : Fin a.initialLanes→Fin a.groups)
    (home : ∀ i,finCongr ng (g i)=T.group v.1 (P.destination v.1 (T.site i)))
    (nav : Nodes a) (branch out : Memory W) (stats : (a.summaryHeader nav).stored a.age branch)
    (done : a.packedPost g (a.outputAfter g branch) out) (r : OutputRoom a W)
    (space : TickWorkspace.base a.age 5+4*a.initialLanes≤TickWorkspace.base a.age 6)
    (chunkFit : (cell).lo+A.bits<2^W) (grpFit : c.group t<2^W)
    (clockChunk : out (A.clockWords+2)=((cell).lo:Word W))
    (clockGroup : out A.clockWords=(c.group t:Word W))
    (old : ∀ i : Fin A.bits,out (A.oldAux+i.val)=TickBitRelation.bitWord W (oa i)) :
    ScanWords cell out := by
  have cntFit : c.groups<2^W := by have:=r.countersEnd;omega
  have no6 : TickWorkspace.base a.age 6<TickWorkspace.base a.age 7 := by
    have pos : 0<TickWorkspace.stride a.age := by simp [TickWorkspace.stride]
    simp only [TickWorkspace.base];omega
  have partCount : out A.intervalCount=(a.initialLanes:Word W) := by
    rw [sCount,output_frame a g branch out done _ (.inr space) (.inl no6) (.inl (by
      have:=r.chunkEnd;omega)) (.inl (by have:=r.chunkEnd;have:=r.countBeforeSource;omega))
      (.inl (by have:=r.chunkEnd;have:=r.countBeforeGroups;omega))]
    exact stats 0
  have cells : (T.finiteRows (A:=A) v).length=a.initialLanes := by
    rw [groups_rows (A₀:=A) a T v total width ng g home]
    simp [packedRows,BucketRows.pack_length]
  refine ⟨finite_rows_disjoint (A₀:=A) a T v,chunkFit,grpFit,
    fun e he=>finite_rows_fit (A₀:=A) a T v total cntFit r.pairCount e he,?_,clockChunk,clockGroup,?_,?_,?_,?_,?_⟩
  · change out A.intervalCount=((T.finiteRows (A:=A) v).length:Word W);rwa [cells]
  · rw [sTable];exact interval_words (A₀:=A) a T v total width ng g home branch out done
  · intro j hj
    rw [sMap]
    exact output_zero a g branch out done r (by omega) j (by rwa [chunkBits])
  · intro i
    change TickChunkCheck.codeAt (TickGroupScanBank.layout A.scan _ (c.group t)) (T.finiteRows (A:=A) v) i.val≤T.length v (c.group t)
    rw [T.finite_values (A:=A)]
    exact PackedBucketBijection.pairCode_le_count ..
  · intro j hpos
    rw [T.cellInput_before_read (fit:=fit) v t oa pairFit N L hh hj lut j hpos]
    simpa only [Nat.add_assoc] using old ⟨(cell).aux.wiresEnd+j,by
      change 1+A.capacity+j<A.bits
      change j<T.length v (c.group t) at hpos
      omega⟩
  · intro j hpos
    rw [T.cellInput_after_read (fit:=fit) v t oa pairFit N L hh hj lut j hpos]
    simpa only [Nat.add_assoc] using old ⟨(cell).aux.wiresEnd+(cell).count+j,by
      change 1+A.capacity+T.length v (c.group t)+j<A.bits
      change j<T.length v (c.group t) at hpos
      omega⟩

def preparedInput (a : RootArchive) (x : TickActiveROM.CellInput A c fit) (nodes : Nodes a) (teams : ℕ)
    (ls : List Layers) (m : Memory W) (g : Fin a.initialLanes→Fin a.groups) (prepared : Memory W) :=
  ∃ b o,a.branchPost nodes teams (a.mounted ls m) b ∧ a.packedPost g (a.outputAfter g b) o ∧
    prepared=x.filled .evaluate o

/-- Observable navigation state for all native phases. The selected preparation
receives the actual returned memory with the scheduled roots, and its pair
request fields initialized by the active tick module. -/
theorem navOutput (sCount : A.intervalCount=TickWorkspace.base a.age 6)
    (sTable : A.intervalTable=TickWorkspace.base a.age 5) (sMap : A.intervalMap=TickWorkspace.base a.age 7)
    (sCounters : A.groupCounts=TickWorkspace.base a.age 8)
    (chunkBits : a.chunkBits=A.bits) (total : a.totalPairs=c.chunks*A.bits) (width : a.pairsPerLane=span)
    (ng : a.groups=c.groups) (g : Fin a.initialLanes→Fin a.groups)
    (home : ∀ i,finCongr ng (g i)=T.group v.1 (P.destination v.1 (T.site i)))
    (nav : Nodes a) (teams : ℕ) (ls : List Layers) (m branch out : Memory W)
    (published : a.branchPost nav teams (a.mounted ls m) branch)
    (done : a.packedPost g (a.outputAfter g branch) out) (r : OutputRoom a W)
    (space : TickWorkspace.base a.age 5+4*a.initialLanes≤TickWorkspace.base a.age 6)
    (bounds : WordBounds A fit) (ranges : ScanRanges A (T.finiteRows v).length W)
    (chunkFit : (cell).lo+A.bits<2^W) (grpFit : c.group t<2^W) (clkFit : A.clockWords<2^W)
    (clo : A.clockWords+3<a.protectedBelow) (ctl : A.control+3<a.protectedBelow)
    (oaFit : A.oldAux+A.bits≤a.protectedBelow) (naFit : A.newAux+A.bits≤a.protectedBelow)
    (ocFit : A.oldChunk+A.bits≤a.protectedBelow) (ncFit : A.newChunk+A.bits≤a.protectedBelow)
    (na oc nc : Aux A.bits) (team : ℕ) (clock : TickPhysicalABI.Inputs A c m team t)
    (mountedOld : ∀ i : Fin A.bits,m (A.oldAux+i.val)=TickBitRelation.bitWord W (oa i))
    (mountedNew : ∀ i : Fin A.bits,m (A.newAux+i.val)=TickBitRelation.bitWord W (na i))
    (chunkOld : ∀ i : Fin A.bits,m (A.oldChunk+i.val)=TickBitRelation.bitWord W (oc i))
    (chunkNew : ∀ i : Fin A.bits,m (A.newChunk+i.val)=TickBitRelation.bitWord W (nc i)) :
    NavOutput cell (c.phase t) oa na oc nc (a.preparedInput cell nav teams ls m g) out := by
  have low:=read_low a nav teams ls g m branch out published done r.current
  have readGroup : out A.clockWords=(c.group t:Word W) := by
    rw [low _ (by omega)]
    have groupWord := clock.2 (0 : Fin 4)
    change m (A.clockWords+0) = (c.group t : Word W) at groupWord
    simpa only [Nat.add_zero] using groupWord
  have readChunk : out (A.clockWords+2)=((cell).lo:Word W) := by
    rw [low _ (by omega)];exact clock.2 2
  have readOld (i : Fin A.bits) := (low (A.oldAux+i.val) (by have:=i.isLt;omega)).trans (mountedOld i)
  have selected : TickPairHeader.selected out A.clockWords A.groupCounts c.groups=((cell).count:Word W) := by
    rw [sCounters,←ng,a.output_selected g branch out done r _ _ clkFit grpFit readGroup]
    by_cases inside : c.group t<a.groups
    · rw [dite_eq_left inside,←group_count a T v total width ng g home ⟨c.group t,inside⟩]
      change (T.length v (c.group t) : Word W) = (T.length v (c.group t) : Word W)
      rfl
    · change (if hh : _ then _ else 0)=(T.length v (c.group t):Word W)
      rw [dite_eq_right inside,T.length_outside v _ (by omega),Nat.cast_zero]
  apply NavOutput.of_staged cell (c.phase t) out oa na oc nc _ bounds selected
  · rw [low _ (by omega)];exact clock.1 2
  · rw [low _ (by omega)];exact clock.1 3
  · exact readOld
  · intro i;exact (low _ (by have:=i.isLt;omega)).trans (mountedNew i)
  · intro i;exact (low _ (by have:=i.isLt;omega)).trans (chunkOld i)
  · intro i;exact (low _ (by have:=i.isLt;omega)).trans (chunkNew i)
  · intro _
    refine ⟨ranges,?_⟩
    exact scanWords a T v t oa pairFit N L hh hj lut sCount sTable sMap chunkBits total width ng g home
      nav branch out published.2.1 done r space chunkFit grpFit readChunk readGroup readOld
  · intro eq
    exact ⟨branch,out,published,done,by rw [eq]⟩

/-- The actual complete root-publisher procedure returns all phase/scan inputs
to the caller. The selected continuation receives the same root ordering and
immutable archives used by the geometry. -/
theorem publish_nav (nodes : Nodes a) (teams : ℕ) (ls : List Layers) (m : Memory W)
    (geometry : PublishRoom a W) (schedule : ScheduleFacts a W teams nodes.work nodes.pairs a.ids)
    (headers : Mount a.headerImage a.headerData m) (stages : Mount a.stageImage (a.stageData ls) m)
    (stored : nodes.Stored m) (sCount : A.intervalCount=TickWorkspace.base a.age 6)
    (sTable : A.intervalTable=TickWorkspace.base a.age 5) (sMap : A.intervalMap=TickWorkspace.base a.age 7)
    (sCounters : A.groupCounts=TickWorkspace.base a.age 8)
    (chunkBits : a.chunkBits=A.bits) (total : a.totalPairs=c.chunks*A.bits) (width : a.pairsPerLane=span)
    (ng : a.groups=c.groups) (groupFits : a.groups<2^W)
    (home : ∀ i,finCongr ng (a.groupOf nodes teams schedule groupFits (nodes.laneRoot geometry.lanes i))=
      T.group v.1 (P.destination v.1 (T.site i)))
    (space : TickWorkspace.base a.age 5+4*a.initialLanes≤TickWorkspace.base a.age 6)
    (bounds : WordBounds A fit) (ranges : ScanRanges A (T.finiteRows v).length W)
    (chunkFit : (cell).lo+A.bits<2^W) (grpFit : c.group t<2^W) (clkFit : A.clockWords<2^W)
    (clo : A.clockWords+3<a.protectedBelow) (ctl : A.control+3<a.protectedBelow)
    (oaFit : A.oldAux+A.bits≤a.protectedBelow) (naFit : A.newAux+A.bits≤a.protectedBelow)
    (ocFit : A.oldChunk+A.bits≤a.protectedBelow) (ncFit : A.newChunk+A.bits≤a.protectedBelow)
    (na oc nc : Aux A.bits) (team : ℕ) (clock : TickPhysicalABI.Inputs A c m team t)
    (mountedOld : ∀ i : Fin A.bits,m (A.oldAux+i.val)=TickBitRelation.bitWord W (oa i))
    (mountedNew : ∀ i : Fin A.bits,m (A.newAux+i.val)=TickBitRelation.bitWord W (na i))
    (chunkOld : ∀ i : Fin A.bits,m (A.oldChunk+i.val)=TickBitRelation.bitWord W (oc i))
    (chunkNew : ∀ i : Fin A.bits,m (A.newChunk+i.val)=TickBitRelation.bitWord W (nc i)) :
    let groups:=(a.groupOf nodes teams schedule groupFits) ∘ nodes.laneRoot geometry.lanes
    (a.publish (W:=W)).Spec (·=m) (fun _ out=>NavOutput cell (c.phase t) oa na oc nc
      (a.preparedInput cell nodes teams ls m groups) out) (a.publishCost W) := by
  let g:=(a.groupOf nodes teams schedule groupFits) ∘ nodes.laneRoot geometry.lanes
  have issued : (a.publish (W:=W)).Spec (·=m) (fun _ out => ∃ branch,
      a.branchPost nodes teams (a.mounted ls m) branch ∧
      a.packedPost g (a.outputAfter g branch) out) (a.publishCost W) :=
    a.publish_spec nodes teams ls m geometry schedule headers stages stored
  change (a.publish (W:=W)).Spec (·=m) (fun _ out=>NavOutput cell (c.phase t) oa na oc nc
    (a.preparedInput cell nodes teams ls m g) out) (a.publishCost W)
  intro labelCount registerCount slotCount machine
  refine Procedure.Spec.mono (A:=a.publish (W:=W)) issued (fun _ h=>h) ?_ le_rfl machine
  rintro _ out ⟨b,bv,done⟩
  exact navOutput a T v t oa pairFit N L hh hj lut sCount sTable sMap sCounters chunkBits total width ng g
    home nodes teams ls m b out bv done geometry.output space bounds ranges chunkFit grpFit clkFit
    clo ctl oaFit naFit ocFit ncFit na oc nc team clock mountedOld mountedNew chunkOld chunkNew

end PhysicalInput


end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows PhysicalStage
open scoped Classical

/-- Rows read from the selected physical archive give the immutable input to the
native directory writer. Its child copies always address an earlier layer. -/
theorem sourceRows_of_archivedSource {F : Type} [Field F] {d l W H M : ℕ} {A : State d l}
    (a : NodeArchive) (r : Run F A) (h : r.plan.History) (C : r.Charges) (O : A.ArchiveSites)
    (p : r.ArchivePath h C O) (seed : LayerData O.layer) (m : Memory W) (safe : ℕ→Prop)
    (noChildren : O.layer.childCount=0) (halfCap : H≤a.halfCap) (motifCap : M≤a.motifCap) :
    let xs:=r.archiveList h C O p seed
    (∀ q∈xs,ArchivedSource q safe (natural m) H M) →
    (∀ x,safe x→x<2^W ∧ stable a (records xs) x ∧ ∀ i : Fin (records xs).length,
      x<a.banks.charges ∨ a.banks.nodes+8*(((records xs).get i).actual.first+((records xs).get i).actual.count)≤x) →
    SourceRows a (program xs) m := by
  intro xs archived protect
  have row (i : Fin (records xs).length) := archived _ (view_mem xs i)
  refine ⟨fun i=>(row i).contents.reads,?_,?_,?_,fun i=>(row i).parents,?_,
    archive_old r h C O p seed noChildren,?_,?_⟩
  · intro i
    have f:=((row i).contents.footprint).mono (fun x hx=>(protect x hx).1)
    exact ⟨f.child,f.halfPtr,f.width,f.motifPtr,f.copies⟩
  · exact fun i=>((row i).contents.footprint).mono (fun x hx=>(protect x hx).2.1)
  · exact fun i=>((row i).contents.footprint).mono (fun x hx=>(protect x hx).2.2 i)
  · exact fun i current j=>(protect _ ((row i).ownerCells current j)).2.1
  · exact fun i j=>((row i).contents.halves j).trans halfCap
  · exact fun i nz j=>((row i).contents.motifs nz j).trans motifCap


end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure PhysicalStage NavigationDirectory
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 1000000 in
/-- Apply journal reconstruction using the records and charges of the same repeated block.
The machine and its cursor remain parameters until the selected seed run supplies them. -/
private theorem block_journal_rows {F : Type} [Field F] (B : Block F) {a : Archive} {u : ℕ}
    {cur ctr : Word (16*u^10)} (n rem : ℕ)
    (X : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (cap : B.alphabetCap ≤ a.K)
    (word : B.repeatFactor*((X.maxWidth+1)*B.widthBase^n) < 2^(16*u^10))
    (raw : List Bool) {origin final : Memory (16*u^10)}
    (journal : a.Journal u cur ctr (B.repeat n) rem X a.cursor raw origin final)
    (age : 40 ≤ u) (controls : cur.val < ctr.val) (old : X.ArchiveSites)
    (num : old.Numbered) (first : old.layer.first=a.cursor.node) (data : LayerData old.layer)
    (safe : ℕ → Prop) (H MCap : ℕ)
    (seed : RowContents data safe (fun i=>(final i).val) H MCap)
    (space : JournalSpace a.K (16*u^10) H MCap ((B.repeat n).directory rem (Fintype.card X.Base))
      a.cursor old.layer safe)
    (headerDense : (finish a.K ((B.repeat n).directory rem (Fintype.card X.Base)) a.cursor).header ≤ a.cursor.dense)
    (headerStart : TickWorkspace.base u 20 ≤ a.cursor.header) :
    let P := B.repeat n
    let rows := P.directory rem (Fintype.card X.Base)
    let endAt := finish a.K rows a.cursor
    Recovered (P.run rem X) (B.recordTable a.K (16*u^10) n rem X cap word).records
      (B.charges n rem X) old data raw (RecordedStep a.K cur ctr endAt.header endAt.heap final)
      (fun Pins => P.assembly (Pins:=Pins) rem X)
      (fun Pins => RecordedWordStep a.K cur ctr endAt.header endAt.heap final Pins B.publicTemplate)
      (stagePost a.K rows a.cursor old.layer safe (fun i=>(final i).val) H MCap) := by
  let Z := (X.maxWidth+1)*B.widthBase^n
  have bounds (b) (hb : b∈(B.repeat n).recordBounds) : b.1 ≤ a.K ∧ b.2*Z < 2^(16*u^10) :=
    ⟨(Block.component_le Prod.fst (B.bounds_repeat n hb)).trans cap,
     (Nat.mul_le_mul_right Z (Block.component_le Prod.snd (B.bounds_repeat n hb))).trans_lt word⟩
  exact Archive.Journal.reconstruct (B.repeat n) Z B.costFactors.sum bounds (B.factor_bound n)
    rem X (B.repeat_widthCeiling n rem X) a.cursor raw journal age controls old num first
    data safe H MCap seed space B.publicTemplate (B.repeat_supported n) headerDense headerStart le_rfl


private theorem ArchivedSource.transfer {row : NodeRow} {safe : ℕ→Prop} {m n : ℕ→ℕ} {H M : ℕ}
    (r : ArchivedSource row safe m H M) (agree : ∀ x,safe x→n x=m x) : ArchivedSource row safe n H M where
  contents := ⟨r.contents.reads.of_footprint r.contents.footprint agree,
    r.contents.footprint.transfer r.contents.footprint agree,r.contents.halves,r.contents.motifs⟩
  parents nf j := (agree _ (r.ownerCells nf j)).trans (r.parents nf j)
  ownerCells := r.ownerCells

/-- The same decoded history, word visits and archived rows survive the terminal write
when the heap agrees and the archived rows supply the publication's physical inputs. -/
private theorem framed_journal_rows {F : Type} [Field F] {d l w : ℕ} {X : State d l}
    (r : Run F X) (E : r.Records) (C : r.Charges) (O : X.ArchiveSites)
    (data : LayerData O.layer) (raw : List Bool) (K : ℕ) (cur ctr : Word w)
    (ops : List Stage) (c : Cursor) (mid out : Memory w) (J : ∀ Pins : Type, r.Assembler Pins)
    (allow : StaticMotif F → Prop) (safe : ℕ → Prop) (a : NodeArchive)
    (recovered : Recovered r E C O data raw
      (RecordedStep K cur ctr (finish K ops c).header (finish K ops c).heap mid) J
      (fun Pins => RecordedWordStep K cur ctr (finish K ops c).header (finish K ops c).heap mid Pins allow)
      (stagePost K ops c O.layer safe (natural mid) a.halfCap a.motifCap))
    (frame : ∀ i, i < (finish K ops c).heap → out i=mid i)
    (fromRows : ∀ (h : r.plan.History) (path : r.ArchivePath h C O),
      let xs := r.archiveList h C O path data
      records xs = nodeLayers K ops c O.layer →
      (∀ q∈xs, ArchivedSource q safe (natural mid) a.halfCap a.motifCap) → SourceRows a (program xs) out) :
    ∃ (h : r.plan.History) (suffix : List Bool) (path : r.ArchivePath h C O),
      let xs := r.archiveList h C O path data
      r.plan.read (r.codes E) raw=some (h,suffix) ∧ r.FinalNumbered h C O path ∧
      r.ArchiveVisits (RecordedStep K cur ctr (finish K ops c).header (finish K ops c).heap out) h C O path ∧
      (∀ (Pins : Type) (L : X.Words Pins),r.WordVisits
        (RecordedWordStep K cur ctr (finish K ops c).header (finish K ops c).heap out Pins allow)
        h (J Pins).steps L C O path) ∧ records xs=nodeLayers K ops c O.layer ∧
      (r.finalArchive h C O path).1=lastLayer K ops c O.layer ∧ SourceRows a (program xs) out := by
  obtain ⟨h,suffix,path,decoded,numbered,visits,words,spine,terminal,stored⟩ := recovered
  refine ⟨h,suffix,path,decoded,numbered,?_,?_,spine,terminal,fromRows h path spine stored⟩
  · exact Run.ArchiveVisits.mono (RecordedStep.transfer frame) r h C O path visits
  · intro Pins L
    exact r.wordVisits_mono _ _ (RecordedWordStep.transfer frame) h (J Pins).steps L C O path (words Pins L)


private theorem cursor_frame_source_rows {F : Type} [Field F] {d l w : ℕ} {X : State d l}
    (a : NodeArchive) (r : Run F X) (h : r.plan.History) (charges : r.Charges)
    (sites : X.ArchiveSites) (path : r.ArchivePath h charges sites)
    (seed : LayerData sites.layer) (mid out : Memory w) (safe : ℕ → Prop) (rows : List Layers)
    (noChildren : sites.layer.childCount = 0)
    (spine : records (r.archiveList h charges sites path seed) = rows)
    (stored : ∀ row ∈ r.archiveList h charges sites path seed,
      ArchivedSource row safe (natural mid) a.halfCap a.motifCap)
    (agree : ∀ i, safe i → out i = mid i)
    (room : ∀ x, safe x → x < 2^w ∧ stable a rows x ∧
      ∀ i : Fin rows.length, x < a.banks.charges ∨
        a.banks.nodes + 8*((rows.get i).actual.first + (rows.get i).actual.count) ≤ x) :
    SourceRows a (program (r.archiveList h charges sites path seed)) out := by
  apply sourceRows_of_archivedSource a r h charges sites path seed out safe noChildren
    (le_refl a.halfCap) (le_refl a.motifCap)
  · intro row member
    exact ArchivedSource.transfer (stored row member) fun i hi => congrArg Fin.val (agree i hi)
  · rw [spine]
    exact room


variable {F : Type} [Field F] [Fintype F] (B : Block F) {u rem low stride cells tableOffset tariff e : ℕ}
    (shape : PhysicalPinsExpr.Shape)
open scoped Fin.CommRing
set_option quotPrecheck false
local notation "p" => Parameters.cursor B u rem low stride cells shape tableOffset tariff
local notation "W" => (16*u^10)
local notation "n" => (u^8)
local notation "P" => B.repeat n
local notation "k" => (P).charge+rem
local notation "d" => 2^B.exponent 0
local notation "off" => 1+((k+low)+(k+low))
local notation "A" => (p).archive d W
local notation "cur" => ((A).control:Word W)
local notation "ctr" => (((A).control+3:ℕ):Word W)
variable (hk : 2 ≤ (B.repeat (u^8)).charge + rem)
local notation "X" => B.cursorState hk low off cells
local notation "R" => (P).run rem X
local notation "v" => Fintype.card (X).Base
local notation "ss" => (P).directory rem v
local notation "edges" => (P).finalEdges rem v
local notation "N" => (p).nodeArchive A ss W
local notation "O" => (A).cursorSeedSites B hk low off cells rfl rfl
local notation "C" => B.charges n rem X
local notation "z" => (((X).maxWidth+1)*B.widthBase^n)
local notation "qtab" => B.recordTable B.alphabetCap W n rem X le_rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 10000 in
private theorem cursor_journal_space (sites : ℕ) (card : sites = (p).axes)
    (hu : 40 ≤ u) (levels : B.levels+1 ≤ u) (allocation : B.allocations.sum ≤ u)
    (half : low = u^10/2) (depth : k+low ≤ u^10+2*u^6)
    (lim : (A).Limits u cur ((P).directory rem sites) ((P).finalEdges rem sites) (A).pairCapacity) :
    let ops := (P).directory rem sites
    let bank := (p).nodeArchive A ops W
    (cur).val < (ctr).val ∧
      JournalSpace (A).K W bank.halfCap bank.motifCap ops (A).cursor (A).seedLayer
        (fun x => x < (finish (A).K ops (A).cursor).heap ∨ (A).initialRecords ≤ x ∧ x < (A).metadataEnd) ∧
      (finish (A).K ops (A).cursor).header ≤ (A).cursor.dense ∧
      TickWorkspace.base u 20 ≤ (A).cursor.header := by
  subst sites
  intro ops bank
  have geom := Parameters.node_publication_arena B u rem low stride cells shape tableOffset tariff
    hu levels allocation half depth
  have headerBank : bank.headerBase ≤ bank.banks.charges := (Nat.le_add_right _ _).trans geom.header
  have chargeBank : bank.banks.charges ≤ bank.banks.nodes := (Nat.le_add_right _ _).trans geom.chargeEnd
  have nodeBank : bank.banks.nodes < 2^W := lt_of_le_of_lt (Nat.le_add_right _ _) geom.nodeEnd
  have counterRoom : (A).control+3 < 2^W :=
    lt_trans (lt_of_lt_of_le geom.counter (headerBank.trans chargeBank)) nodeBank
  have controlRoom : (A).control < 2^W := lt_of_le_of_lt (Nat.le_add_right _ _) counterRoom
  have controls : (cur).val < (ctr).val := by
    rw [Fin.val_cast_of_lt controlRoom, Fin.val_cast_of_lt counterRoom]
    exact Nat.lt_add_of_pos_right (by decide)
  have denseHeader : (finish (A).K ops (A).cursor).header ≤ (A).cursor.dense := by
    have tables := lim.tables
    rw [Archive.directory_length] at tables
    change (A).seed + 64*(ops.length+2) ≤ (A).cursor.dense at tables
    rw [header_finish, lim.origin]
    omega
  have starts : TickWorkspace.base u 20 ≤ (A).cursor.header := by
    change TickWorkspace.base u 20 ≤ TickWorkspace.base u 20+64
    exact Nat.le_add_right _ _
  refine ⟨controls, ?_, denseHeader, starts⟩
  constructor
  · intro row member
    have span := (geom.span row member).2
    omega
  · exact denseHeader.trans ((Nat.le_add_right _ _).trans lim.raw)
  · exact fun _ _ hi => Or.inl hi
  · exact fun op member => ⟨stage_le_maxRows stageHalves _ ops op member,
      stage_le_maxRows stageMotifs _ ops op member⟩


set_option maxHeartbeats 1600000 in
set_option maxRecDepth 10000 in
/-- The seed and the selected physical row records in the closed navigation RAM give exactly
the source instance consumed by the native node publisher, with the parser's own history. -/
theorem cursor_source_rows (hu : e+40≤u) (half : low=u^10/2) (depth : k+low≤u^10+2*u^6)
    (fixed : directoryCap B≤u) (levels : B.levels+1≤u) (allocation : B.allocations.sum≤u)
    (slot : off*cells*3≤u^e) (word : B.repeatFactor*z<2^W) (bits : ℕ→Bool) {origin out : Memory W}
    (closed : (A).Closed B n rem X bits (qtab word).records origin out)
    («meta» : (A).InitialNodeMetadata (X).graph (finCongr (show k=(A).axes from rfl)) (fun _=>(A).relayWidth) origin)
    (lim : (A).Limits u cur ss edges (A).pairCapacity) (room : (A).TerminalRoom ss edges W) :
    let raw:=List.ofFn (fun j : Fin (A).pairCapacity=>bits j.val)
    ∃ (h : (R).plan.History) (suffix : List Bool) (path : (R).ArchivePath h C O),
      let xs:=(R).archiveList h C O path (A).seedData
      (R).plan.read (qtab word).codes raw=some (h,suffix) ∧ (R).FinalNumbered h C O path ∧
      (R).ArchiveVisits (RecordedStep (A).K cur (((A).control+3:ℕ):Word W) (finish (A).K ss (A).cursor).header
        (finish (A).K ss (A).cursor).heap out) h C O path ∧
      (∀ (Pins : Type) (L : (X).Words Pins),(R).WordVisits (RecordedWordStep (A).K cur ctr
        (finish (A).K ss (A).cursor).header (finish (A).K ss (A).cursor).heap out Pins B.publicTemplate) h
        ((P).assembly rem X).steps L C O path) ∧ records xs=nodeLayers (A).K ss (A).cursor (A).seedLayer ∧
      ((R).finalArchive h C O path).1=lastLayer (A).K ss (A).cursor (A).seedLayer ∧ SourceRows N (program xs) out := by
  intro raw
  let safe := fun x=>x<(finish (A).K ss (A).cursor).heap ∨ (A).initialRecords≤x ∧ x<(A).metadataEnd
  have card : v=(p).axes := Fintype.card_fin k
  have degree : d≤u := by unfold directoryCap at fixed;omega
  obtain ⟨mid,log,ends,frame⟩:=(A).closed_frame B n rem X bits _ closed
  have seed:=cursor_seed_contents B shape hk hu half depth degree slot room raw log «meta»
  have order := (A).cursorSeedSites_numbered B hk low off cells rfl rfl
  obtain ⟨controls,space,headerDense,headerStart⟩ :=
    cursor_journal_space B (u:=u) (rem:=rem) (low:=low) (stride:=stride) (cells:=cells)
      (tableOffset:=tableOffset) (tariff:=tariff) shape v card (by omega) levels allocation half depth lim
  have got := block_journal_rows B (a:=A) (u:=u) («cur»:=cur) («ctr»:=ctr) n rem X le_rfl word
    raw log (by omega) controls O order rfl (A).seedData safe (N).halfCap (N).motifCap
    seed space headerDense headerStart
  have prior (i : ℕ) (hi : i<(finish (A).K ss (A).cursor).heap) : out i=mid i := frame i (Or.inl hi)
  refine framed_journal_rows R (qtab word).records C O (A).seedData raw (A).K cur ctr ss
    (A).cursor mid out (fun Pins => (P).assembly (Pins:=Pins) rem X) B.publicTemplate safe N got prior ?_
  intro h path xs spine stored
  refine cursor_frame_source_rows N R h C O path (A).seedData mid out safe
    (nodeLayers (A).K ss (A).cursor (A).seedLayer) rfl spine stored ?_ ?_
  · intro i hi
    apply frame
    apply hi.elim Or.inl
    intro above
    have age40 : 40 ≤ u := by omega
    have axesDepth : k ≤ u^10+2*u^6 := (Nat.le_add_right k low).trans depth
    have start : (A).control < (A).initialRecords :=
      ((p).initial_space d age40 degree axesDepth).controlBeforeRecords
    right
    change (finish (A).K ss (A).cursor).heap+edges+1 ≤ i
    exact (Nat.succ_le_of_lt room.control).trans (start.le.trans above.1)
  · have loc:=cursor_record_addresses B (rem:=rem) (low:=low) (stride:=stride) (cells:=cells)
      («off»:=tableOffset) (tariff:=tariff) shape (by omega) fixed levels allocation half depth
    let addressFits (sites : ℕ) : Prop :=
      let ops := (P).directory rem sites
      let bank := (p).nodeArchive (A) ops W
      let rows := nodeLayers (A).K ops (A).cursor (A).seedLayer
      ∀ x : ℕ, x < (finish (A).K ops (A).cursor).heap ∨ ((A).initialRecords ≤ x ∧ x < (A).metadataEnd) →
        x < 2^W ∧ stable bank rows x ∧
          ∀ i : Fin rows.length, x < bank.banks.charges ∨
            bank.banks.nodes + 8*((rows.get i).actual.first+(rows.get i).actual.count) ≤ x
    have selected : addressFits (p).axes := loc
    exact (congrArg addressFits card).mpr selected

end

end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open Computability.VPVNP.Compression
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] (B : Block F) {k : ℕ} (hk : 2≤k) (low off slots total : ℕ)

/-- Clipping uses every pair exactly once on cursor layer zero, with empty
intervals on every remaining cursor layer. -/
theorem clippedPairs_sum :
    (∑ z : (B.cursorState hk low off slots).Site,B.clippedPairs hk low off slots total z)=
      min total (2^k*2^low) := by
  let first : Fin k := ⟨0,by omega⟩
  let mass (s : Fin k × BitWord k) : ℕ :=
    let row := s.1.val*2^k+(finFunctionFinEquiv s.2).val
    if row<2^k then min (total-row*2^low) (2^low) else 0
  change (∑ s : Fin k × BitWord k,mass s)=_
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ v : BitWord k,mass (first,v) := by
      apply Finset.sum_eq_single first
      · intro i _ hi
        apply Finset.sum_eq_zero
        intro v _
        have pos : 0 < i.val := Nat.pos_of_ne_zero (fun e=>hi (Fin.ext e))
        have outside : 2^k ≤ i.val*2^k+(finFunctionFinEquiv v).val :=
          (Nat.le_mul_of_pos_left _ pos).trans (Nat.le_add_right ..)
        exact ite_eq_right (Nat.not_lt.mpr outside)
      · simp
    _ = ∑ v : BitWord k,TraceSuffix.pairs total low (finFunctionFinEquiv v).val := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [mass,first,Nat.zero_mul,Nat.zero_add,(finFunctionFinEquiv v).isLt,
        ite_true,TraceSuffix.pairs]
      exact min_comm _ _
    _ = ∑ i : Fin (2^k),TraceSuffix.pairs total low i.val := by
      let lanes : BitWord k ≃ Fin (2^k) := finFunctionFinEquiv
      exact lanes.sum_comp (fun i : Fin (2^k) => TraceSuffix.pairs total low i.val)
    _ = _ := TraceSuffix.pairs_prefix total low (2^k)

end

end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM RAM LinearAlgebra.SpectralBooks.VNP PhysicalStage
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] {d l W : ℕ} {A : State d l}
variable (a : RootArchive) (r : Run F A) (h : r.plan.History) (C : r.Charges)
variable (O : A.ArchiveSites) (p : r.ArchivePath h C O) (m : Memory W)
variable (rows : r.ArchiveRowsStored a.nodeBank (fun u=>(m u).val) h C O p)
variable (zero : O.layer.first=0) (first : a.firstFinal=(r.finalArchive h C O p).1.first)
variable (card : a.rootCount=(r.finalArchive h C O p).1.count)
variable (start pay : A.Site→ℕ)
local notation "N" => nodesOfRun a r h C O p m rows zero first card start pay

def terminalOrder : Fin a.rootCount ≃ (r.plan.finish h).Site :=
  (finCongr card).trans ((r.finalArchive h C O p).2.symm.trans (r.finalSite h))

theorem nodes_work_sum : Team.ticks (N).work a.ids=a.nodeBank.unitWork*r.rootTotal h C start := by
  rw [←r.chargeAt_sum h C start]
  simp only [Team.ticks,ids,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  change (∑ i : Fin a.rootCount,a.nodeBank.unitWork*r.chargeAt h C start (terminalOrder a r h C O p card i))=_
  rw [←Finset.mul_sum,(terminalOrder a r h C O p card).sum_comp]

theorem nodes_pair_sum : Team.ticks (N).pairs a.ids=∑ z,pay z := by
  simp only [Team.ticks,ids,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  let label:=(terminalOrder a r h C O p card)
  let hits (v : (r.plan.finish h).Site):=∑ x : {x // r.plan.destination h x=v},pay x.val
  change (∑ i,hits (label i))=_
  rw [label.sum_comp]
  exact Fintype.sum_fiberwise _ _

end

end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open LinearAlgebra.SpectralBooks.VNP PhysicalStage Computability.VPVNP.BurstRAM
open scoped BigOperators Classical
noncomputable section

/-- The exact work denominator used by the native recurrence includes all
inherited external pairs, each charged in its terminal owner's work row. -/
theorem scheduleFacts_of_native_charges {α : Type*} (a : RootArchive) {W K M : ℕ}
    (work pairs : α → ℕ) (xs : List α)
    (groups : 0<a.groups) (pairPos : 0<a.totalPairs)
    (totalPairs : Team.ticks pairs xs=a.totalPairs)
    (cost : ∀ z∈xs,pairs z<work z ∧ work z≤M) (cap : a.groups*M≤a.totalPairs)
    (groupFits : 4*(Team.ticks work xs*a.totalPairs)<2^W) (slotFits : a.slotBudget/4<2^W)
    (enough : 4*a.groups≤K) (room : 16≤a.slotBudget) (each : 16*M≤a.slotBudget)
    (volume : 256*Team.ticks work xs≤a.slotBudget*K) :
    ScheduleFacts a W (K/(4*a.groups)) work pairs xs := by
  have le (ys : List α) (sub : ∀ z∈ys,z∈xs) : Team.ticks pairs ys≤Team.ticks work ys := by
    induction ys with
    | nil => exact le_rfl
    | cons y ys ih =>
      change pairs y+Team.ticks pairs ys≤work y+Team.ticks work ys
      exact Nat.add_le_add (cost y (sub y (by simp))).1.le (ih (fun z h=>sub z (by simp [h])))
  have lower : a.totalPairs≤Team.ticks work xs := by rw [←totalPairs]; exact le xs (fun _ h=>h)
  have pos (z) (hz : z∈xs) : 0<work z := Nat.zero_lt_of_lt (cost z hz).1
  have scores (z) (hz : z∈xs) := cellScore_le_of_cell_budget work pairs z (cost z hz).2
    ((cost z hz).1.le.trans (cost z hz).2) (cap.trans lower) cap
  refine ⟨groups,pairPos.trans_le lower,pairPos,groupFits,slotFits,pos,totalPairs.le,scores,
    (fun z hz=>(cost z hz).2.trans (by omega)),?_⟩
  obtain ⟨_,flat,bound⟩:=schedule_spec groups (pairPos.trans_le lower) pairPos work pairs xs
    pos le_rfl totalPairs.le scores
  intro b hb
  apply Team.handoff_covers work (a.slotBudget/4) M (K/(4*a.groups)) b ?_
    (group_slot_budget groups enough room each (bound b hb).1 volume)
  intro z hz
  have inxs : z∈xs := by rw [←flat]; exact List.mem_flatten.mpr ⟨b,hb,hz⟩
  exact ⟨pos _ inxs,(cost _ inxs).2.trans (Nat.le_succ _)⟩

set_option Elab.async false in
set_option maxHeartbeats 1600000 in
/-- All numerical rows are the charges of the parsed history and its actual
terminal ownership fibers. The tariff pays for the per-site pair mass. -/
theorem cursor_nodes_bounds {F : Type} [Field F] [Fintype F] (B : Block F)
    {u rem low off slots stride cells e Aexp copies depth W : ℕ}
    (hk : 2 ≤ ((B.repeat (u^8)).charge+rem))
    (a : RootArchive)
    (h : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.History)
    (O : (B.cursorState hk low off slots).ArchiveSites)
    (p : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).ArchivePath h
      (B.charges (u^8) rem (B.cursorState hk low off slots)) O)
    (m : Memory W)
    (rows : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).ArchiveRowsStored
      a.nodeBank (fun addr => (m addr).val) h (B.charges (u^8) rem (B.cursorState hk low off slots)) O p)
    (zero : O.layer.first=0)
    (first : a.firstFinal=(((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).finalArchive
      h (B.charges (u^8) rem (B.cursorState hk low off slots)) O p).1.first)
    (card : a.rootCount=(((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).finalArchive
      h (B.charges (u^8) rem (B.cursorState hk low off slots)) O p).1.count)
    (hu : e+40≤u) (young : 40≤u) (half : low≤u^10/2)
    (axes : ((B.repeat (u^8)).charge+rem)≤u^11) (degree : 2^(B.exponent 0)≤u) (slot : off*slots*3≤u^e)
    (traceCost : TraceBitHeader.seedTraceWork low stride cells copies depth≤2^low*u^e)
    (level : B.levels+1≤u) (coeff : B.costFactors.sum≤u)
    (energy : 4*Real.sqrt B.blockError≤(u:ℝ)) (growth : Real.sqrt B.stageGrowth≤(u:ℝ))
    (peak : B.peakBase≤u) (unit : 0<a.nodeBank.unitWork) (tariff : a.nodeBank.unitWork≤u^e)
    (enough : 146+2*e+26≤Aexp) (clock : 2^(((B.repeat (u^8)).charge+rem)+low)≤2*FoldTrace.hFuel u Aexp)
    (pins : a.totalPairs≤2^(((B.repeat (u^8)).charge+rem)+low)) :
    let nodes := nodesOfRun a ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)) h
      (B.charges (u^8) rem (B.cursorState hk low off slots)) O p m rows zero first card
      (B.seedWork hk low off slots a.totalPairs copies depth stride cells)
      (B.clippedPairs hk low off slots a.totalPairs)
    Team.ticks nodes.pairs a.ids=a.totalPairs ∧
    Team.ticks nodes.work a.ids≤FoldTrace.total u/u^(Aexp-(146+2*e+26)) ∧
    ∀ i, nodes.pairs i<nodes.work i ∧ nodes.work i≤2^((3*u^10+4)/5) := by
  intro nodes
  let state := B.cursorState hk low off slots
  let run := (B.repeat (u^8)).run rem state
  let charges := B.charges (u^8) rem state
  let seed := B.seedWork hk low off slots a.totalPairs copies depth stride cells
  let clipped := B.clippedPairs hk low off slots a.totalPairs
  have scaled : run.rootTotal h (run.scaled a.nodeBank.unitWork charges)
      (fun v => a.nodeBank.unitWork * seed v) ≤ FoldTrace.total u/u^(Aexp-(146+2*e+26)) :=
    B.cursor_total_work (u:=u) (rem:=rem) (low:=low) (off:=off) (slots:=slots)
      (total:=a.totalPairs) (copies:=copies) (depth:=depth) (stride:=stride) (cells:=cells)
      (e:=e) (unitWork:=a.nodeBank.unitWork) (Aexp:=Aexp) young hk axes degree slot traceCost
      level coeff energy growth tariff enough clock h
  have pairsEq := nodes_pair_sum a run h charges O p m rows zero first card seed clipped
  have workEq := nodes_work_sum a run h charges O p m rows zero first card seed clipped
  refine ⟨pairsEq.trans ?_,workEq.le.trans ?_,?_⟩
  · apply (B.clippedPairs_sum hk low off slots a.totalPairs).trans
    apply min_eq_left
    simpa only [Nat.pow_add] using pins
  · exact (run.rootTotal_scaled h charges seed a.nodeBank.unitWork).ge.trans scaled
  · intro i
    let v := runRootSite a run h charges O p card i
    have covers := B.terminal_charge_covers (u^8) rem state h seed clipped
      (B.seedWork_covers hk low off slots a.totalPairs copies depth stride cells) v
    have strict (a b : ℕ) : b < 1+a+b :=
      Nat.lt_add_of_pos_left (Nat.add_pos_left (by decide) a)
    have rowBound : nodes.pairs i < run.chargeAt h charges seed v :=
      (strict (run.terminalIncident h v) (nodes.pairs i)).trans_le covers
    have pos : 0 < u := (by decide : 0 < 40).trans_le young
    have exp : u^e ≤ u^(e+2) := Nat.pow_le_pow_right pos (Nat.le_add_right e 2)
    refine ⟨rowBound.trans_le (Nat.le_mul_of_pos_left _ unit),?_⟩
    change a.nodeBank.unitWork * run.chargeAt h charges seed v ≤ _
    rw [Nat.mul_comm]
    exact B.cursor_terminal_peak (e:=e+2) young ((Nat.add_le_add_left (by decide : 2≤40) e).trans hu)
      half peak (slot.trans exp) hk h seed
      (B.cursor_start_le (e:=e) ((by decide : 4≤40).trans young) hk degree slot traceCost)
      (tariff.trans exp) v

end

end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open LinearAlgebra.SpectralBooks.VNP PhysicalStage RAM Computability.VPVNP.BurstRAM
open scoped BigOperators Classical
noncomputable section

private theorem scheduler_age_bounds {u s : ℕ} (hu : 512≤u) (hs : TraceVolume.cm+2 ≤ s) :
    let M:=2^((3*u^10+4)/5)
    let q:=2^(u^3)
    let T:=2^(u^6)
    let m:=TraceVolume.cap u/4
    1024*M≤2^(u^10-u^4) ∧ 16*M≤ m ∧
      256*(FoldTrace.total u/u^s)≤ m*(q*T) ∧ 4*(FoldTrace.total u*2^(u^10+2*u^6))<2^(16*u^10) ∧
      m/4<2^(16*u^10) := by
  intro M q T m
  have up : 0<u := by omega
  have six : 16≤u^6 := (by omega : 16≤u).trans (Nat.le_self_pow (by decide) _)
  have four : 16≤u^4 := (by omega : 16≤u).trans (Nat.le_self_pow (by decide) _)
  have gap : 16*u^4≤u^10 := (Nat.mul_le_mul_right (u^4) six).trans_eq (Nat.pow_add u 6 4).symm
  have two : u^2≤u^4 := Nat.pow_le_pow_right up (by decide)
  have sixTen : u^6≤u^10 := Nat.pow_le_pow_right up (by decide)
  have threeTen : u^3≤u^10 := Nat.pow_le_pow_right up (by decide)
  have cm : TraceVolume.cm+1≤u := by unfold TraceVolume.cm; omega
  have maxSlot : 64*M≤TraceVolume.cap u := by
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos up)).mpr
    calc (64*M)*u^TraceVolume.cm ≤ (2^6*M)*2^(u^2) :=
            Nat.mul_le_mul_left _ (width_pow_le_two_pow_sq (by omega : TraceVolume.cm≤u))
         _ ≤ _ := by
            dsimp only [M]
            rw [←Nat.pow_add,←Nat.pow_add]
            exact Nat.pow_le_pow_right (by decide) (by omega)
  have fine := diagonal_work_budget (cm:=TraceVolume.cm+1) hu cm hs
  have fb : 2^(u^10)/u^(TraceVolume.cm+1)≤ m := by
    change _≤(2^(u^10)/u^TraceVolume.cm)/4
    rw [Nat.pow_succ u TraceVolume.cm,←Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_left (by omega : 4≤u) (by decide)
  refine ⟨?_,by change 16*M≤TraceVolume.cap u/4;omega,?_,?_,?_⟩
  · change 2^10*2^((3*u^10+4)/5)≤_
    rw [←Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · unfold FoldTrace.total
    rw [show 2^(u^3)*2^(u^10)*2^(u^6)=2^(u^3)*2^(u^6)*2^(u^10) by ac_rfl]
    exact fine.trans (Nat.mul_le_mul_right _ fb)
  · unfold FoldTrace.total
    change 2^2*(((2^(u^3)*2^(u^10))*2^(u^6))*2^(u^10+2*u^6))<_
    simp only [←Nat.pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  · have small : m/4≤2^(u^10) := ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _)).trans
          (Nat.div_le_self _ _)
    exact small.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

section ScalarSchedule
variable {u e Aexp : ℕ}
set_option quotPrecheck false
local notation "W" => 16*u^10
local notation "q" => 2^(u^3)
local notation "T" => 2^(u^6)

/-- Numeric schedule at diagonal scale for any table with the actual aggregate and
peak charges, including intrinsically enumerated histories before RAM publication. -/
theorem cursor_schedule_scalars (a : RootArchive) (shape : PhysicalPinsExpr.Shape) (eval : ℕ)
    (billedWork billedPairs : Fin a.rootCount→ℕ) (age : 512≤u)
    (save : 146+2*e+26+(TraceVolume.cm+2)≤Aexp)
    (pins : 2*shape.halfBits≤2^(u^10+2*u^6)) (chunks : 0<shape.chunks)
    (chunk : shape.bits=2^(u^10-u^4)) (pairs : a.totalPairs=2*shape.halfBits)
    (groups : a.groups=1024*(2*shape.chunks)) (budget : a.slotBudget=TraceVolume.cap u/4)
    (timetable : T=4*(a.groups*eval))
    (total : Team.ticks billedPairs a.ids=a.totalPairs ∧ Team.ticks billedWork a.ids≤FoldTrace.total u/u^(Aexp-(146+2*e+26)) ∧
      ∀i,billedPairs i<billedWork i ∧ billedWork i≤2^((3*u^10+4)/5)) :
    ScheduleFacts a W (eval*q) billedWork billedPairs a.ids := by
  let M:=2^((3*u^10+4)/5)
  obtain ⟨cellPair,cellWork,gain,word,slotWord⟩:=scheduler_age_bounds (s:=Aexp-(146+2*e+26)) age (by omega)
  have grp : 0<a.groups := by rw [groups];omega
  have bitPos : 0<shape.bits := by rw [chunk]; exact Nat.two_pow_pos _
  have pairPos : 0<a.totalPairs := by
    rw [pairs,PhysicalPinsExpr.Shape.halfBits];exact Nat.mul_pos (by decide) (Nat.mul_pos chunks bitPos)
  have cfit : a.groups*M≤a.totalPairs := by
    rw [groups,pairs,PhysicalPinsExpr.Shape.halfBits,chunk]
    calc 1024*(2*shape.chunks)*M=(2*shape.chunks)*(1024*M) := by ring
         _ ≤ _ := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (2*shape.chunks) cellPair
  have clockPos : 0<T:=Nat.two_pow_pos _
  have ePos : 0<eval := by
    by_contra! hz
    have z : eval=0 := by omega
    exact (Nat.ne_of_gt clockPos) (by simpa only [z,Nat.mul_zero] using timetable)
  have days : 4*a.groups≤T := by rw [timetable,←Nat.mul_assoc];exact Nat.le_mul_of_pos_right _ ePos
  have slotsEq : q*T/(4*a.groups)=eval*q := by
    rw [timetable,show q*(4*(a.groups*eval))=(eval*q)*(4*a.groups) by ring,
      Nat.mul_div_cancel _ (Nat.mul_pos (by decide) grp)]
  rw [←slotsEq]
  refine scheduleFacts_of_native_charges a billedWork billedPairs a.ids grp pairPos total.1
    (fun i _=>total.2.2 i) cfit ?_ (by simpa only [budget] using slotWord)
    (days.trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))) ?_ ?_ ?_
  · have wide := Nat.mul_le_mul total.2.1 (by
      rw [pairs];exact pins : a.totalPairs≤2^(u^10+2*u^6))
    exact (Nat.mul_le_mul_left 4 (wide.trans (Nat.mul_le_mul_right _ (Nat.div_le_self _ _)))).trans_lt word
  · rw [budget]
    have := Nat.two_pow_pos ((3*u^10+4)/5)
    omega
  · simpa only [budget] using cellWork
  · rw [budget]
    exact (Nat.mul_le_mul_left 256 total.2.1).trans gain


end ScalarSchedule

set_option Elab.async false in
set_option maxHeartbeats 1600000 in
/-- The physical stage branch satisfies each native scheduler obligation for its exact
work and pair arrays. Its number of slots is the product of the true evaluation ticks
per group and the number of parallel teams. -/
theorem cursor_schedule_facts {F : Type} [Field F] [Fintype F] (B : Block F)
    {u rem low off slots stride cells e Aexp copies depth : ℕ}
    (hk : 2 ≤ ((B.repeat (u^8)).charge+rem))
    (a : RootArchive)
    (h : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.History)
    (O : (B.cursorState hk low off slots).ArchiveSites)
    (p : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).ArchivePath h
      (B.charges (u^8) rem (B.cursorState hk low off slots)) O)
    (m : Memory (16*u^10))
    (rows : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).ArchiveRowsStored
      a.nodeBank (fun addr => (m addr).val) h (B.charges (u^8) rem (B.cursorState hk low off slots)) O p)
    (zero : O.layer.first=0)
    (first : a.firstFinal=(((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).finalArchive
      h (B.charges (u^8) rem (B.cursorState hk low off slots)) O p).1.first)
    (card : a.rootCount=(((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).finalArchive
      h (B.charges (u^8) rem (B.cursorState hk low off slots)) O p).1.count)
    (shape : PhysicalPinsExpr.Shape) (eval : ℕ)
    (age : 512≤u) (hu : e+40≤u) (half : low≤u^10/2) (axes : ((B.repeat (u^8)).charge+rem)≤u^11)
    (traceDepth : ((B.repeat (u^8)).charge+rem)+low≤u^10+2*u^6) (degree : 2^(B.exponent 0)≤u) (slot : off*slots*3≤u^e)
    (traceCost : TraceBitHeader.seedTraceWork low stride cells copies depth≤2^low*u^e)
    (level : B.levels+1≤u) (coeff : B.costFactors.sum≤u)
    (energy : 4*Real.sqrt B.blockError≤(u:ℝ)) (growth : Real.sqrt B.stageGrowth≤(u:ℝ))
    (peak : B.peakBase≤u) (unit : 0<a.nodeBank.unitWork) (tariff : a.nodeBank.unitWork≤u^e)
    (save : 146+2*e+26+(TraceVolume.cm+2)≤Aexp) (clock : 2^(((B.repeat (u^8)).charge+rem)+low)≤2*FoldTrace.hFuel u Aexp)
    (pins : 2*shape.halfBits≤2^(((B.repeat (u^8)).charge+rem)+low)) (chunks : 0<shape.chunks)
    (chunk : shape.bits=2^(u^10-u^4)) (pairs : a.totalPairs=2*shape.halfBits)
    (groups : a.groups=1024*(2*shape.chunks)) (budget : a.slotBudget=TraceVolume.cap u/4)
    (timetable : 2^(u^6)=4*(a.groups*eval)) :
    let nodes := nodesOfRun a ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)) h
      (B.charges (u^8) rem (B.cursorState hk low off slots)) O p m rows zero first card
      (B.seedWork hk low off slots a.totalPairs copies depth stride cells)
      (B.clippedPairs hk low off slots a.totalPairs)
    ScheduleFacts a (16*u^10) (eval*2^(u^3)) nodes.work nodes.pairs a.ids := by
  intro nodes
  have age₀ : 40 ≤ u := (by decide : 40 ≤ 512).trans age
  have paid : 146+2*e+26 ≤ Aexp :=
    (Nat.le_add_right (146+2*e+26) (TraceVolume.cm+2)).trans save
  have pairsBound : a.totalPairs ≤ 2^(((B.repeat (u^8)).charge+rem)+low) := pairs.le.trans pins
  have total := cursor_nodes_bounds (u:=u) (rem:=rem) (low:=low) (off:=off) (slots:=slots)
    (stride:=stride) (cells:=cells) (e:=e) (Aexp:=Aexp) (copies:=copies) (depth:=depth)
    B hk a h O p m rows zero first card hu age₀ half axes degree slot traceCost level coeff
    energy growth peak unit tariff paid clock pairsBound
  exact cursor_schedule_scalars (u:=u) (Aexp:=Aexp) (e:=e) a shape eval nodes.work nodes.pairs
    age save (pins.trans (Nat.pow_le_pow_right (by decide) traceDepth)) chunks chunk pairs
    groups budget timetable total

end


end ThreeFlat.Diagonal.NavigationPass.RootArchive

end OAI
