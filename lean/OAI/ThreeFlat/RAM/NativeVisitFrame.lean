import OAI.ThreeFlat.Diagonal.NavigationSlotSchedule
import OAI.ThreeFlat.RAM.TickLedgerTerminal

namespace OAI
/-! # The chronological selected loop's physical controls and unchanged directories -/
namespace ThreeFlat.RAM.HistoryNodeDirectory.Selected
open Computability.VPVNP.BurstRAM
open scoped BigOperators
variable {W n count : ℕ}

/-- Read the same S45 table of absolute node ordinals when the run length
is expressed using the final archived layer. -/
def Directory.atCount (D : Directory W n) (width : n=count) : Directory W count where
  root i:=D.root (i.cast width.symm)
  owner:=D.owner
  group:=D.group
  slot:=D.slot

theorem Directory.picked_atCount (D : Directory W n) (width : n=count) (i : ℕ) :
    picked (D.atCount width) i=picked D i := by
  cases width
  rfl

theorem Directory.price_atCount (D : Directory W n) (width : n=count) (cost : ℕ→ℕ) :
    (∑ i:Fin count,if picked (D.atCount width) i.val then cost i.val else 0)=
      ∑ i:Fin n,if picked D i.val then cost i.val else 0 := by
  cases width
  rfl


end ThreeFlat.RAM.HistoryNodeDirectory.Selected

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM RAM NavigationPass RootArchive HistoryStageBody.Physical
open HistoryNodeDirectory HistoryNodeDirectory.Selected TickWorkspace
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W : ℕ}
variable (a : RootArchive) (N : Nodes a) (slots : ℕ) (group slot : Word W)
local notation "u" => a.age
local notation "n" => a.rootsTotal
local notation "D" => a.selectedDirectory N slots group slot
local notation "data" => ownerData W u
local notation "step" => stride u

/-- Natural addresses for the five reads performed at each true chronological
site. Every address survives mounting the compact H reader in sectors 53–58. -/
private theorem guard_words (size : PublishSizes a W) (i : Fin n) (j : Fin 5) :
    (addresses data D i j).val<base u 53 ∧ (addresses data D i j).val≠base u 18 ∧
      (addresses data D i j).val≠base u 18+1 := by
  let rank:=N.chronology.root i
  let ptr : Fin 5→ℕ:=![base u 45+i.val,TickPhysicalABI.directory u 1+2*rank,
    TickPhysicalABI.directory u 1+2*rank+1,base u 1,base u 1+3]
  have rlt : rank<a.rootCount:=by
    have h:=N.chronology.root_lt i
    rw [N.first] at h
    simpa [rootsTotal] using h
  have counted : a.rootCount≤n:=by dsimp only [rootsTotal];omega
  have fixed:=size.fixed
  have nodes:=size.nodes
  have wide : 51*step<2^W:=size.address
  have ii:=i.isLt
  have ptrFit (t : Fin 5) : ptr t<2^W:=by
    fin_cases t
    · change 46*step+i.val<2^W;omega
    · change 12*step+1*(step/4)+2*rank<2^W;omega
    · change 12*step+1*(step/4)+2*rank+1<2^W;omega
    · change 2*step<2^W;omega
    · change 2*step+3<2^W;omega
  have addr (t : Fin 5) : addresses data D i t=(ptr t:Word W):=by
    fin_cases t <;> simp [addresses,ptr,selectedDirectory,ownerData,rank,Nat.two_mul,Nat.cast_add]
  rw [addr,Fin.val_cast_of_lt (ptrFit j)]
  fin_cases j
  · change 46*step+i.val<54*step ∧ 46*step+i.val≠19*step ∧ 46*step+i.val≠19*step+1
    omega
  · change 12*step+1*(step/4)+2*rank<54*step ∧ 12*step+1*(step/4)+2*rank≠19*step ∧
      12*step+1*(step/4)+2*rank≠19*step+1
    omega
  · change 12*step+1*(step/4)+2*rank+1<54*step ∧ 12*step+1*(step/4)+2*rank+1≠19*step ∧
      12*step+1*(step/4)+2*rank+1≠19*step+1
    omega
  · change 2*step<54*step ∧ 2*step≠19*step ∧ 2*step≠19*step+1
    omega
  · change 2*step+3<54*step ∧ 2*step+3≠19*step ∧ 2*step+3≠19*step+1
    omega

/-- On the evaluation phase the fourth S1 word is the actual zero-based
team/time slot and the first word is the genuine group. -/
theorem evaluation_slot {teams t : ℕ} (clock : TickChronology.Clock) (k : Fin teams)
    (active : clock.phase t=.evaluate) :
    clock.group t<clock.groups ∧ TickClockWords.values clock 0 teams k.val t 3<clock.evaluateTicks*teams := by
  have phase:=active
  unfold TickChronology.Clock.phase at phase
  split at phase <;> try contradiction
  split at phase <;> try contradiction
  split at phase <;> try contradiction
  split at phase <;> try contradiction
  rename_i live
  have groupIndex : clock.group t<clock.groups:=by
    apply (Nat.div_lt_iff_lt_mul clock.duration_pos).mpr
    change t<clock.beginTick+clock.groups*clock.groupDuration at live
    omega
  have within:=phase
  unfold TickChronology.Clock.within at within
  split at within <;> try contradiction
  split at within <;> try contradiction
  split at within
  · rename_i small
    have pos : clock.offset t-(clock.chunks+1)<clock.evaluateTicks:=by omega
    have mul:=Nat.mul_le_mul_right teams pos
    rw [Nat.succ_mul] at mul
    refine ⟨groupIndex,?_⟩
    change (clock.offset t-(clock.chunks+1))*teams+k.val<clock.evaluateTicks*teams
    have card:=k.isLt
    omega
  · split at within <;> contradiction

/-- Every root chosen by the actual S1/S11 scan is a picked chronological
node. The same finite list proves the word-width fit of its native ordinal. -/
theorem cursor_root_picked {ι : Type*} (size : PublishSizes a W) (vs : List ι)
    (rank : ι→ℕ) (id : ι→Fin n) (index : ∀ v∈vs,(id v).val=a.firstFinal+rank v)
    (m : Memory W) (groupWord : m (base u 1)=group) (slotWord : m (base u 1+3)=slot)
    (schedule : TickTerminalRoot.rootIds u (a.summaryHeader N) (a.scheduledOwner N slots) m=vs.map rank) :
    ∀ i : Fin vs.length,rank (vs.get i)<2^W ∧ picked D (id (vs.get i)).val=true := by
  intro i
  let v:=vs.get i
  let t:=rank v
  have mem : v∈vs:=List.get_mem _ _
  have here : t∈TickTerminalRoot.rootIds u (a.summaryHeader N) (a.scheduledOwner N slots) m:=by
    rw [schedule]
    exact List.mem_map.mpr ⟨v,mem,rfl⟩
  change t∈(List.range a.rootCount).filter
    (TickSlotLookup.matchesOwner (a.scheduledOwner N slots) (m (base u 1)) (m (base u 1+3))) at here
  obtain ⟨range,hit⟩:=List.mem_filter.mp here
  have bounded:=List.mem_range.mp range
  have cnt : a.rootCount≤n:=by dsimp only [rootsTotal];omega
  have nodes:=size.nodes
  have word : 51*step<2^W:=size.address
  have fit : t<2^W:=by omega
  have pickedOwner : a.scheduledOwner (W:=W) N slots t=(group,slot):=by
    simpa only [TickSlotLookup.matchesOwner,groupWord,slotWord,decide_eq_true_eq] using hit
  have terminal_rank {total : ℕ} (c : Chronology total) (node : Fin total) (rankValue : ℕ)
      (position : node.val = c.firstFinal + rankValue) : c.root node = rankValue := by
    have terminal : ¬ node.val < c.firstFinal := by omega
    rw [Chronology.root, dite_eq_right terminal]
    omega
  have num : N.chronology.root (id v) = t :=
    terminal_rank N.chronology (id v) t (by rw [N.first]; exact index v mem)
  refine ⟨fit, ?_⟩
  change picked (a.selectedDirectory N slots group slot) (id v).val = true
  have within : (id v).val < a.rootsTotal := (id v).isLt
  simp only [picked, dite_eq_left within, decide_eq_true_eq]
  change a.scheduledOwner N slots (((N.chronology.root (id v) : ℕ) : Word W).val) = (group, slot)
  rwa [num, Fin.val_cast_of_lt fit]

/-- The published S6 root count, the owner rows, and all three S11
descriptor words remain available after the group interval packing. -/
theorem cursor_directory_words {K : Type*} [Field K] [Fintype K] {B : TickActiveROM.Layout} {p H J : ℕ}
    {f : Contraction.Fits (TickWeightedBank.shape K p H J) W} {clock : TickChronology.Clock}
    (x : TickActiveROM.CellInput B clock f) (ls : List Layers) (g : Fin a.initialLanes→Fin a.groups)
    (m prepared : Memory W) (post : a.preparedInput x N slots ls m g prepared)
    (sched : ScheduleFacts a W slots N.work N.pairs a.ids) (size : PublishSizes a W) (room : OutputRoom a W)
    (sources : a.sourceRows=base u 46) (grp : a.groupRows=base u 47)
    (fit : B.bounds+4≤2^W) (boundsEnd : B.bounds+4≤a.statsBase) (reqEnd : B.auxRequest+8*B.bits≤a.statsBase) :
    TickTerminalRoot.directoryInput u (a.summaryHeader N) (a.scheduledOwner N slots) prepared ∧
      ∀ i : Fin 3,prepared (TickPhysicalABI.directory u 3+i.val)=(a.rootWords i:Word W) := by
  have fixed:=size.fixed
  have nodes:=size.nodes
  have lanes:=size.lanes
  have groupSize:=size.groups
  have chunks:=size.chunks
  have lower : base u 5+4*a.initialLanes≤a.statsBase:=by change 6*step+4*a.initialLanes≤7*step;omega
  have count : a.statsBase+8≤base u 7:=by change 7*step+8≤8*step;omega
  have groupEnd : base u 8+a.groups≤a.ownerBase:=by change 9*step+a.groups≤12*step+1*(step/4);omega
  obtain ⟨branch,out,first,done,rfl⟩:=post
  refine ⟨a.directory_read x N slots g (a.mounted ls m) branch out first done sched room lower count groupEnd fit boundsEnd reqEnd,?_⟩
  intro i
  let ptr:=TickPhysicalABI.directory u 3+i.val
  have ii:=i.isLt
  have whereAt : ptr=12*step+3*(step/4)+i.val:=rfl
  have head : a.statsBase≤ptr:=by change 7*step≤_;omega
  rw [filled_high x out .evaluate ptr fit (boundsEnd.trans head) (reqEnd.trans head)]
  have keep:=a.output_frame g branch out done ptr
  exact (keep (.inr (by change 6*step+4*a.initialLanes≤ptr;omega))
    (.inr (by change 8*step+a.chunkBits≤ptr;omega)) (.inr (by change 9*step+a.groups≤ptr;omega))
    (.inl (by rw [sources];change ptr<47*step;omega))
    (.inl (by rw [grp];change ptr<48*step;omega))).trans (first.2.2.1 i)

/-- The S12 slices and S13 records of all sites fit simultaneous addresses.
This also bounds every S11 lookup at the two-word terminal owner index. -/
theorem cursor_visit_space (size : PublishSizes a W) (_age : 1≤u) (sites : n≤2^(u^10-u^4)) :
    base u 46<2^W ∧ n ≤ step ∧ (∀ i,2*((D).root i).val+2 ≤ step/4) ∧
      ∀ i : Fin n,base u 12+(i.val+1)*(volume u)^2≤base u 13 ∧ base u 13+8*i.val+8≤base u 14 := by
  have fixed:=size.fixed
  have nodes:=size.nodes
  have word : 51*step<2^W:=size.address
  have cnt : a.rootCount≤n:=by dsimp only [rootsTotal];omega
  have vpos : 1≤volume u:=Nat.two_pow_pos _
  have lengthV : n≤volume u:=sites.trans (Nat.pow_le_pow_right (by decide:0<2) (Nat.sub_le ..))
  refine ⟨by change 47*step<2^W;omega,by omega,?_,?_⟩
  · intro j
    have above:=N.chronology.root_lt j
    rw [N.first] at above
    have rlt : N.chronology.root j<a.rootCount:=by simpa [rootsTotal] using above
    change 2*((N.chronology.root j:Word W).val)+2 ≤ step/4
    rw [Fin.val_cast_of_lt (show N.chronology.root j<2^W by omega)]
    omega
  · intro i
    have hi:=i.isLt
    have slice : (i.val+1)*(volume u)^2 ≤ step := by
      calc _ ≤ volume u*(volume u)^2:=Nat.mul_le_mul_right _ (i.isLt.trans_le lengthV)
           _ = (volume u)^3:=by ring
           _ ≤ (volume u)^4:=Nat.pow_le_pow_right vpos (by decide)
    change 13*step+(i.val+1)*(volume u)^2≤14*step ∧ 14*step+8*i.val+8≤15*step
    omega

omit [Field F] in
/-- The only remaining fields of NativeVisits after this lemma are the
per-site native dispatch and the seed/shrink/refresh message it publishes. -/
theorem cursor_visit_frame (size : PublishSizes a W) (prepared warm : Memory W)
    (directory : Recorded data D prepared) (header : (a.summaryHeader N).stored u prepared)
    (rootStart : (prepared (TickPhysicalABI.directory u 3)).val=a.firstFinal)
    (frame : ∀ z,z<base u 53→warm z=prepared z)
    (values : Fin n→NodeValue F) (records : ∀ i,(values i).stream+4*(values i).net.cells≤base u 14)
    (ends : ∀ i,(values i).ext+(values i).external≤base u 14)
    (cost : ℕ→ℕ) :
    VisitFrame u warm D values (TickTerminalRoot.slotKeep u) cost
      (17+24*n+∑ i : Fin n, if picked D i.val then cost i.val else 0) := by
  have fixed:=size.fixed
  have nodes:=size.nodes
  have word : 51*step<2^W:=size.address
  have nf : n<2^W:=by omega
  have counted : a.rootCount≤n:=by dsimp only [rootsTotal];omega
  have ptr : (data 0).val=base u 18:=by
    change ((19*step:ℕ):Word W).val=19*step
    exact Fin.val_cast_of_lt (by omega)
  have bump : (data 0+1).val=base u 18+1:=by
    change (((19*step:ℕ):Word W)+1).val=19*step+1
    have addWord (k : ℕ) : (k : Word W) + 1 = ((k+1 : ℕ) : Word W) := (Nat.cast_succ k).symm
    exact (congrArg (fun x : Word W => x.val) (addWord (19*step))).trans
      (Fin.val_cast_of_lt (show 19*step+1 < 2^W by omega))
  have firstPtr : (data 4).val=TickPhysicalABI.directory u 3:=by
    change ((12*step+3*(step/4):ℕ):Word W).val=_
    exact Fin.val_cast_of_lt (by omega)
  have nPtr : (data 5).val=base u 6+1:=by
    change ((7*step+1:ℕ):Word W).val=_
    exact Fin.val_cast_of_lt (by omega)
  have firstWord : (warm (data 4).val).val=a.firstFinal:=by
    rw [firstPtr,frame _ (by change 12*step+3*(step/4)<54*step;omega),rootStart]
  have countWord : (warm (data 5).val).val=a.rootCount:=by
    rw [nPtr,frame _ (by change 7*step+1<54*step;omega)]
    have h:=header 1
    change prepared (base u 6+1)=(a.rootCount:Word W) at h
    rw [h]
    exact Fin.val_cast_of_lt (counted.trans_lt nf)
  refine ⟨?_,by rw [firstWord,countWord];rfl,nf,?_,?_,?_,?_,?_,by omega,?_,?_⟩
  · intro i j
    rw [frame _ ((guard_words a N slots group slot size i j).1)]
    exact directory i j
  · rw [bump,ptr];omega
  · intro j
    fin_cases j
    · change (data 4).val≠(data 0).val
      rw [firstPtr,ptr];change 12*step+3*(step/4)≠19*step;omega
    · change (data 5).val≠(data 0).val
      rw [nPtr,ptr];change 7*step+1≠19*step;omega
  · intro i j;rw [ptr,bump]
    exact (guard_words a N slots group slot size i j).2
  · intro z saved;rw [ptr,bump]
    change z<13*step ∨ 20*step≤z at saved
    change z≠19*step ∧ z≠19*step+1
    omega
  · intro i z read
    rw [ptr]
    have ix:=i.isLt
    have row:=records i
    have endpoint:=ends i
    change (14*step+8*i.val≤z ∧ z<14*step+8*i.val+6) ∨
      ((values i).stream≤z ∧ z<(values i).stream+4*(values i).net.cells) ∨
      ((values i).ext≤z ∧ z<(values i).ext+(values i).external) at read
    change (values i).stream+4*(values i).net.cells≤15*step at row
    change (values i).ext+(values i).external≤15*step at endpoint
    change z≠19*step
    omega
  · change 19*step<2^W;omega
  · rw [←cost_fiber D (fun i=>cost i.val)]

omit [Field F] in
/-- The exact final-layer count is the one consumed by the typed chronological
loop, even when the two native root counters use separate header fields. -/
theorem cursor_frame_at_count {count : ℕ} (width : n=count) (size : PublishSizes a W)
    (prepared warm : Memory W) (directory : Recorded data D prepared)
    (header : (a.summaryHeader N).stored u prepared) (first : (prepared (TickPhysicalABI.directory u 3)).val=a.firstFinal)
    (frame : ∀ z,z<base u 53→warm z=prepared z)
    (v : Fin count→NodeValue F) (rows : ∀i,(v i).stream+4*(v i).net.cells≤base u 14)
    (ends : ∀i,(v i).ext+(v i).external≤base u 14) (cost : ℕ→ℕ) :
    VisitFrame u warm ((D).atCount width) v (TickTerminalRoot.slotKeep u) cost
      (17+24*count+∑i : Fin count,if picked ((D).atCount width) i.val then cost i.val else 0) := by
  subst count
  exact cursor_visit_frame a N slots group slot size prepared warm directory header first frame v rows ends cost


end
end ThreeFlat.Diagonal.TraceBitHeader

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM RAM PhysicalStage NavigationPass RootArchive TickChronology HistoryNodeDirectory
open HistoryNodeDirectory.Selected TickWorkspace
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W d l : ℕ} {X : State d l}
variable (a : RootArchive) (r : Run F X) (h : r.plan.History) (C : r.Charges) (start pay : X.Site→ℕ)
  (c : Clock) (teams : ℕ) (O : X.ArchiveSites) (path : r.ArchivePath h C O)
  (card : a.rootCount=(r.finalArchive h C O path).1.count)
  (m : Memory W) (rows : r.ArchiveRowsStored a.nodeBank (fun z=>(m z).val) h C O path)
  (zero : O.layer.first=0) (first : a.firstFinal=(r.finalArchive h C O path).1.first)
  (num : r.FinalNumbered h C O path)
local notation "N" => nodesOfRun a r h C O path m rows zero first card start pay
local notation "slots" => (c.evaluateTicks*teams)
local notation "head" => a.typedHeader r h C start
local notation "owner" => a.typedOwner r h C start pay W slots
local notation "ranks" => terminalRank r h
local notation "index" => r.archivePlanIndex h C O path

include num in
/-- Read every root label against the directory that the accepted history
actually published. The result uses the typed head and owner chosen before
the warm slot memory, and the genuine final-layer array length. -/
theorem cursor_warm_labels (g : Fin a.groups) (j : Fin slots) (prepared warm : Memory W)
    (room : PublishSizes a W) (gf : a.groups≤2^W) (sf : slots≤2^W)
    (sched : ScheduleFacts a W slots (N).work (N).pairs a.ids)
    (cg : prepared (base a.age 1)=(g.val:Word W)) (cs : prepared (base a.age 1+3)=(j.val:Word W))
    (dir : TickTerminalRoot.directoryInput a.age (a.summaryHeader N) (a.scheduledOwner (W:=W) N slots) prepared)
    (words : ∀ i:Fin 3,prepared (TickPhysicalABI.directory a.age 3+i.val)=(a.rootWords i:Word W))
    (frame : ∀ z,z<base a.age 53→warm z=prepared z) :
    let line:=a.teamRoots r h C start pay c teams g.val j.val
    let D:=a.selectedDirectory N slots (g.val:Word W) (j.val:Word W)
    let eqn : a.rootsTotal =
      (r.finalArchive h C O path).1.first + (r.finalArchive h C O path).1.count :=
      congrArg₂ Nat.add first card
    TickTerminalRoot.directoryInput a.age head owner warm ∧
    (warm (TickPhysicalABI.directory a.age 3)).val=(r.finalArchive h C O path).1.first ∧
    TickTerminalRoot.rootIds a.age head owner warm=line.map ranks ∧
    ∀i:Fin line.length,ranks (line.get i)<2^W ∧ picked (D.atCount eqn) (index (line.get i)).val=true := by
  intro line D eqn
  have hs:=room.fixed
  have ns:=room.nodes
  have cnt : a.rootCount≤a.rootsTotal:=by unfold rootsTotal;omega
  have ownerFit : 2 * (a.summaryHeader N).roots ≤ stride a.age / 4 := by
    change 2 * a.rootCount ≤ stride a.age / 4
    omega
  have ids:=a.teamRoots_numbers r h C start pay c teams O path card m rows zero first num sched gf sf g j
    prepared cg cs
  have atFirst:=first_word a room prepared words
  have ⟨loaded,firstSet,chosen,_⟩:=TickTerminalRoot.warm_directory (u:=a.age) (stop:=0)
    (a.summaryHeader N) (a.scheduledOwner (W:=W) N slots) prepared warm (by omega) ownerFit (Nat.zero_le _)
    frame dir a.firstFinal atFirst (line.map ranks) ids.symm
  have observ:=a.ranked_observables r h C start pay O path card m rows zero first num slots
  rw [observ.2.2.1,observ.2.2.2]
  refine ⟨loaded,firstSet.trans first,chosen,?_⟩
  let root:=fun v=>(index v).cast eqn.symm
  have ord (z) (_ : z∈line) : (root z).val=a.firstFinal+ranks z:=
    physical_rank r h C O path a first num z
  intro i
  have selected:=cursor_root_picked a N slots (g.val:Word W) (j.val:Word W) room line ranks root ord
    prepared cg cs ids.symm i
  rw [Directory.picked_atCount]
  exact selected

end
end ThreeFlat.Diagonal.TraceBitHeader

end OAI
