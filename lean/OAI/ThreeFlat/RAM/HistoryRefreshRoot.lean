import OAI.ThreeFlat.RAM.HistoryRefreshVacantArm

namespace OAI
/-! # Refresh party roster, snapshots, and root construction -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

set_option maxRecDepth 6000

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W p a b : ℕ} {F : Type*}
variable [CommRing F]

def privateStage (A : HistoryGatherBody.Layout) (input : Memory W) :=
  HistoryMotifJoin.headerImage (privateHeader A W) A.privateStarts 9 input

def afterRaw (A : HistoryGatherBody.Layout) (pre : List ℕ) (stage : Memory W)
    (pair gather : ℕ→Memory W→Memory W) :=
  pre.foldl (fun m j=>gather j (pair j m)) (privateStage (withMotif A 0) stage)

section Roster
variable (A : HistoryGatherBody.Layout) (node : ℕ) (winner : Fin A.party.parties)
  (id : ((Fin 3→Bool)→F)→ℕ) (stage occupiedPair occupiedGather : Memory W)

def choosePair (j : ℕ) (input : Memory W) :=
  if j=winner.val then occupiedPair else afterVacantPair (rawArm A j).party node id input

def chooseMap (j : ℕ) (input : Memory W) :=
  if j=winner.val then occupiedGather else vacantMap (rawArm A j) input

def entryOf (j : ℕ) := afterRaw A (List.range j) stage (choosePair A node winner id occupiedPair)
  (chooseMap A winner occupiedGather)

private theorem before_range {n j : ℕ} {pre tail : List ℕ} (loc : List.range n=pre++j::tail) :
    pre=List.range j ∧ j<n := by
  have inrange : j<n:=List.mem_range.mp (by rw [loc];simp)
  have len : pre.length<n := by have h:=congrArg List.length loc;simp at h;omega
  have atj := congrArg (fun l : List ℕ=>l[pre.length]?) loc
  have r : (List.range n)[pre.length]?=some pre.length := by
    rw [List.getElem?_eq_getElem (by simpa using len),List.getElem_range]
  have q : (pre++j::tail)[pre.length]?=some j := by rw [List.getElem?_append_right (by omega)];simp
  change (List.range n)[pre.length]?=(pre++j::tail)[pre.length]? at atj
  rw [r,q] at atj
  have eq : pre.length=j := Option.some.inj atj
  have t:=congrArg (List.take pre.length) loc
  have e : (List.range n).take pre.length=List.range pre.length := by
    simp [List.take_range,Nat.min_eq_left len.le]
  have f : (pre++j::tail).take pre.length=pre := by simp
  change (List.range n).take pre.length=(pre++j::tail).take pre.length at t
  rw [e,f,eq] at t
  exact ⟨t.symm,inrange⟩

def choosePairCost (activeTicks j : ℕ) :=
  if j=winner.val then activeTicks else vacantPairCost (rawArm A j) (entryOf A node winner id stage occupiedPair occupiedGather j)
def chooseMapCost (activeTicks j : ℕ) :=
  if j=winner.val then activeTicks else vacantMapCost (rawArm A j) W

omit [CommRing F] in
/-- All actual raw party invocations in ascending order. The elected branch starts at
the chronological state reached by the preceding absent arms, which are executed in full. -/
theorem arm_roster (pairTicks gatherTicks : ℕ)
    (activePair : (HistoryPartyPair.procedure W (rawArm A winner.val).party).Exec
      (entryOf A node winner id stage occupiedPair occupiedGather winner.val) occupiedPair pairTicks)
    (activeMap : (HistoryGatherBody.procedure W (rawArm A winner.val)).Exec occupiedPair occupiedGather gatherTicks)
    (off : ∀ j : Fin A.party.parties,j≠winner→VacantRoom (rawArm A j.val) node id
      (entryOf A node winner id stage occupiedPair occupiedGather j.val)) :
    ∀ before j tail,List.range A.party.parties=before++j::tail →
    let pairs:=choosePair A node winner id occupiedPair
    let maps:=chooseMap A winner occupiedGather
    let mid:=afterRaw A before stage pairs maps
    (HistoryPartyPair.procedure W (rawArm A j).party).Exec mid (pairs j mid)
      (choosePairCost A node winner id stage occupiedPair occupiedGather pairTicks j) ∧
    (HistoryGatherBody.procedure W (rawArm A j)).Exec (pairs j mid) (maps j (pairs j mid))
      (chooseMapCost (W:=W) A winner gatherTicks j) := by
  intro before j tail where_
  obtain ⟨eq,bound⟩:=before_range where_
  subst before
  by_cases isWinner : j=winner.val
  · subst j
    simp only [choosePair,chooseMap,choosePairCost,chooseMapCost,ite_true,entryOf]
    exact ⟨@activePair,@activeMap⟩
  · have prior:=vacant_arm (rawArm A j) node id (entryOf A node winner id stage occupiedPair occupiedGather j)
      (off ⟨j,bound⟩ (fun h=>isWinner (congrArg Fin.val h)))
    simpa only [choosePair,chooseMap,choosePairCost,chooseMapCost,ite_eq_right isWinner,entryOf] using prior

def beforeWinner := (List.range winner.val).foldl (fun m j=>vacantPass (rawArm A j) node id m)
  (privateStage (withMotif A 0) stage)

omit [CommRing F] in
/-- The starting memory of the live receipt is defined independently of that receipt.
Every earlier party is absent and has already executed its two empty batches. -/
theorem winner_entry : entryOf A node winner id stage occupiedPair occupiedGather winner.val=
    beforeWinner A node winner id stage := by
  have fixed (l : List ℕ) (off : ∀ j∈l,j≠winner.val) (m : Memory W) :
      l.foldl (fun u k=>chooseMap A winner occupiedGather k (choosePair A node winner id occupiedPair k u)) m=
      l.foldl (fun u k=>vacantPass (rawArm A k) node id u) m := by
    induction l generalizing m with
    | nil=>rfl
    | cons j rest ih=>
      have absent:=off j (List.mem_cons_self ..)
      simp only [List.foldl_cons,choosePair,chooseMap,ite_eq_right absent]
      exact ih (fun z hz=>off z (List.mem_cons_of_mem _ hz)) _
  exact fixed _ (fun j hj=>Nat.ne_of_lt (List.mem_range.mp hj)) _

end Roster

section Snapshot
variable (A : HistoryGatherBody.Layout) (node : ℕ) (winner : Fin A.party.parties) (L : Tree F a) (R : Tree F b)
  (wire : Fin (a+b)→BitSource 0 p) (id : ((Fin 3→Bool)→F)→ℕ)
local notation "src" => HistoryPartyPair.atPair (rawArm A winner.val).party node

/-- The three live sectors of the one elected party are the joined row stream, its
four-word root and the geometric pin map. Sector three is the ensuing private map output. -/
structure WinnerImage (mem : Memory W) : Prop where
  rows : HistoryCompiledRows.Records id (pair L R).compile (src 0) mem
  header : ∀ j : Fin 4,mem (src 1+j.val)=(Info.words ⟨src 0,a+b,L.rows+R.rows,L.bits+R.bits⟩ j:Word W)
  pins : ∀ x : Fin (a+b), mem (src 2+x.val)=(BitLayout.sourceAddress (wire x):Word W)

def winnerAddress (x : ℕ) : Prop :=
  (src 0≤x ∧ x<src 0+4*(pair L R).compile.cells) ∨ (src 1≤x ∧ x<src 1+4) ∨
    (src 2≤x ∧ x<src 2+(a+b))

omit [CommRing F] in
theorem WinnerImage.retain {before after : Memory W}
    (read : WinnerImage A node winner L R wire id before)
    (keep : ∀ x,winnerAddress A node winner L R x→after x=before x) :
    WinnerImage A node winner L R wire id after := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    rw [keep _ (.inl (by have := i.isLt;have := j.isLt;omega))]
    exact read.rows i j
  · intro j
    rw [keep _ (.inr (.inl (by have := j.isLt;omega)))]
    exact read.header j
  · intro x
    rw [keep _ (.inr (.inr (by have := x.isLt;omega)))]
    exact read.pins x

omit [CommRing F] in
/-- Only the elected map scan populates the three live sectors. Every later raw
arm has another slot number, even when the elected slot is the first or last. -/
theorem image_after_parties (stage : Memory W) (pairs gather : ℕ→Memory W→Memory W)
    (elected : let mid:=afterRaw A (List.range winner.val) stage pairs gather
      WinnerImage A node winner L R wire id (gather winner.val (pairs winner.val mid)))
    (vacant : ∀ j : Fin A.party.parties,winner.val<j.val→
      let mid:=afterRaw A (List.range j.val) stage pairs gather
      ∀ x,winnerAddress A node winner L R x → gather j.val (pairs j.val mid) x=mid x) :
    WinnerImage A node winner L R wire id (afterRaw A (List.range A.party.parties) stage pairs gather) := by
  have loop (k : ℕ) (bound : k≤A.party.parties) (done_ : winner.val<k) :
      WinnerImage A node winner L R wire id (afterRaw A (List.range k) stage pairs gather) := by
    induction k with
    | zero=>omega
    | succ k ih=>
      have step : afterRaw A (List.range (k+1)) stage pairs gather=
          gather k (pairs k (afterRaw A (List.range k) stage pairs gather)) := by
        simp [afterRaw,List.range_succ]
      rw [step]
      by_cases atWinner : k=winner.val
      · subst k;exact elected
      · have gt : winner.val<k := by omega
        apply (ih (by omega) gt).retain
        exact vacant ⟨k,by omega⟩ gt
  exact loop A.party.parties le_rfl winner.isLt

omit [CommRing F] in
/-- The actual final map write preserves the preceding pair's factor stream and root.
The geometry scan's own output theorem supplies the third page. -/
theorem winner_from_gather (input : Memory W) (plan : HistoryGatherExecution.Plan W)
    (rows : HistoryCompiledRows.Records id (pair L R).compile (src 0) input)
    (header : ∀ j : Fin 4,input (src 1+j.val)=(Info.words ⟨src 0,a+b,L.rows+R.rows,L.bits+R.bits⟩ j:Word W))
    (pins : ∀ x : Fin (a+b),HistoryGatherExecution.output (rawArm A winner.val) plan input (src 2+x.val)=
      (BitLayout.sourceAddress (wire x):Word W))
    (away : ∀ x,(src 0≤x ∧ x<src 0+4*(pair L R).compile.cells) ∨ (src 1≤x ∧ x<src 1+4) →
      let J:=rawArm A winner.val
      (x<J.temp ∨ J.temp+(HistoryGatherBody.fields (W:=W) J).length≤x) ∧
      (∀ q j,j<HistoryGatherExecution.cap J q→x<HistoryGatherBody.srcBase J q j ∨
        HistoryGatherBody.srcBase J q j+plan.width q j≤x) ∧
      (x<plan.gatherBase ∨ plan.gatherBase+plan.gatherCount≤x)) :
    WinnerImage A node winner L R wire id (HistoryGatherExecution.output (rawArm A winner.val) plan input) := by
  have keep (x : ℕ) (live : (src 0≤x ∧ x<src 0+4*(pair L R).compile.cells) ∨ (src 1≤x ∧ x<src 1+4)) :=
    HistoryGatherExecution.output_away (rawArm A winner.val) plan input x (away x live).1
      (away x live).2.1 (away x live).2.2
  refine ⟨?_,?_,pins⟩
  · intro i j
    rw [keep _ (.inl (by have:=i.isLt;have:=j.isLt;omega))]
    exact rows i j
  · intro j
    rw [keep _ (.inr (by have:=j.isLt;omega))]
    exact header j

end Snapshot

def resultTree (L : Tree F a) (R : Tree F b) (wire : Fin (a+b)→BitSource 0 p) : Tree F p :=
  .join 0 1 (fun _=>a+b) (fun _=>wire) (fun _=>pair L R)

section Root
variable (A : HistoryGatherBody.Layout) (node : ℕ) (winner : Fin A.party.parties)
  (L : Tree F a) (R : Tree F b) (wire : Fin (a+b)→BitSource 0 p) (id : ((Fin 3→Bool)→F)→ℕ)
  (mem : Memory W)
local notation "C" => withMotif A 0
local notation "src" => HistoryPartyPair.atPair (rawArm A winner.val).party node
local notation "dst" => resultBank C node true
local notation "K" => groupHub C mem true node p 0 1
local notation "B" => groupBuild C true K mem

def rootLink : Child := ⟨src 1,src 3,10,(C).party.seed+64+7+4*(C).party.parties⟩
def rootHeader (pins current : ℕ) : HistoryJoinScan.Header ℕ := ⟨src 0,dst 0,src 3,pins,current,0⟩
def rootMap : Tape.MapRow := ⟨10,(rootLink A node winner).operand,src 2,0,0⟩

/-- Four-word data supplied to the actual child-selecting group header. -/
structure RootInput (pins : ℕ) (raw : ℕ→ℕ) : Prop where
  link : ∀ j : Fin 4,raw ((C).party.seed+64+7+j.val)=(rootLink A node winner).words j
  child : ∀ j : Fin 4,raw (src 1+j.val)=(Info.words ⟨src 0,pins,(pair L R).compile.cells,(pair L R).compile.internal⟩ j)

private theorem child_zero_from_words (hub : HistoryBoundedJoin.Hub) (raw : ℕ → ℕ) (link : Child)
    (cols : ∀ j : Fin 4, raw (hub.children+j.val)=link.words j) :
    HistoryBoundedJoin.child hub raw 0=link := by
  cases link with
  | mk nodePtr mapPtr op argPtr =>
    change Child.mk (raw (hub.children+0)) (raw (hub.children+1))
      (raw (hub.children+2)) (raw (hub.children+3)) = _
    rw [show raw (hub.children+0)=nodePtr from cols 0,
      show raw (hub.children+1)=mapPtr from cols 1,
      show raw (hub.children+2)=op from cols 2,
      show raw (hub.children+3)=argPtr from cols 3]

omit [CommRing F] in
theorem RootInput.childPtr {raw : ℕ→ℕ} (disk : RootInput A node winner L R (a+b) raw) :
    HistoryBoundedJoin.child K raw 0=rootLink A node winner :=
  child_zero_from_words K raw (rootLink A node winner) disk.link

omit [CommRing F] in
theorem RootInput.commands {raw : ℕ→ℕ} (disk : RootInput A node winner L R (a+b) raw) :
    let q:=rootHeader A node winner (a+b) p
    command K raw 0 false= ![(rootLink A node winner).operand,q.pins,10,0,0,0,q.pins+(a+b)] ∧
    command K raw 0 true= ![A.party.arguments,q.dest,1,0,0,0,q.dest+4*(pair L R).compile.cells] ∧
    HistoryBoundedJoin.arguments K raw 0= ![q.source,q.dest,q.pins,q.oldPins,q.newPins,q.offset,q.dest+4*(pair L R).compile.cells] := by
  have link:=RootInput.childPtr A node winner L R (p:=p) mem disk
  have inc : HistoryBoundedJoin.read (rootLink A node winner).node raw =
      ⟨src 0,a+b,(pair L R).compile.cells,(pair L R).compile.internal⟩ := by
    change Info.mk (raw (src 1+0)) (raw (src 1+1)) (raw (src 1+2)) (raw (src 1+3)) = _
    rw [show raw (src 1+0)=src 0 from disk.child 0,
      show raw (src 1+1)=a+b from disk.child 1,
      show raw (src 1+2)=(pair L R).compile.cells from disk.child 2,
      show raw (src 1+3)=(pair L R).compile.internal from disk.child 3]
  simp only [command,HistoryBoundedJoin.arguments,link,inc,moved,offset,total,
    Finset.range_zero,Finset.sum_empty,Nat.mul_zero,Nat.add_zero]; exact ⟨rfl,rfl,rfl⟩

omit [CommRing F] in
/-- The selected mask and the cursor supply the real linked group header. -/
theorem root_image (read : WinnerImage A node winner L R wire id mem)
    (cursor : (HistoryNodePorts.id (C).nodePorts).value (fun _=>0) mem (fun _=>0)=(node:Word W))
    (ports : let t:=HistoryGatherBody.selected C mem;t.oldBits+t.newBits=(p:Word W))
    (free : mem ((((C).privateStarts+8:ℕ):Word W).val)=0)
    (live : ((C).party.motif:Word W)<HistoryGatherBody.wordAt mem (HistoryGatherBody.selected C mem).kernel 3)
    (mask : (HistoryGatherBody.wordAt mem (HistoryGatherBody.selected C mem).incident 5).val=2^winner.val)
    (small : 2^(C).party.parties<2^W) (two : 2<2^W)
    (childFits : src 1+1<2^W) (room : (C).party.seed+64+(HistoryMotifJoin.rows C W true).length<2^W) :
    (∀ j : Fin 6,(B).input ((B).layout.hub+j.val)=((K).words j:Word W)) ∧
    (B).input ((B).layout.hub+6)=(dst 1:Word W) ∧
    (∀ j : Fin 4,(B).input ((K).children+j.val)=((rootLink A node winner).words j:Word W)) ∧
    (∀ j : Fin 3,(B).input ((rootLink A node winner).operand+j.val)=
      ((![src 3,a+b,src 2] j:ℕ):Word W)) := by
  obtain ⟨count,which⟩:=single_role C mem winner live mask
  have cap : 1≤(C).party.parties := by have := winner.isLt;change 1≤A.party.parties;omega
  have source (idx : ℕ) : sourceBank C node true 0 (role C mem 0) idx = src idx := by
    rw [which]; rfl
  have fit (i : Fin 1) : sourceBank C node true i.val (role C mem i.val) 1+1<2^W := by
    have eq : i=0 := Subsingleton.elim _ _
    subst i
    change sourceBank C node true 0 (role C mem 0) 1+1<2^W
    rw [source]
    exact childFits
  have link : groupLink C mem true node 0=rootLink A node winner := by
    change Child.mk (sourceBank C node true 0 (role C mem 0) 1)
      (sourceBank C node true 0 (role C mem 0) 3) 10 _ = _
    rw [source,source]; rfl
  have pin : mem (src 1+1)=((a+b:ℕ):Word W) := read.header 1
  have argv : groupArgs C mem true node 0 =
      ![(src 3 : Word W),((a+b : ℕ) : Word W),(src 2 : Word W)] := by
    change ![(sourceBank C node true 0 (role C mem 0) 3 : Word W),
      mem (sourceBank C node true 0 (role C mem 0) 1+1),
      (sourceBank C node true 0 (role C mem 0) 2 : Word W)] = _
    simp only [source,pin]
  let H:=GroupRead.of_values C true mem node p 0 1 cursor ports (fun _=>free) (fun _=>count.symm)
    (by simp) cap small two fit
  obtain ⟨header,dest,links,args⟩:=GroupRead.group_image C H room
  refine ⟨header,dest,?_,?_⟩
  · intro j
    have row := links (0:Fin 1) j
    change (B).input ((K).children+(4*0+j.val)) = ((groupLink C mem true node 0).words j : Word W) at row
    simp only [Nat.mul_zero, Nat.zero_add] at row
    rwa [link] at row
  · intro j
    have arg := args (0:Fin 1) j
    change (B).input ((groupLink C mem true node 0).operand+j.val) = groupArgs C mem true node 0 j at arg
    rw [link,argv] at arg
    fin_cases j <;> exact arg

omit [CommRing F] in
/-- The zero-child prefix of the singleton group produces zero row and hidden offsets. -/
private theorem pair_cells : (pair L R).compile.cells=L.rows+R.rows := by
  change (∑ i : Fin 2,(pairNetwork L R i).cells)=_
  rw [Fin.sum_univ_two]
  change L.compile.cells+R.compile.cells=_
  simp only [compiled_rows]

omit [CommRing F] in
private theorem pair_bits : (pair L R).compile.internal=L.bits+R.bits := by
  change 0+(∑ i : Fin 2,(pairNetwork L R i).internal)=_
  rw [Nat.zero_add,Fin.sum_univ_two]
  change L.compile.internal+R.compile.internal=_
  simp only [compiled_bits]

def inBank (lo len x : ℕ) := lo≤x ∧ x<lo+len

/-- Which words must persist through the three scratch writes of the singleton root join. -/
def rootAddress (x : ℕ) :=
  inBank (B).layout.hub 7 x ∨ inBank (K).children 4 x ∨ inBank (rootLink A node winner).operand 3 x ∨
    winnerAddress A node winner L R x

structure PrepAway (P : HistoryBoundedBody.Build W) (x : ℕ) : Prop where
  seed : x<P.layout.seed ∨ P.layout.seed+9≤x
  command : x<P.layout.commands ∨ P.layout.commands+14*P.hub.argc≤x
  arguments : x<P.hub.arguments ∨ P.hub.arguments+7*P.hub.argc≤x

theorem PrepAway.keeps {P : HistoryBoundedBody.Build W} {x : ℕ} (frame : PrepAway P x) :
    P.seeded x=P.input x ∧ P.commands x=P.input x ∧ P.entered x=P.input x := by
  have seed : ¬(P.layout.seed≤x ∧ x<P.layout.seed+9) := by have := frame.seed;omega
  have cmd : ¬(P.layout.commands≤x ∧ x<P.layout.commands+14*P.hub.argc) := by have := frame.command;omega
  have args : ¬(P.hub.arguments≤x ∧ x<P.hub.arguments+7*P.hub.argc) := by have := frame.arguments;omega
  simp [HistoryBoundedBody.Build.seeded,HistoryBoundedBody.Build.commands,HistoryBoundedBody.Build.entered,
    fillSegment,seed,cmd,args]

local notation "q" => rootHeader A node winner (a+b) p
local notation "M" => rootMap A node winner
local notation "N" => fun _ : Fin 1=>(pair L R).compile
local notation "MP" => fun _ : Fin 1=>wire
local notation "qa" => fun _ : Fin 1=>q
local notation "ma" => fun _ : Fin 1=>M
local notation "ops" => Tape.tape (W:=W) N MP id qa

/-- Root-bank width and separation conditions. All maps and gate rows use the actual
private sectors of the single elected party. -/
structure RootBanksRoom : Prop where
  prep : ∀ x,rootAddress A node winner L R (p:=p) mem x→PrepAway B x
  boot : ∀ x,winnerAddress A node winner L R x→x<(B).layout.hub ∨ (B).layout.hub+(HistoryMotifJoin.rows C W true).length≤x
  linkFit : ∀ j,(rootLink A node winner).words j<2^W
  infoFit : ∀ j,(Info.words ⟨src 0,a+b,L.rows+R.rows,L.bits+R.bits⟩ j)<2^W
  mapArgFit : (M).arg+4<2^W
  cmdProtected : ∀ (side : Bool) (j : Fin 7),(B).protectedAt N qa ((B).layout.commands+(7*side.toNat+j.val))
  argsProtected : ∀ j : Fin 6,(B).protectedAt N qa ((K).arguments+j.val)
  operandsProtected : ∀ j : Fin 3,(B).protectedAt N qa ((M).arg+j.val)
  rowsProtected : ∀ r : Fin (pair L R).compile.cells,∀ j : Fin 4,(B).protectedAt N qa (src 0+(4*r.val+j.val))
  pinProtected : ∀ j : Fin (a+b),(B).protectedAt N qa (src 2+j.val)

omit [CommRing F] in
theorem root_banks (read : WinnerImage A node winner L R wire id mem)
    (linkWords : ∀ j : Fin 4,(B).input ((K).children+j.val)=((rootLink A node winner).words j:Word W))
    (argWords : ∀ j : Fin 3,(B).input ((M).arg+j.val)=((![src 3,a+b,src 2] j:ℕ):Word W))
    (source : (B).Source ops) (room : RootBanksRoom A node winner L R (p:=p) mem) :
    (B).Banks N MP id qa ma := by
  have original (x : ℕ) (w : winnerAddress A node winner L R x) : (B).input x=mem x := by
    have f:=room.boot x w
    change x<(C).party.seed+64 ∨ (C).party.seed+64+(HistoryMotifJoin.rows C W true).length≤x at f
    have off : ¬((C).party.seed+64≤x ∧ x<(C).party.seed+64+(HistoryMotifJoin.rows C W true).length):=by omega
    simp [groupBuild,HistoryMotifJoin.headerImage,fillSegment,off]
  have roots (j : Fin 4) : winnerAddress A node winner L R (src 1+j.val) :=
    .inr (.inl (by have := j.isLt;omega))
  have links (j : Fin 4) : rootAddress A node winner L R (p:=p) mem ((K).children+j.val) :=
    .inr (.inl (by dsimp [inBank]; have := j.isLt;omega))
  have disk (ν : Memory W) (keep : ∀ x,rootAddress A node winner L R (p:=p) mem x→ν x=(B).input x) :
      RootInput A node winner L R (a+b) (numeric ν) := by
    constructor
    · intro j
      change (ν ((K).children+j.val)).val=_
      rw [keep _ (links j),linkWords,Fin.val_cast_of_lt (room.linkFit j)]
    · intro j
      rw [numeric,keep _ (.inr (.inr (.inr (roots j)))),original _ (roots j),read.header j,
        Fin.val_cast_of_lt (room.infoFit j),pair_cells,pair_bits]
  have commands:=RootInput.commands A node winner L R (p:=p) mem
    (disk (B).seeded (fun x h=>(room.prep x h).keeps.1))
  have arguments:=RootInput.commands A node winner L R (p:=p) mem
    (disk (B).commands (fun x h=>(room.prep x h).keeps.2.1))
  have ctl:(B).control.val=(B).layout.seed+7:=Fin.val_cast_of_lt (by have:=source.seedRoom;omega)
  refine ⟨rfl,?_,source.commandRoom.le,.inl source.order.2,?_,?_,?_,?_,?_,?_,?_,?_,
    source.argumentsRoom.le,?_,?_,?_,?_⟩
  · rw [ctl]
    exact ((B).entered_word ops source 7).trans ((B).seeded_word 7)
  · intro i side j
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    simpa using room.cmdProtected side j
  · intro i
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    change command K (numeric (B).seeded) 0 false 2 = 10
    exact congrFun commands.1 (2 : Fin 7)
  · intro i
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    change command K (numeric (B).seeded) 0 false 0 = (rootLink A node winner).operand
    exact congrFun commands.1 (0 : Fin 7)
  · exact fun _=>room.mapArgFit
  · intro i j ok
    have hj:j.val<3:=ok.resolve_right (by change ¬(10:ℕ)=8; decide)
    exact room.operandsProtected ⟨j.val,hj⟩
  · intro i j ok
    have hj:j.val<3:=ok.resolve_right (by change ¬(10:ℕ)=8; decide)
    let k : Fin 3:=⟨j.val,hj⟩
    have loc : rootAddress A node winner L R (p:=p) mem ((M).arg+k.val) :=
      .inr (.inr (.inl (by
        change (rootLink A node winner).operand ≤ (rootLink A node winner).operand+j.val ∧
          (rootLink A node winner).operand+j.val < (rootLink A node winner).operand+3
        omega)))
    rw [(room.prep _ loc).keeps.2.2,argWords k]
    fin_cases j <;> first
      | rfl
      | exact False.elim ((by decide : ¬3<3) hj)
      | exact False.elim ((by decide : ¬4<3) hj)
  · intro i j
    have loc : winnerAddress A node winner L R (src 2+j.val):=.inr (.inr (by have:=j.isLt;omega))
    change (B).entered (src 2+j.val)=_
    rw [(room.prep _ (.inr (.inr (.inr loc)))).keeps.2.2,original _ loc]
    exact read.pins j
  · exact fun _ _ j=>room.pinProtected j
  · intro i j
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    change (B).protectedAt N qa ((K).arguments+(7*0+j.val))
    simpa only [Nat.mul_zero,Nat.zero_add] using room.argsProtected j
  · intro i j
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    change HistoryBoundedJoin.arguments K (numeric (B).commands) 0 j.castSucc = _
    rw [arguments.2.2]
    fin_cases j <;> rfl
  · exact fun _ r j=>room.rowsProtected r j
  · intro i r j
    have loc : winnerAddress A node winner L R (src 0+(4*r.val+j.val)) :=
      .inl (by have := r.isLt;have:=j.isLt;change _≤_ ∧ _<_+4*(pair L R).compile.cells;omega)
    change (B).entered (src 0+(4*r.val+j.val))=_
    rw [(room.prep _ (.inr (.inr (.inr loc)))).keeps.2.2,original _ loc]
    exact read.rows r j

/-- Numeric space used by the two real jobs of the singleton group. -/
structure RootSpace : Prop where
  width : 2+(a+b)<2^W
  mapOut : src 3+(a+b)≤2^W
  mapIn : src 2+(a+b)≤2^W
  mapBase : src 2<2^W
  mapRows : src 3+(a+b)≤dst 0 ∨ dst 0+4*(pair L R).compile.cells≤ src 3
  cursorMap : (B).control.val<src 3 ∨ src 3+(a+b)≤(B).control.val
  cursorRows : (B).control.val<dst 0 ∨ dst 0+4*(pair L R).compile.cells≤(B).control.val
  childStream : src 0+4*(pair L R).compile.cells≤2^W
  small : ∀ i j,HistoryCompiledRows.metadata id (pair L R).compile i j<2^W
  stream : 4*(pair L R).compile.cells≤A.party.V

omit [CommRing F] in
theorem root_resident (read : WinnerImage A node winner L R wire id mem)
    (linkWords : ∀ j : Fin 4,(B).input ((K).children+j.val)=((rootLink A node winner).words j:Word W))
    (argWords : ∀ j : Fin 3,(B).input ((M).arg+j.val)=((![src 3,a+b,src 2] j:ℕ):Word W))
    (source : (B).Source ops) (room : RootBanksRoom A node winner L R (p:=p) mem)
    (space : RootSpace A node winner L R (p:=p) id mem) (dest : (B).outputBase=dst 1) :
    (B).Resident N MP id qa ma (dst 0) := by
  have bank:=root_banks A node winner L R wire id mem read linkWords argWords source room
  have next : dst 1=dst 0+A.party.V := by
    change bankAddr C node ((C).party.motif+2) 0 3 1 = bankAddr C node ((C).party.motif+2) 0 3 0 + A.party.V
    unfold bankAddr HistoryScratch.atWord HistoryScratch.sector
    dsimp only [withMotif]
    ring
  apply (B).resident_of_banks N MP id qa ma bank (dst 0) (by have:=source.small;omega)
    (fun _=>Or.inr (Or.inl rfl)) (fun _=>space.mapBase) (fun _=>space.mapOut)
    (fun _ _=>space.mapIn) (fun _ _=>space.mapRows) (fun _=>space.cursorMap) (fun _=>space.cursorRows)
    (fun _=>space.childStream) (fun _=>space.width)
  · intro i
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    simp [rootHeader]
  · intro i
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    simp [rootHeader,Tree.before]
  · exact fun _=>space.small
  · right
    rw [dest,next]
    apply Nat.add_le_add_left
    change 4*(∑ _ : Fin 1,(pair L R).compile.cells)≤A.party.V
    simpa using space.stream

/-- The physical addresses in the original root header that survive the ready-tape scan. -/
structure RootStay : Prop where
  hub : ∀ j : Fin 7,(B).layout.hub+j.val≠(B).control.val ∧
    ∀ u∈ops,(B).layout.hub+j.val<u.start ∨ u.finish≤(B).layout.hub+j.val
  child : ∀ j : Fin 4,src 1+j.val≠(B).control.val ∧ ∀ u∈ops,src 1+j.val<u.start ∨ u.finish≤ src 1+j.val
  link : (K).children≠(B).control.val ∧ ∀ u∈ops,(K).children<u.start ∨ u.finish≤(K).children

omit [CommRing F] in
theorem root_result (read : WinnerImage A node winner L R wire id mem)
    (hubWords : ∀ j : Fin 6,(B).input ((B).layout.hub+j.val)=((K).words j:Word W))
    (target : (B).input ((B).layout.hub+6)=(dst 1:Word W))
    (linkWords : ∀ j : Fin 4,(B).input ((K).children+j.val)=((rootLink A node winner).words j:Word W))
    (hubFit : ∀ j,(K).words j<2^W) (destFit : dst 1<2^W)
    (room : RootBanksRoom A node winner L R (p:=p) mem) (stay : RootStay A node winner L R wire id mem) :
    let m:=numeric ((B).reached ops)
    (B).outputBase=dst 1 ∧
    (m (B).layout.hub=dst 0 ∧ m ((B).layout.hub+1)=p ∧ m ((B).layout.hub+2)=0 ∧ m ((B).layout.hub+3)=1) ∧
    let root:=m (m ((B).layout.hub+4))
    m (root+2)=(pair L R).compile.cells ∧ m (root+3)=(pair L R).compile.internal := by
  have held {x} (known : rootAddress A node winner L R (p:=p) mem x)
      (off : x≠(B).control.val ∧ ∀ u∈ops,x<u.start ∨ u.finish≤x) :
      (B).reached ops x=(B).input x :=
    (HistoryReadyTape.after_away (B).control ops (B).entered x off.1 off.2).trans (room.prep x known).keeps.2.2
  have hub (j : Fin 6) : numeric ((B).reached ops) ((B).layout.hub+j.val)=(K).words j := by
    have saved := held (x:=(B).layout.hub+j.val)
      (.inl (by dsimp [inBank];have:=j.isLt;omega)) (stay.hub j.castSucc)
    rw [numeric,saved,
      hubWords,Fin.val_cast_of_lt (hubFit j)]
  have childptr : numeric ((B).reached ops) (K).children=src 1 := by
    have hw:=linkWords (0:Fin 4)
    have fit:=room.linkFit (0:Fin 4)
    simp only [Fin.val_zero,Nat.add_zero] at hw
    change ((B).reached ops (K).children).val=_
    rw [held (.inr (.inl (by dsimp [inBank];omega))) stay.link,hw,Fin.val_cast_of_lt fit]
    rfl
  have root (j : Fin 4) : numeric ((B).reached ops) (src 1+j.val)=
    Info.words ⟨src 0,a+b,L.rows+R.rows,L.bits+R.bits⟩ j := by
    have x : winnerAddress A node winner L R (src 1+j.val):=.inr (.inl (by have:=j.isLt;omega))
    have outside:=room.boot _ x
    have off : ¬((C).party.seed+64≤ src 1+j.val ∧ src 1+j.val<(C).party.seed+64+(HistoryMotifJoin.rows C W true).length) := by
      change src 1+j.val<(C).party.seed+64 ∨
        (C).party.seed+64+(HistoryMotifJoin.rows C W true).length≤ src 1+j.val at outside
      omega
    have boot : (B).input (src 1+j.val)=mem (src 1+j.val) := by
      simp only [groupBuild,HistoryMotifJoin.headerImage,fillSegment,ite_eq_right off]
    rw [numeric,held (.inr (.inr (.inr x))) (stay.child j),boot,read.header j,Fin.val_cast_of_lt (room.infoFit j)]
  dsimp only
  refine ⟨?_,⟨?_,hub 1,hub 2,hub 3⟩,?_⟩
  · rw [HistoryBoundedBody.Build.outputBase,numeric,target,Fin.val_cast_of_lt destFit]
  · have first : (K).words (0:Fin 6)=dst 0 := rfl
    simpa only [Fin.val_zero,Nat.add_zero] using (hub 0).trans first
  · have hp : numeric ((B).reached ops) ((B).layout.hub+4)=(K).children:=hub 4
    rw [hp,childptr,pair_cells,pair_bits]
    exact ⟨root 2,root 3⟩

/-- Scalar bounds needed by the physical root tape. All persisted values and the two
commands themselves are obtained from the generated group header. -/
structure RootSourceRoom : Prop where
  small : 14<2^W
  cap : A.party.parties≤2^W
  seed : (B).layout.seed+9<2^W
  header : (B).layout.hub+7<2^W
  order : (B).layout.seed+9≤(B).layout.commands ∧ (B).layout.commands+14≤(K).arguments
  cmd : (B).layout.commands+14<2^W
  args : (K).arguments+7<2^W
  link : (K).children+4≤2^W
  child : src 1+3<2^W
  result : dst 1+4<2^W
  resultAway : ∀ x,rootAddress A node winner L R (p:=p) mem x→ x<dst 1 ∨ dst 1+4≤x
  controlAway : HistoryReadyTape.Away (B).layout.seed 9 ops ∧ HistoryReadyTape.Away (B).layout.commands 14 ops
  limits : ∀ j∈ops,j.finish<2^W

omit [CommRing F] in
theorem root_source (read : WinnerImage A node winner L R wire id mem)
    (hubWords : ∀ j : Fin 6,(B).input ((B).layout.hub+j.val)=((K).words j:Word W))
    (target : (B).input ((B).layout.hub+6)=(dst 1:Word W))
    (linkWords : ∀ j : Fin 4,(B).input ((K).children+j.val)=((rootLink A node winner).words j:Word W))
    (hubFit : ∀ j,(K).words j<2^W)
    (room : RootBanksRoom A node winner L R (p:=p) mem) (stay : RootStay A node winner L R wire id mem)
    (small : RootSourceRoom A node winner L R wire id mem) : (B).Source ops := by
  let relevant (x : ℕ):=rootAddress A node winner L R (p:=p) mem x
  have atHub (j : Fin 7) : relevant ((B).layout.hub+j.val):=.inl (by dsimp [inBank];have:=j.isLt;omega)
  have atLink (j : Fin 4) : relevant ((K).children+j.val):=.inr (.inl (by dsimp [inBank];have:=j.isLt;omega))
  have atChild (j : Fin 4) : winnerAddress A node winner L R (src 1+j.val):=.inr (.inl (by have:=j.isLt;omega))
  have fromChild (j : Fin 4) : relevant (src 1+j.val):=.inr (.inr (.inr (atChild j)))
  have disk (μ : Memory W)
      (one : ∀ j : Fin 4,μ ((K).children+j.val)=(B).input ((K).children+j.val))
      (two : ∀ j : Fin 4,μ (src 1+j.val)=(B).input (src 1+j.val)) :
      RootInput A node winner L R (a+b) (numeric μ) := by
    constructor
    · intro j
      change (μ ((K).children+j.val)).val=_
      rw [one,linkWords,Fin.val_cast_of_lt (room.linkFit j)]
    · intro j
      have f:=room.boot _ (atChild j)
      have off : ¬((C).party.seed+64≤ src 1+j.val ∧ src 1+j.val<(C).party.seed+64+(HistoryMotifJoin.rows C W true).length) := by
        change src 1+j.val<(C).party.seed+64 ∨
          (C).party.seed+64+(HistoryMotifJoin.rows C W true).length ≤ src 1+j.val at f
        omega
      have original : (B).input (src 1+j.val)=mem (src 1+j.val):=by
        simp only [groupBuild,HistoryMotifJoin.headerImage,fillSegment,ite_eq_right off]
      rw [numeric,two,original,read.header,Fin.val_cast_of_lt (room.infoFit j),pair_cells,pair_bits]
  have first:=disk (B).seeded (fun j=>(room.prep _ (atLink j)).keeps.1) (fun j=>(room.prep _ (fromChild j)).keeps.1)
  have second:=disk (B).commands (fun j=>(room.prep _ (atLink j)).keeps.2.1) (fun j=>(room.prep _ (fromChild j)).keeps.2.1)
  have init (j : Fin 6):numeric (B).input ((B).layout.hub+j.val)=(K).words j:=by
    rw [numeric,hubWords,Fin.val_cast_of_lt (hubFit j)]
  have keep {x} (re : relevant x) (away : x≠(B).control.val ∧ ∀ u∈ops,x<u.start ∨ u.finish≤x) :
      (B).reached ops x=(B).input x:=(HistoryReadyTape.after_away (B).control ops (B).entered x away.1 away.2).trans
        (room.prep x re).keeps.2.2
  have fin (j : Fin 6) : numeric ((B).reached ops) ((B).layout.hub+j.val)=(K).words j :=
    (congrArg Fin.val (keep (atHub j.castSucc) (stay.hub j.castSucc))).trans (init j)
  have pc : ((B).reached ops (K).children).val=src 1 := by
    have z:=linkWords 0
    simp only [Fin.val_zero,Nat.add_zero] at z
    have re : relevant (K).children := by simpa using atLink (0:Fin 4)
    rw [keep re stay.link,z,Fin.val_cast_of_lt (room.linkFit 0)]
    rfl
  have loadedH : readHub (B).layout (numeric ((B).reached ops))=K := by
    have h0 : numeric ((B).reached ops) (B).layout.hub=(K).stream := fin 0
    have h1 : numeric ((B).reached ops) ((B).layout.hub+1)=(K).pins := fin 1
    have h2 : numeric ((B).reached ops) ((B).layout.hub+2)=(K).shared := fin 2
    have h3 : numeric ((B).reached ops) ((B).layout.hub+3)=(K).argc := fin 3
    have h4 : numeric ((B).reached ops) ((B).layout.hub+4)=(K).children := fin 4
    have h5 : numeric ((B).reached ops) ((B).layout.hub+5)=(K).arguments := fin 5
    rw [readHub,h0,h1,h2,h3,h4,h5]
  have frame {μ : Memory W} {lo len : ℕ} (key : (child K (numeric μ) 0).node=src 1)
      (protect : ∀ x,relevant x→x<lo ∨ lo+len≤x) : HistoryBoundedBody.Frame (B).layout K μ lo len := by
    refine ⟨fun j=>protect _ (atHub j),?_,?_⟩
    · intro i j
      have hz:i.val=0:=by have:=i.isLt;change i.val<1 at this;omega
      simpa [hz] using protect _ (atLink j)
    · intro i j
      have hz:i.val=0:=by have:=i.isLt;change i.val<1 at this;omega
      simpa [hz,key] using protect _ (fromChild j)
  have childAt (μ : Memory W) (r : RootInput A node winner L R (a+b) (numeric μ)) :
      (child K (numeric μ) 0).node=src 1 := by
    have z:=r.link (0:Fin 4)
    change numeric μ ((C).party.seed+64+7+0)=src 1 at z
    exact z
  have key₁ := childAt (B).seeded first
  have key₂ := childAt (B).commands second
  have key₃ : (child K (numeric ((B).reached ops)) 0).node=src 1:=by simpa [child,numeric] using pc
  have eq:=RootInput.commands A node winner L R (p:=p) mem first
  have load := (B).loaded N MP id qa rfl (.inl small.order.2)
    (fun i=>by have hz:i=0:=Subsingleton.elim _ _;subst i;exact congrFun eq.1 (1:Fin 7))
    (fun i=>by have hz:i=0:=Subsingleton.elim _ _;subst i;exact congrFun eq.1 (6:Fin 7))
    (fun i=>by have hz:i=0:=Subsingleton.elim _ _;subst i;exact congrFun eq.2.1 (1:Fin 7))
    (fun i=>by have hz:i=0:=Subsingleton.elim _ _;subst i;exact congrFun eq.2.1 (6:Fin 7))
  have base : (B).outputBase=dst 1:=by
    rw [HistoryBoundedBody.Build.outputBase,numeric,target,Fin.val_cast_of_lt (by have:=small.result;omega)]
  have count : numeric ((B).reached ops) ((B).layout.hub+3)=1:=fin 3
  have ch : numeric ((B).reached ops) ((B).layout.hub+4)=(K).children:=fin 4
  refine ⟨by have:=winner.isLt;change 1≤A.party.parties;omega,small.seed,small.header,?_,small.order,
    small.cmd,small.args,init,?_,frame key₁ (fun x h=>(room.prep x h).command),
    frame key₂ (fun x h=>(room.prep x h).arguments),small.small,small.cap,small.link,?_,
    Tape.tape_length N MP id qa,small.controlAway,small.limits,load,?_,?_,?_,?_,?_⟩
  · right
    change (C).party.seed+9≤(C).party.seed+64
    omega
  · intro j
    exact ⟨(congrArg Fin.val (room.prep _ (atHub j.castSucc)).keeps.1).trans (init j),
      (congrArg Fin.val (room.prep _ (atHub j.castSucc)).keeps.2.1).trans (init j)⟩
  · intro i
    have hz:i.val=0:=by have:=i.isLt;change i.val<1 at this;omega
    change (child K (numeric (B).seeded) i.val).node+3<2^W ∧
      (child K (numeric (B).commands) i.val).node+3<2^W
    rw [hz,key₁,key₂]
    exact ⟨small.child,small.child⟩
  · rw [base];exact small.result
  · rw [base,loadedH];exact frame key₃ small.resultAway
  · exact congrArg Fin.val (keep (atHub 6) (stay.hub 6))
  · dsimp only
    rw [count,ch]
    simpa using small.link
  · dsimp only
    intro k
    have hz:k.val=0:=by have:=k.isLt;omega
    rw [hz,ch]
    simpa [numeric,pc] using small.child

end Root

section DirectParty
open Diagonal Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms Diagonal.HistogramTileNetwork
open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
variable {K H J E S : Type} [Field K] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] {r k n e d s : ℕ}
  (D : PortGraph J E) (G : Supply J S) (j : J) (live base : E→ℕ)
  (B : Header (D.Port j) H (fun q=>base q.1.1) k n) (sa : Fin e≃(ports G).Port j)
  (sw : H→S→ℕ) (fits : ∀ z q,sw z (sa q).1.1≤d)
  (M : ∀ z i,D.State (fun t=>Fin (2^base t)) i → (ports G).State (fun t=>Fin (2^sw z t)) i → K)
  (id : H≃Fin s) (z : Histogram H r) (C : BitNetwork K ((r*d)+(r*d+r*d)))
  (cnt : BitNetwork K (r+(r+r))) (old : (u : D.Port j)→Fin (live u.1.1)→Fin p)
  (fresh : (u : (ports G).Port j)→Fin (histWidth sw z u.1.1+r*k)→Fin p)

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
/-- The singleton root is definitionally the direct party used by the degree-refresh H cell. -/
theorem resultTree_direct :
    resultTree (admission (headerGood G j sa B.code) (headerLetter G j sa id B.code) cnt (numberHistogram id z))
      (tiled (tile D G j base B sa sw fits M) C)
      (partyPointer D G j base live B sa sw z (fun q t=>.pin (old q t)) (fun q t=>.pin (fresh q t)))=
    directParty D G j live base B sa sw fits M id z C cnt old fresh := rfl

end DirectParty


end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
