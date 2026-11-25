import OAI.ThreeFlat.RAM.HistoryMotifTariffCosts
import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.RAM.HistorySelectedFamily

namespace OAI
/-! # Refresh roster and catalogue reads at entry -/

set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalProcedure Diagonal.TickWorkspace
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryStageBody.Physical
open HistoryMotifJoin HistoryBoundedBody HistoryScratch HistoryPartyBatchExec
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {u node x : ℕ}
local notation "V" => volume u
local notation "W₀" => 16*u^10

private theorem frame_size (age : 16≤u) : 1024≤V ∧ 10*V ≤ Diagonal.TickWorkspace.stride u := by
  have large : 1024≤V := Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide : 10 ≠ 0) u))
  refine ⟨large,?_⟩
  change 10*V≤V^4
  calc
    _≤V*V:=Nat.mul_le_mul_right V (by omega)
    _=V^2:=(pow_two V).symm
    _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)

/-- The child-prefix scan only changes the S18 array at offset three volumes. -/
theorem starts_outside (archive : Archive) (f : Family) (input : Memory W₀)
    (age : 16≤u) (cap : ℕ) (fits : cap+1≤V) (safe : OutsideNode u node x) :
    let A:=layout u archive f
    fillSegment A.nodePorts.starts (cap+1)
      (fun j=>(childWidth A.nodePorts cap (numeric input) j:Word W₀)) input x=input x := by
  obtain ⟨large,big⟩:=frame_size age
  have s₁:=apart (u:=u) (by decide : 14<18)
  have s₂:=apart (u:=u) (by decide : 18<19)
  have h:=safe.scratch_range (lo:=base u 18+3*V) (hi:=base u 18+3*V+(cap+1))
    (by omega) (by omega) (.inr (by omega))
  have clean : ¬(base u 18+3*V≤x ∧ x<base u 18+3*V+(cap+1)):=by omega
  change fillSegment (base u 18+3*V) (cap+1) _ input x=_
  simp only [fillSegment,ite_eq_right clean]

/-- Both physical scans immediately preceding the arm loop protect all outside words. -/
theorem prefix_outside (archive : Archive) (f : Family) (input : Memory W₀)
    (age : 16≤u) (cap : ℕ) (fits : cap+1≤V) (safe : OutsideNode u node x) :
    let A:=layout u archive f
    let stage:=fillSegment A.nodePorts.starts (cap+1)
      (fun j=>(childWidth A.nodePorts cap (numeric input) j:Word W₀)) input
    privateStage (withMotif A 0) stage x=input x :=
  (private_stage_outside archive f node _ x safe age).trans (starts_outside archive f input age cap fits safe)

section RootFrame
variable {p a b : ℕ} {F : Type*} [CommRing F]
variable (archive : Archive) (f : Family) (winner : Fin f.parties)
variable (L : Tree F a) (R : Tree F b) (wire : Fin (a+b)→BitSource 0 p)
variable (id : ((Fin 3→Bool)→F)→ℕ) (mem : Memory (16*u^10))
local notation "A₀" => layout u archive f
local notation "C₀" => withMotif A₀ 0
local notation "B₀" => groupBuild C₀ true (groupHub C₀ mem true node p 0 1) mem
local notation "jobs₀" => Tape.tape (W:=W₀) (fun _ : Fin 1=>(pair L R).compile)
  (fun _=>wire) id (fun _=>rootHeader A₀ node winner (a+b) p)

omit [CommRing F] in
/-- All writes of the singleton H root: header, seed, commands, arguments,
ready-tape cursor, pin map, copied rows and four output words. -/
theorem root_join_outside (age : 16≤u) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (pins : a+b≤V) (rowsFit : 4*(pair L R).compile.cells≤V)
    (result : (B₀).outputBase=resultBank C₀ node true 1)
    (safe : OutsideNode u node x) : (B₀).output jobs₀ x=mem x := by
  obtain ⟨large,big⟩:=frame_size age
  have s14:=apart (u:=u) (by decide : 14<15)
  have s15:=apart (u:=u) (by decide : 15<16)
  have s16:=apart (u:=u) (by decide : 16<18)
  have s18:=apart (u:=u) (by decide : 18<19)
  have wordRoom:=word_space (i:=18) (by omega : 1≤u) (by omega : 18<Diagonal.TickWorkspace.stride u)
  have parties : f.parties≤V := by
    have positive : 1≤f.motifs+2:=by omega
    have step:=Nat.mul_le_mul_right (f.parties+2) positive
    simp only [Nat.one_mul] at step
    omega
  have sep {lo hi : ℕ} (low : base u 14≤lo) (high : hi≤base u 18) : x<lo ∨ hi≤x :=
    safe.scratch_range low (by omega) (.inl high)
  have prep : PrepAway B₀ x := by
    constructor
    · change x<base u 14+V ∨ base u 14+V+9≤x
      apply sep <;> omega
    · change x<base u 15 ∨ base u 15+14*1≤x
      apply sep <;> omega
    · change x<base u 16 ∨ base u 16+7*1≤x
      apply sep <;> omega
  have hdr : (B₀).input x=mem x := by
    have aside:=sep (lo:=base u 14+V+64) (hi:=base u 14+V+64+(7+7*f.parties))
      (by omega) (by omega)
    have neg : ¬(base u 14+V+64≤x ∧ x<base u 14+V+64+(7+7*f.parties)):=by omega
    change headerImage _ (base u 14+V+64) (rows C₀ W₀ true).length mem x=mem x
    rw [rows_len]
    simp only [headerImage,fillSegment,ite_true,withMotif,layout,neg,ite_false]
  have ctrl : (B₀).control.val=base u 14+V+7 := by
    exact Fin.val_cast_of_lt (show base u 14+V+7<2^W₀ by omega)
  have different : x≠(B₀).control.val:=by
    have h:=prep.seed
    change x<base u 14+V ∨ base u 14+V+9≤x at h
    rw [ctrl]
    omega
  have source : (⟨2,winner.val+2,2,3⟩:Local).Valid f.motifs f.parties := by
    change 2<f.motifs+2 ∧ winner.val+2<f.parties+2 ∧ 2<8 ∧ 3<32
    exact ⟨by omega, Nat.add_lt_add_right winner.isLt 2, by decide, by decide⟩
  have target (k:ℕ) (small:k<32) : (⟨2,0,3,k⟩:Local).Valid f.motifs f.parties := by
    change 2<f.motifs+2 ∧ 0<f.parties+2 ∧ 3<8 ∧ k<32
    exact ⟨by omega, by omega, by decide, small⟩
  have pinRange:=safe.private_range capacity _ source (a+b) pins
  have rowRange:=safe.private_range capacity _ (target 0 (by decide)) _ rowsFit
  have opsAway : ∀ op∈jobs₀,x<op.start ∨ op.finish≤x := by
    intro op member
    obtain ⟨i,_,h⟩:=List.mem_flatMap.mp member
    rcases (show op=_ ∨ op=_ from by simpa only [Tape.jobs,List.mem_cons,List.not_mem_nil,
      or_false] using h) with rfl|rfl
    · exact pinRange
    · exact rowRange
  have stream:=HistoryReadyTape.after_away (B₀).control jobs₀ (B₀).entered x different opsAway
  have outRange:=safe.private_range capacity _ (target 1 (by decide)) 4 (by omega)
  change x<resultBank C₀ node true 1 ∨ resultBank C₀ node true 1+4≤x at outRange
  have outNeg : ¬((B₀).outputBase≤x ∧ x<(B₀).outputBase+4):=by rw [result];omega
  calc
    (B₀).output jobs₀ x=(B₀).reached jobs₀ x:=by simp only [HistoryBoundedBody.Build.output,fillSegment,outNeg,ite_false]
    _=(B₀).entered x:=stream
    _=(B₀).input x:=prep.keeps.2.2
    _=mem x:=hdr

end RootFrame

/-- Enter the true elected party after running only the earlier dormant arms.
The proof is independent of every operation of the elected party itself. -/
theorem physical_before_winner {F : Type*} [CommRing F] (arch : Archive) (f : Family)
    (winner : Fin f.parties) (id : ((Fin 3→Bool)→F)→ℕ) (stage : Memory W₀)
    {kernelPtr incidentPtr : ℕ}
    (original : IncidenceRead u f node winner stage kernelPtr incidentPtr)
    (immutable : IncidenceRoom u node kernelPtr incidentPtr) (loc : IncidenceOutside u node kernelPtr incidentPtr)
    (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (mask : 2^f.parties<2^W₀)
    (lookup : arch.lut+1<2^W₀) (lutStride : arch.lutStride<2^W₀) (pages : arch.pages<2^W₀)
    (pageStride : arch.pageStride<2^W₀) (counts : arch.counts+1<2^W₀)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts)
    (cap : 3+5*f.demands+4*f.supplies≤V) (ports : HistoryGatherExecution.portsEnd (layout u arch f)<2^W₀) :
    let A:=layout u arch f
    let live:=beforeWinner A node winner id stage
    IncidenceRead u f node winner live kernelPtr incidentPtr ∧
      (∀ x,(readZone u x ∨ OutsideNode u node x)→live x=privateStage (withMotif A 0) stage x) ∧
      (∀ x,OutsideNode u node x→live x=stage x) := by
  let A:=layout u arch f
  let init:=privateStage (withMotif A 0) stage
  let pre (n:ℕ):=(List.range n).foldl (fun m j=>vacantPass (rawArm A j) node id m) init
  have start (x:ℕ) (safe:OutsideNode u node x) : init x=stage x:=private_stage_outside arch f node stage x safe age
  have loop (n:ℕ) (earlier:n≤winner.val) :
      IncidenceRead u f node winner (pre n) kernelPtr incidentPtr ∧
        ∀ x,(readZone u x ∨ OutsideNode u node x)→pre n x=init x := by
    induction n with
    | zero => exact ⟨original.keep_outside f node winner loc start,fun _ _=>rfl⟩
    | succ n ih =>
      let j:Fin f.parties:=⟨n,by have:=winner.isLt;omega⟩
      have before:=ih (by omega)
      have off : j≠winner:=by intro h;have:=congrArg Fin.val h;change n=winner.val at this;omega
      have frame:=(physical_vacant_room_all u arch f node winner j (pre n) kernelPtr incidentPtr id before.1 immutable off
        age count motifs capacity mask lookup lutStride pages pageStride counts lutAway countsAway cap ports).2
      have step : pre (n+1)=vacantPass (rawArm A j.val) node id (pre n) := by
        simp only [pre,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]; rfl
      rw [step]
      exact ⟨before.1.keep_outside f node winner loc (fun x h=>frame x (.inr h)),
        fun x h=>(frame x h).trans (before.2 x h)⟩
  have out:=loop winner.val (Nat.le_refl _)
  exact ⟨out.1,out.2,fun x h=>(out.2 x (.inr h)).trans (start x h)⟩

section FullKernelFrame
open Diagonal Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms Diagonal.MotifSelectorChecks
open HistoryPartySpecialization
open private liveCheckJobs from OAI.ThreeFlat.RAM.HistoryRefreshElectedJobs
variable {K : Type} [CommRing K] [Fintype K] {H : Type*} {r s e k b d B ar p : ℕ}
    (tile : Tile K H e d b) (good : (Fin (e*k)→Bool)→Prop) (letter : (Fin (e*k)→Bool)→Fin s)
    (tp : b+(e*d+e*d)≤ar) (sp : e*k+s≤ar) (arch : HistoryStageBody.Physical.Archive) (f : Family)
    (node : ℕ) (winner : Fin f.parties) (oldCap : ℕ) (mem : Memory (16*u^10))
local notation "A" => layout u arch f
local notation "J" => rawArm A winner.val
local notation "C" => withMotif A 0
local notation "stage" => fillSegment (A).nodePorts.starts (oldCap+1)
    (fun j=>(childWidth (A).nodePorts oldCap (numeric mem) j:Word W₀)) mem
local notation "input" => beforeWinner A node winner (tag (K:=K)) stage
variable (t : Fin (B+1)) (z : Histogram (Fin s) r)
local notation "lib" => HistoryStaticArchive.all K ar
local notation "X" => electedBatch tile good letter tp sp (J).party input true
private abbrev kernelPrefixChecks : Prop :=
  Reads (X).regs (numeric (X).bootImage) lib r t
variable (readC : kernelPrefixChecks (u:=u) (tile:=tile) (good:=good) (letter:=letter)
  (tp:=tp) (sp:=sp) (arch:=arch) (f:=f) (node:=node) (winner:=winner)
  (oldCap:=oldCap) (mem:=mem) (r:=r) (t:=t))
local notation "SC" => MotifNativeCompactors.partialInput K r t.val
local notation "PC" => MotifNativeCompactors.partialInput K (r*d) t.val
local notation "L" => admission good letter SC z
local notation "R" => tiled tile PC
local notation "a₀" => r*(e*k)
local notation "b₀" => r*b+e*(r*d)
local notation "jobsC" => liveCheckJobs tile good letter tp sp (J).party input t z readC
local notation "Y" => electedBatch tile good letter tp sp (J).party ((X).published jobsC) false
private abbrev kernelPrefixPayload : Prop :=
  Reads (Y).regs (numeric (Y).bootImage) lib r t
variable (readP : kernelPrefixPayload (u:=u) (tile:=tile) (good:=good) (letter:=letter)
  (tp:=tp) (sp:=sp) (arch:=arch) (f:=f) (node:=node) (winner:=winner)
  (oldCap:=oldCap) (mem:=mem) (t:=t) (z:=z) (readC:=readC))
variable (wire : Fin (r*(e*k)+(r*b+e*(r*d)))→BitSource 0 p)
    (plan : HistoryGatherExecution.Plan (16*u^10))
local notation "pairMem" => electedOutput tile good letter tp sp (J).party node input t z readC readP
local notation "gathered" => HistoryGatherExecution.output J plan pairMem
local notation "finalInput" => entryOf A node winner (tag (K:=K)) stage pairMem gathered f.parties
local notation "builder" => groupBuild C true (groupHub C finalInput true node p 0 1) finalInput
local notation "jobs" => Tape.tape (W:=W₀) (fun _ : Fin 1=>(pair L R).compile)
    (fun _=>wire) tag (fun _=>rootHeader A node winner (a₀+b₀) p)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2200000 in
/-- The actual H kernel memory after child prefixes, private header, all two-batch
party arms and gathers, and the singleton ready-tape root protects every outside
word, including both traversal controls. -/
theorem kernel_output_outside {kernelPtr incidentPtr : ℕ}
    (incidence : IncidenceRead u f node winner mem kernelPtr incidentPtr)
    (immutable : IncidenceRoom u node kernelPtr incidentPtr) (loc : IncidenceOutside u node kernelPtr incidentPtr)
    (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (mask : 2^f.parties<2^W₀)
    (lookup : arch.lut+1<2^W₀) (lutStride : arch.lutStride<2^W₀) (pages : arch.pages<2^W₀)
    (pageStride : arch.pageStride<2^W₀) (counts : arch.counts+1<2^W₀)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts)
    (cap : oldCap+1≤V) (headerCap : 3+5*f.demands+4*f.supplies≤V)
    (ports : HistoryGatherExecution.portsEnd J<2^W₀)
    (widths : ∀q i,i<HistoryGatherExecution.cap J q → plan.width q i≤V)
    (mapBase : plan.gatherBase=HistoryPartyPair.atPair (J).party node 2) (pinCount : plan.gatherCount≤V)
    (room : ElectedRoom tile good letter tp sp (J).party node input t z readC readP)
    (checksCount : (X).count≤V) (checkRows : 8*HistoryPartyTapeRun.batchRows (X).table≤V)
    (checkPins : HistoryPartyTapeRun.batchPins (X).table≤V) (payloadCount : (Y).count≤V)
    (payloadRows : 8*HistoryPartyTapeRun.batchRows (Y).table≤V) (payloadPins : HistoryPartyTapeRun.batchPins (Y).table≤V)
    (pairPins : a₀+b₀≤V) (pairRows : 4*((L).rows+(R).rows)≤V)
    (result : (builder).outputBase=resultBank C node true 1) :
    ∀ x,OutsideNode u node x→(builder).output jobs x=mem x := by
  have scan_frame (addr : ℕ) (safeWord : OutsideNode u node addr) : stage addr = mem addr :=
    starts_outside (u:=u) (node:=node) (x:=addr) arch f mem age oldCap cap safeWord
  have source : IncidenceRead u f node winner stage kernelPtr incidentPtr :=
    incidence.keep_outside f node winner loc scan_frame
  have arm:=elected_pair_outside tile good letter tp sp (J).party node input t z readC readP room
    (PartyWindow.of_layout arch f 0 winner.val age motifs winner.isLt capacity)
    checksCount checkRows checkPins payloadCount payloadRows payloadPins pairPins pairRows
  have roster:=(physical_roster_frame arch f node winner (tag (K:=K)) stage pairMem plan source immutable loc
    age count motifs capacity mask lookup lutStride pages pageStride counts lutAway countsAway
    headerCap ports widths mapBase pinCount arm f.parties (Nat.le_refl _)).2
  have cells : (pair L R).compile.cells=(L).rows+(R).rows := by
    change (∑ i : Fin 2,(pairNetwork L R i).cells)=_
    rw [Fin.sum_univ_two]
    change (L).compile.cells+(R).compile.cells=_
    simp only [compiled_rows]
  intro x safe
  have root:=root_join_outside (u:=u) (node:=node) (x:=x) arch f winner L R wire (tag (K:=K)) finalInput age motifs capacity
    pairPins (by simpa only [cells] using pairRows) result safe
  exact root.trans ((roster x safe).trans (scan_frame x safe))


open private privateStage_away from OAI.ThreeFlat.RAM.HistoryRefreshEmitter

private theorem prefix_words_of_frames (prior selected : Memory (16*u^10))
    (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (cap : oldCap+1≤V)
    (priorRead : ∀ addr, readZone u addr → prior addr=privateStage C stage addr)
    (selectedRead : ∀ addr, PartyAway u (J).party node addr → selected addr=prior addr)
    (j : Fin (oldCap+1)) :
    selected ((A).nodePorts.starts+j.val) =
      (childWidth (A).nodePorts oldCap (numeric mem) ((A).nodePorts.starts+j.val):Word W₀) := by
  let addr := (A).nodePorts.starts+j.val
  have childBase : (A).nodePorts.starts=base u 18+3*V := rfl
  have privateBase : (C).privateStarts=base u 18+4*V := rfl
  have indexBound : j.val<V := Nat.lt_of_lt_of_le j.isLt cap
  have low : base u 18≤addr := by dsimp only [addr]; rw [childBase]; omega
  have high : addr<base u 18+5*V := by dsimp only [addr]; rw [childBase]; omega
  have beforePrivate : addr<(C).privateStarts := by
    dsimp only [addr]; rw [privateBase,childBase]; omega
  have away : PartyAway u (J).party node addr := by
    refine ⟨Or.inr (Or.inr ⟨low,high⟩),?_⟩
    intro fam bank famBound bankBound len lenBound
    let slot : Local := ⟨2,winner.val+2,fam,bank⟩
    have valid : slot.Valid f.motifs f.parties :=
      ⟨Nat.add_lt_add_right motifs 2,Nat.add_lt_add_right winner.isLt 2,famBound,bankBound⟩
    have below := (local_window u f node age count capacity slot valid).2.1
    exact Or.inr (((Nat.add_le_add_left lenBound _).trans below).trans
      ((Diagonal.TickWorkspace.apart (u:=u) (by decide : 12<18)).trans low))
  have throughPrivate : privateStage C stage addr=stage addr :=
    privateStage_away C stage addr (fun h => (Nat.not_le_of_lt beforePrivate) h.1)
  have atChild : (A).nodePorts.starts≤addr ∧ addr<(A).nodePorts.starts+(oldCap+1) :=
    ⟨Nat.le_add_right _ _,Nat.add_lt_add_left j.isLt _⟩
  have childWord : stage addr=(childWidth (A).nodePorts oldCap (numeric mem) addr:Word W₀) :=
    ite_eq_left atChild
  exact (selectedRead addr away).trans ((priorRead addr (Or.inr low)).trans
    (throughPrivate.trans childWord))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
/-- Before the gather, both published party batches and the pair join preserve
the real child-prefix scan and every address outside the selected node. -/
theorem elected_prefix_frame {kernelPtr incidentPtr : ℕ}
    (incidence : IncidenceRead u f node winner mem kernelPtr incidentPtr)
    (immutable : IncidenceRoom u node kernelPtr incidentPtr) (loc : IncidenceOutside u node kernelPtr incidentPtr)
    (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (mask : 2^f.parties<2^W₀)
    (lookup : arch.lut+1<2^W₀) (lutStride : arch.lutStride<2^W₀) (pages : arch.pages<2^W₀)
    (pageStride : arch.pageStride<2^W₀) (counts : arch.counts+1<2^W₀)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts)
    (cap : oldCap+1≤V) (headerCap : 3+5*f.demands+4*f.supplies≤V)
    (ports : HistoryGatherExecution.portsEnd J<2^W₀)
    (room : ElectedRoom tile good letter tp sp (J).party node input t z readC readP)
    (components : r+max s e≤V) (gates : 8*((L).rows+(R).rows)≤V)
    (pins : (r*(e*k+s)+s*(r+(r+r)))+(r*(b+(e*d+e*d))+e*(r*d+(r*d+r*d)))≤V) :
    (∀ j : Fin (oldCap+1),pairMem ((A).nodePorts.starts+j.val)=
      (childWidth (A).nodePorts oldCap (numeric mem) ((A).nodePorts.starts+j.val):Word W₀)) ∧
      ∀ x,OutsideNode u node x→pairMem x=mem x := by
  have scan_frame (addr : ℕ) (safeWord : OutsideNode u node addr) : stage addr = mem addr :=
    starts_outside (u:=u) (node:=node) (x:=addr) arch f mem age oldCap cap safeWord
  have source : IncidenceRead u f node winner stage kernelPtr incidentPtr :=
    incidence.keep_outside f node winner loc scan_frame
  have early:=physical_before_winner arch f winner (tag (K:=K)) stage source immutable loc age count motifs capacity
    mask lookup lutStride pages pageStride counts lutAway countsAway headerCap ports
  have win:=PartyWindow.of_layout arch f 0 winner.val age motifs winner.isLt capacity
  have pairAt:=elected_room_away tile good letter tp sp (J).party node input t z readC readP room win components gates pins
  constructor
  · exact prefix_words_of_frames (u:=u) (arch:=arch) (f:=f) (node:=node) (winner:=winner)
      (oldCap:=oldCap) (mem:=mem) input pairMem age count motifs capacity cap
      (fun addr inZone => early.2.1 addr (Or.inl inZone)) pairAt
  · intro x safe
    exact (pairAt x (PartyAway.of_outside win safe)).trans ((early.2.2 x safe).trans (scan_frame x safe))

private theorem roster_private_last {w ports height padding : ℕ} (cfg : HistoryGatherBody.Layout)
    (source : Memory w) (mode : cfg.mode = .refresh ports height padding) :
    privateStage cfg source (cfg.privateStarts+8) = 0 := by
  have inside : cfg.privateStarts ≤ cfg.privateStarts+8 ∧ cfg.privateStarts+8 < cfg.privateStarts+9 := by omega
  simp only [privateStage, HistoryMotifJoin.headerImage, fillSegment, ite_eq_left inside]
  exact HistoryMotifJoin.privateHeader_refresh_zero cfg mode source ((cfg.privateStarts+8 : ℕ) : Word w)

private theorem roster_private_child {w : ℕ} (cfg : HistoryGatherBody.Layout)
    (start cap : ℕ) (word : ℕ → Word w) (source : Memory w) (j : Fin (cap+1))
    (before : start+j.val < cfg.privateStarts) :
    privateStage cfg (fillSegment start (cap+1) word source) (start+j.val) = word (start+j.val) := by
  have outside : ¬(cfg.privateStarts ≤ start+j.val ∧ start+j.val < cfg.privateStarts+9) := by omega
  have inside : start ≤ start+j.val ∧ start+j.val < start+(cap+1) :=
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left j.isLt _⟩
  simp only [privateStage, HistoryMotifJoin.headerImage, fillSegment, ite_eq_right outside, ite_eq_left inside]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2200000 in
/-- The complete live refresh roster preserves the ninth private prefix and
the actual older-child prefixes, including the singleton child's final width. -/
theorem roster_prefix_words {kernelPtr incidentPtr modePorts modeH modePad : ℕ}
    (mode : f.mode=.refresh modePorts modeH modePad)
    (incidence : IncidenceRead u f node winner mem kernelPtr incidentPtr)
    (immutable : IncidenceRoom u node kernelPtr incidentPtr) (loc : IncidenceOutside u node kernelPtr incidentPtr)
    (age : 16≤u) (count : node<V^2) (motifs : 0<f.motifs)
    (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V) (mask : 2^f.parties<2^W₀)
    (lookup : arch.lut+1<2^W₀) (lutStride : arch.lutStride<2^W₀) (pages : arch.pages<2^W₀)
    (pageStride : arch.pageStride<2^W₀) (counts : arch.counts+1<2^W₀)
    (lutAway : arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway : arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts)
    (cap : oldCap+1≤V) (headerCap : 3+5*f.demands+4*f.supplies≤V)
    (ports : HistoryGatherExecution.portsEnd J<2^W₀)
    (widths : ∀q i,i<HistoryGatherExecution.cap J q → plan.width q i≤V)
    (mapBase : plan.gatherBase=HistoryPartyPair.atPair (J).party node 2) (pinCount : plan.gatherCount≤V)
    (room : ElectedRoom tile good letter tp sp (J).party node input t z readC readP)
    (components : r+max s e≤V) (gates : 8*((L).rows+(R).rows)≤V)
    (pins : (r*(e*k+s)+s*(r+(r+r)))+(r*(b+(e*d+e*d))+e*(r*d+(r*d+r*d)))≤V) :
    finalInput ((((C).privateStarts+8:ℕ):Word W₀).val)=0 ∧
      ∀ k : Fin (oldCap+1),finalInput ((A).nodePorts.starts+k.val)=
        (childWidth (A).nodePorts oldCap (numeric mem) ((A).nodePorts.starts+k.val):Word W₀) := by
  let early (x : ℕ) : Prop := base u 18≤x ∧ x<base u 18+5*V
  let keep (x : ℕ) : Prop := OutsideNode u node x ∨ early x
  have before:=fun x (h : OutsideNode u node x)=>starts_outside arch f mem age oldCap cap h
  have source:=incidence.keep_outside f node winner loc before
  have initOutside:=fun x (h : OutsideNode u node x)=>private_stage_outside arch f node stage x h age
  have inRead:=source.keep_outside f node winner loc initOutside
  have w:=PartyWindow.of_layout arch f 0 winner.val age motifs winner.isLt capacity
  have protect:=elected_room_away tile good letter tp sp (J).party node input t z readC readP room w components gates pins
  have ord:=apart (u:=u) (by decide : 12<18)
  have pairAt (x : ℕ) (h : keep x) : pairMem x=input x := by
    apply protect x
    rcases h with h|h
    · exact PartyAway.of_outside w h
    · refine ⟨Or.inr (Or.inr h),?_⟩
      intro k bank hk hb len hlen
      have valid : (⟨2,winner.val+2,k,bank⟩:Local).Valid f.motifs f.parties:=
        ⟨by change 2<f.motifs+2; omega, Nat.add_lt_add_right winner.isLt 2, hk, hb⟩
      have below:=(local_window u f node age count capacity _ valid).2.1
      right
      exact ((Nat.add_le_add_left hlen _).trans below).trans (ord.trans h.1)
  have gatherAt (x : ℕ) (h : keep x) : gathered x=pairMem x := by
    let index : Local:=⟨2,winner.val+2,2,2⟩
    have valid : index.Valid f.motifs f.parties:=
      ⟨by change 2<f.motifs+2; omega, Nat.add_lt_add_right winner.isLt 2,
        (by decide : (2:ℕ)<8), (by decide : (2:ℕ)<32)⟩
    rcases h with h|h
    · exact gather_outside_node J plan pairMem h rfl rfl headerCap widths index valid capacity mapBase pinCount
    · have low : base u 18≤x := h.1
      have table : 1+f.demands+f.supplies≤V:=by omega
      have sizes:=Nat.mul_le_mul_right V table
      have growth : V^2≤V^4:=Nat.pow_le_pow_right (Nat.two_pow_pos _) (by decide)
      have ceiling:=apart (u:=u) (by decide : 17<18)
      have stop : HistoryGatherExecution.portsEnd J≤base u 18 := by
        change base u 17+(1+f.demands+f.supplies)*V≤base u 18
        change base u 17+V^4≤base u 18 at ceiling
        rw [pow_two] at growth;omega
      apply HistoryGatherExecution.output_away J plan pairMem x
      · right;rw [HistoryGatherExecution.header_size]
        change base u 17+(3+5*f.demands+4*f.supplies)≤x
        have hv : V ≤ Diagonal.TickWorkspace.stride u := Nat.le_self_pow (by decide : 4 ≠ 0) V
        exact (Nat.add_le_add_left (headerCap.trans hv) (base u 17)).trans (ceiling.trans low)
      · intro q i hi;right
        have width:=widths q i hi
        have bd:=(HistoryGatherExecution.aperture J q i hi).2
        exact ((Nat.add_le_add_left width _).trans bd).trans (stop.trans h.1)
      · right;rw [mapBase]
        have below:=(local_window u f node age count capacity index valid).2.1
        exact ((Nat.add_le_add_left pinCount _).trans below).trans (ord.trans h.1)
  have active (x : ℕ) (hx : keep x) :
      gathered x=entryOf A node winner (tag (K:=K)) stage pairMem gathered winner.val x := by
    have entryAt := congrFun (winner_entry A node winner (tag (K:=K)) stage pairMem gathered) x
    exact (gatherAt x hx).trans ((pairAt x hx).trans entryAt.symm)
  have frame:=roster_preserves A node winner (tag (K:=K)) stage pairMem gathered
    (fun m=>IncidenceRead u f node winner m kernelPtr incidentPtr) keep inRead
    (fun r=>⟨r.keep_outside f node winner loc (fun x hx=>active x (.inl hx)),active⟩) (by
      intro j other memory read
      have proof:=physical_vacant_room_all u arch f node winner j memory kernelPtr incidentPtr (tag (K:=K)) read immutable other
        age count motifs capacity mask lookup lutStride pages pageStride counts lutAway countsAway headerCap ports
      refine ⟨read.keep_outside f node winner loc (fun x hx=>proof.2 x (.inr hx)),?_⟩
      intro x hx
      rcases hx with h|h
      · exact proof.2 x (.inr h)
      · exact proof.2 x (.inl (Or.inr h.1)))
  have saved:= (frame f.parties le_rfl).2
  obtain ⟨large,big⟩:=frame_size (u:=u) age
  have word:=word_space (u:=u) (i:=18) (by omega) (by omega)
  have privateBase : (C).privateStarts=base u 18+4*V:=rfl
  have childBase : (A).nodePorts.starts=base u 18+3*V:=rfl
  constructor
  · have number : (C).privateStarts+8<2^W₀:=by rw [privateBase];omega
    have inPrefix : early ((C).privateStarts+8) := by
      change base u 18≤(C).privateStarts+8 ∧ (C).privateStarts+8<base u 18+5*V
      rw [privateBase]; constructor <;> omega
    exact (congrArg finalInput (Fin.val_cast_of_lt number)).trans
      ((saved ((C).privateStarts+8) (.inr inPrefix)).trans (roster_private_last C stage mode))
  · intro k
    have h:=k.isLt
    have small : (A).nodePorts.starts+k.val<(C).privateStarts:=by rw [privateBase,childBase];omega
    have inPrefix : early ((A).nodePorts.starts+k.val) := by
      change base u 18≤(A).nodePorts.starts+k.val ∧ (A).nodePorts.starts+k.val<base u 18+5*V
      rw [childBase]; constructor <;> omega
    exact (saved ((A).nodePorts.starts+k.val) (.inr inPrefix)).trans
      (roster_private_child C (A).nodePorts.starts oldCap
        (fun addr => (childWidth (A).nodePorts oldCap (numeric mem) addr : Word W₀)) mem k small)

end FullKernelFrame
end
end ThreeFlat.RAM.HistoryRefreshEmitter

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HistoryStageBody.Physical
open RAM.HistoryPartyBatchExec RAM.HistoryRefreshEmitter RAM.NavigationNodeRows HistoryStageSetup
open PhysicalStage NavigationDirectory CompressorPacking Native RefreshDemandRows RefreshStageNav RefreshTies
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {u K headerEnd : ℕ} {cur ctr : Word (16*u^10)}
variable (q : RefreshReceipt F K cur)
local notation "W" => 16*u^10
local notation "M" => refreshBinary q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn
local notation "P" => CursorSpace.recordPointers q.entry
local notation "pre" => (((refreshPre q.tile cur).pipeline cur).run q.mid)
local notation "deg" => 1+q.h+q.pad
local notation "ports" => 2^q.s
local notation "sites" => Fintype.card q.input.Base*ports*2^q.rem

private theorem layer_recast {F : Type} [Field F] {i l d d' r h : ℕ} {X : State i l} (e : d=d')
    (R : Move F X d r) (funding : Program.siteCharge R h) (b : Fin R.rules.count)
    (old : X.ArchiveSites) (row : R.ArchiveStep b old (funding.1 b)) :
    (Program.recastArchiveStep e R funding b old row).sites.layer=row.sites.layer := by cases e;rfl

theorem issued_layer : q.step.sites.layer=refreshOutputLayer K q.cursor (Fintype.card q.input.Base)
    ports (2^q.rem) q.h q.pad := by
  exact layer_recast q.degreeEq M q.funding q.branch q.old _

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
/-- The layer returned by the recorded navigation pass is the very layer whose
S44 children, widths and motif repetitions are traversed at history entry.
Its inputs all lie in the retained half-open allocation interval. -/
theorem issued_data {heads:ℕ} {ctr:Word W} {final:Memory W}
    (y:(q.move.next q.term).Site) (saved:SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds:RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (nodeFit:q.step.sites.id y<2^W) :
    q.step.data.Reads (numeric final) ∧
      q.step.data.Footprint (fun i=>q.cursor.heap ≤ i ∧ i<q.entry.next.heap) (numeric final) := by
  have first:q.step.sites.layer.first=q.cursor.node+sites:=by rw [q.issued_layer];rfl
  have ids:q.cursor.node+sites≤2^W:=by
    have lower:q.step.sites.layer.first≤q.step.sites.id y:=Nat.le_add_right _ _
    omega
  have copies:=fun i=>q.published i (0:Fin 3)
  obtain ⟨row,_,_,_,rd,_,fp,_,_,_,rowEq⟩:=
    refresh_archive_step_at_scale q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn
      q.degreeEq q.cursor cur q.branch pre q.out q.issued q.fit
      (fun i=>by simpa only [Fin.val_zero,Nat.add_zero,ite_eq_left rfl,ite_true] using copies i)
      (bounds.controls.1.trans cur.isLt.le) ids q.old q.numbered q.first q.chargeBound
  have actual:row=q.step:=rowEq
  rw [actual] at rd fp
  have keep (i:ℕ) (range:q.cursor.heap ≤ i ∧ i<q.entry.next.heap) :
      numeric final i=numeric q.out i := by
    have top:=bounds.controls.1
    have ctrTop:=bounds.controls.2
    exact congrArg Fin.val (saved i (by omega) (by omega) (.inr (bounds.header.trans range.1)) range.2)
  exact ⟨rd.of_footprint fp keep,fp.transfer fp keep⟩

/-- Pull a chronological output-site ordinal back to the concrete stored row. -/
def kernelSite (y : (q.move.next q.term).Site) : Records.Site (Fintype.card q.input.Base) ports q.rem :=
  Records.siteOrder.symm (Fin.cast (by rw [q.issued_layer];rfl) (q.step.sites.ord y))

theorem kernelSite_index (y : (q.move.next q.term).Site) :
    Records.siteId ((q.kernelSite y).1.1,(q.kernelSite y).2) (q.kernelSite y).1.2=(q.step.sites.ord y).val := by
  rw [←Records.siteOrder_val]
  simp only [kernelSite,Equiv.apply_symm_apply,Fin.val_cast]

variable {final mem : Memory (16*u^10)}
variable (saved : SavedFrame cur ctr headerEnd q.entry.next.header q.entry.next.heap q.out final)
    (bounds : headerEnd≤q.cursor.heap ∧ q.entry.next.heap≤cur.val ∧ cur.val<ctr.val)
    (retained : ∀ x,q.cursor.heap≤x→x<q.entry.next.heap→mem x=final x)

include saved bounds retained in
/-- The stage's literal emitted tables at the current selected node, after S44
publication, prefix installation, and all earlier cached node emissions. -/
theorem at_entry (t : Records.Table) :
    Records.Reads mem P q.cursor.header K
      (CompressorRefresh.graph (numberedRefreshGraph q.input) (DoublePorts.ofMatrix (Equiv.refl _)
        q.mult q.sym q.rowSum q.noLoop) q.hm q.pad)
      (refreshNumericWidths q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch)
      (fun i=>(pre i).val) t := by
  intro i
  have z:=q.record_interval t (Records.rowOrder deg t i)
  exact (retained _ z.1 z.2).trans (q.saved_records saved bounds.1 (.inr bounds.2.1)
    (.inr (bounds.2.1.trans bounds.2.2.le)) t i)

include saved bounds retained in
/-- The five cells needed at the start of the arm loop follow from the issued
table and the published directory row of this very node. -/
theorem incidence_at_entry (f : Family) (parties : f.parties=ports)
    (y : (q.move.next q.term).Site) (banks : Banks) (baseNodes : banks.nodes=TickWorkspace.base u 44)
    (row : HistoryStageSetup.DirectoryRow banks q.step.sites.layer (q.step.sites.ord y) mem)
    (current : numeric mem (TickWorkspace.base u 18)-1=q.step.sites.id y)
    (mask : 2^f.parties<2^W) :
    let ix:=(q.step.sites.ord y).val
    let winner : Fin f.parties:=Fin.cast parties.symm (q.kernelSite y).1.2
    IncidenceRead u f (q.step.sites.id y) winner mem ((P).kernel+ix*5) ((P).motif+ix*6) := by
  dsimp only
  let z:=q.kernelSite y
  let j:=(q.step.sites.ord y).val
  have siteId' : Records.siteId (z.1.1,z.2) z.1.2=j:=q.kernelSite_index y
  have off (t : Records.Table) (k : Fin (t.cols deg)) :
      (Records.rowOrder deg t (z,k)).val=j*t.cols deg+k.val := by
    rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,siteId'];rfl
  have regionK:=q.record_interval .kernel (Records.rowOrder deg .kernel (z,(0:Fin 5)))
  have regionM:=q.record_interval .motif (Records.rowOrder deg .motif (z,(0:Fin 6)))
  have ko := off .kernel (0:Fin 5)
  have mo := off .motif (0:Fin 6)
  rw [ko] at regionK
  rw [mo] at regionM
  have kFit : (P).kernel+j*5<2^W:=by
    have z':(P).kernel+(j*5+0)<q.entry.next.heap:=regionK.2
    have w:=cur.isLt
    omega
  have mFit : (P).motif+j*6<2^W:=by
    have z':(P).motif+(j*6+0)<q.entry.next.heap:=regionM.2
    have w:=cur.isLt
    omega
  have hd:=row.kernel
  rw [baseNodes] at hd
  have kern : q.step.sites.layer.kernels=(P).kernel:=by rw [q.issued_layer];rfl
  rw [kern] at hd
  have ptr : numeric mem (TickWorkspace.base u 44+8*q.step.sites.id y+5)=(P).kernel+j*5 :=
    (congrArg Fin.val hd).trans (Fin.val_cast_of_lt kFit)
  simpa only [siteId'] using
    (incidence_from_records u f (q.step.sites.id y) (Fin.cast parties.symm z.1.2) mem P q.cursor.header K
      _ _ _ z (q.at_entry saved bounds retained .kernel) (q.at_entry saved bounds retained .motif)
      current (by simpa only [siteId'] using ptr) rfl (by simpa only [siteId'] using mFit) mask)

/-- The three-word table index of the party selected by this site's incident record. -/
def chosenBlock (y : (q.move.next q.term).Site) :=
  (q.input.order.symm (q.kernelSite y).1.1,(q.kernelSite y).2)

/-- The selected typed kernel site, before the program's output-degree transport. -/
def typedKernelSite (y : (q.move.next q.term).Site) : (q.input.Base×BitWord q.rem)×Fin ports :=
  Program.degreeTarget q.degreeEq M q.branch (Move.WordStep.targetSite (R:=q.move) (i:=q.term) y)

private theorem degree_ordinal {F : Type} [Field F] {d l D E t k : ℕ} {X : State d l} (e : D=E)
    (R : Move F X D t) (funding : Program.siteCharge R k) (b : Fin R.rules.count)
    (old : X.ArchiveSites) (issued : R.ArchiveStep b old (funding.1 b))
    (y : ((Program.recastMove e R).next (Program.degreeTerm e R b)).Site) :
    ((Program.recastArchiveStep e R funding b old issued).sites.ord y).val=
      (issued.sites.ord ((Equiv.cast (congrArg HistoryContraction.Shape.Site (R.target_eq b)))
        (Program.degreeTarget e R b (Move.WordStep.targetSite (R:=Program.recastMove e R)
          (i:=Program.degreeTerm e R b) y)))).val := by
  cases e
  let castSite := Equiv.cast (congrArg HistoryContraction.Shape.Site (R.target_eq b))
  exact congrArg (fun v : (R.next b).Site => (issued.sites.ord v).val)
    (castSite.apply_symm_apply y).symm

private theorem degree_ordinal_read {F : Type} [Field F] {d l D E t k : ℕ} {X : State d l} (e : D=E)
    (R : Move F X D t) (funding : Program.siteCharge R k) (b : Fin R.rules.count)
    (old : X.ArchiveSites) (issued : R.ArchiveStep b old (funding.1 b))
    (read : (R.rules.target b).Site → ℕ)
    (indexed : ∀ x, (issued.sites.ord ((Equiv.cast (congrArg HistoryContraction.Shape.Site (R.target_eq b))) x)).val = read x)
    (y : ((Program.recastMove e R).next (Program.degreeTerm e R b)).Site) :
    ((Program.recastArchiveStep e R funding b old issued).sites.ord y).val =
      read (Program.degreeTarget e R b (Move.WordStep.targetSite (R:=Program.recastMove e R)
        (i:=Program.degreeTerm e R b) y)) :=
  (degree_ordinal e R funding b old issued y).trans (indexed _)

private theorem cast_site_self (S : Type) (e : S=S) (x : S) : Equiv.cast e x=x := rfl

local notation "rawRow" => refreshArchiveStep q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop
  q.conn q.issued q.fit (fun i=>by simpa using q.published i 0) q.old q.numbered q.first
local notation "rawCast" => Equiv.cast (congrArg HistoryContraction.Shape.Site ((M).target_eq q.branch))

set_option maxRecDepth 8192 in
private theorem raw_ordinal (x : (q.input.Base × BitWord q.rem) × Fin ports) :
    ((rawRow).sites.ord (rawCast x)).val =
      (Records.siteOrder ((q.input.order x.1.1,x.2),x.1.2)).val := by
  have returned := cast_site_self ((q.input.Base × BitWord q.rem) × Fin ports)
    (congrArg HistoryContraction.Shape.Site ((M).target_eq q.branch)) x
  exact congrArg (fun v : (q.input.Base × BitWord q.rem) × Fin ports =>
    (refreshFinalOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch v).val) returned

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1400000 in
/-- The archive header's native block number, party digit and lane select the same
graph site as the chronological refresh assembler. -/
theorem kernelSite_coordinates (y : (q.move.next q.term).Site) :
    q.kernelSite y=((q.input.order (q.typedKernelSite y).1.1,(q.typedKernelSite y).2),(q.typedKernelSite y).1.2) := by
  let read (x : (q.input.Base × BitWord q.rem) × Fin ports) :=
    (Records.siteOrder ((q.input.order x.1.1,x.2),x.1.2)).val
  have indexed : (q.step.sites.ord y).val=read (q.typedKernelSite y) :=
    degree_ordinal_read q.degreeEq M q.funding q.branch q.old rawRow read (q.raw_ordinal) y
  apply Records.siteOrder.injective
  apply Fin.ext
  exact ((Records.siteOrder_val (q.kernelSite y)).trans (q.kernelSite_index y)).trans indexed

theorem chosenBlock_coordinates (y : (q.move.next q.term).Site) :
    q.chosenBlock y=(q.typedKernelSite y).1 ∧ (q.kernelSite y).1.2=(q.typedKernelSite y).2 := by
  rw [chosenBlock,q.kernelSite_coordinates]
  simp


private theorem degree_charge_at {F : Type} [Field F] {d l D E t k : ℕ} {X : State d l} (e : D=E)
    (R : Move F X D t) (funding : Program.siteCharge R k) (b : Fin R.rules.count)
    (y : ((Program.recastMove e R).next (Program.degreeTerm e R b)).Site) :
    (Program.siteRecast e R funding).1 (Program.degreeTerm e R b) y=
      funding.1 b ((Equiv.cast (congrArg HistoryContraction.Shape.Site (R.target_eq b)))
        (Program.degreeTarget e R b (Move.WordStep.targetSite (R:=Program.recastMove e R)
          (i:=Program.degreeTerm e R b) y))) := by
  cases e
  let castSite := Equiv.cast (congrArg HistoryContraction.Shape.Site (R.target_eq b))
  exact congrArg (funding.1 b) (castSite.apply_symm_apply y).symm

set_option maxRecDepth 8192 in
private theorem raw_charge (x : (q.input.Base × BitWord q.rem) × Fin ports) :
    q.funding.1 q.branch (rawCast x) =
      1+((M).next q.branch).incidentWidth x+refreshBinaryCopies q.tile q.input x.1 := by
  have returned := cast_site_self ((q.input.Base × BitWord q.rem) × Fin ports)
    (congrArg HistoryContraction.Shape.Site ((M).target_eq q.branch)) x
  exact congrArg (q.funding.1 q.branch) returned

set_option maxRecDepth 8192 in
private theorem issued_charge (y : (q.move.next q.term).Site) :
    q.charge y=1+((M).next q.branch).incidentWidth (q.typedKernelSite y)+
      refreshBinaryCopies q.tile q.input (q.chosenBlock y) := by
  rw [(q.chosenBlock_coordinates y).1]
  have moved := degree_charge_at q.degreeEq M q.funding q.branch y
  exact moved.trans (q.raw_charge (q.typedKernelSite y))

/-- The fixed refresh cell and every emitted copy are paid by its own newly
published node charge, independently of the old contribution. -/
theorem issued_unit_copies_charge (y : (q.move.next q.term).Site) :
    1+refreshBinaryCopies q.tile q.input (q.chosenBlock y)≤q.charge y := by
  rw [q.issued_charge y]
  omega

theorem issued_copies_charge (y : (q.move.next q.term).Site) :
    refreshBinaryCopies q.tile q.input (q.chosenBlock y)≤q.charge y := by
  rw [q.issued_charge y]
  omega

theorem charge_positive (y : (q.move.next q.term).Site) : 0<q.charge y := by
  rw [q.issued_charge y]
  omega

def chosenIndex (y : (q.move.next q.term).Site) := refreshBlockOrder q.input (q.chosenBlock y)

theorem chosenIndex_val (y : (q.move.next q.term).Site) :
    (q.chosenIndex y).val=blockId ((q.kernelSite y).1.1,(q.kernelSite y).2) := by
  rw [chosenIndex,refreshBlockOrder_val]
  simp only [chosenBlock,Equiv.apply_symm_apply,blockId]

local notation "Q" => refreshBinaryFamily q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn

include saved bounds retained in
/-- The elected descriptor's kind and number of copies come from the original
score computation on the exact slice of the refreshed state. -/
theorem elected_at_entry (y : (q.move.next q.term).Site)
    (tableFit : q.tile.last+1≤2^W)
    (histFit : (P).counts+(q.chosenIndex y).val*K<2^W) :
    let base:=(P).motif+(q.step.sites.ord y).val*6
    let ix:=q.chosenIndex y
    let z:=q.chosenBlock y
    ∀ k:Fin 4,numeric mem (base+k.val)=
      (![ix.val,(P).counts+ix.val*K,(q.tile.winner (refreshBinaryGraph q.input) (tagOrdinal q.s).symm
        (refreshBinaryInput q.input) z).val,refreshBinaryCopies q.tile q.input z]:Fin 4→ℕ) k := by
  dsimp only
  let ix:=q.chosenIndex y
  let z:=q.chosenBlock y
  let t:=q.kernelSite y
  have inverse : (refreshBlockOrder q.input).symm ix=z:=(refreshBlockOrder q.input).symm_apply_apply z
  have scalar (k:Fin 3):= (q.saved_choice saved bounds.1 (.inr bounds.2.1)
    (.inr (bounds.2.1.trans bounds.2.2.le)) ix k).1
  have copies : (pre ((P).choices+ix.val*3)).val=refreshBinaryCopies q.tile q.input z := by
    have e : pre (q.cursor.heap+ix.val*3)=((Q).copies ix:Word W):=by
      simpa only [Fin.val_zero,Nat.add_zero,ite_eq_left rfl,ite_true] using scalar 0
    have h:=(congrArg Fin.val e).trans (Fin.val_cast_of_lt (q.fit.2 ix))
    change _=refreshBinaryCopies q.tile q.input ((refreshBlockOrder q.input).symm ix) at h
    rwa [inverse] at h
  have kind : (pre ((P).choices+ix.val*3+1)).val=(q.tile.winner (refreshBinaryGraph q.input)
      (tagOrdinal q.s).symm (refreshBinaryInput q.input) z).val := by
    let w:=q.tile.winner (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input) z
    have e : pre (q.cursor.heap+(ix.val*3+1))=(w.val:Word W):=by
      simpa only [Fin.val_one,ite_eq_right (by decide : (1:ℕ)≠0),ite_eq_left rfl,ite_true,inverse,w] using scalar 1
    change (pre (q.cursor.heap+ix.val*3+1)).val=_
    rw [Nat.add_assoc,e,Fin.val_cast_of_lt (w.isLt.trans_le tableFit)]
  have siteEq : Records.siteId (t.1.1,t.2) t.1.2=(q.step.sites.ord y).val:=q.kernelSite_index y
  have idx : blockId (t.1.1,t.2)=ix.val:=(q.chosenIndex_val y).symm
  have smallIndex : ix.val<2^W := by
    have pub:=q.record_interval .kernel (Records.rowOrder deg .kernel (t,(0:Fin 5)))
    have extent:=(CursorSpace.retained_addresses (c:=q.cursor) (K:=K) (v:=Fintype.card q.input.Base)
      (a:=q.s) (t:=q.rem) (h:=q.h) (pad:=q.pad)).2.1
    have count:ix.val<Fintype.card q.input.Base*2^q.rem:=ix.isLt
    change q.cursor.heap+3*(Fintype.card q.input.Base*2^q.rem)≤(P).kernel at extent
    have wordRoom:=cur.isLt
    have endPub : (P).kernel+(Records.rowOrder deg .kernel (t,(0:Fin 5))).val<q.entry.next.heap:=pub.2
    omega
  have small (k:Fin 4) : (![blockId (t.1.1,t.2),(P).counts+blockId (t.1.1,t.2)*K,
      (pre ((P).choices+blockId (t.1.1,t.2)*3+1)).val,(pre ((P).choices+blockId (t.1.1,t.2)*3)).val]:Fin 4→ℕ) k<2^W := by
    rw [idx]
    fin_cases k
    · exact smallIndex
    · exact histFit
    · exact Fin.isLt _
    · exact Fin.isLt _
  intro k
  have got:=elected_record_fields u mem P q.cursor.header K _ _ _ t
    (q.at_entry saved bounds retained .motif) small k
  simpa only [siteEq,idx,kind,copies] using got

/-- All cells used to re-read this party are protected by the actual node
write mask. The incident and kernel pointers are in the recorded native stage. -/
theorem incidence_geometry (y : (q.move.next q.term).Site) (age : 16≤u)
    (high : TickWorkspace.base u 19≤q.cursor.heap)
    (top : q.entry.next.heap≤cur.val) (nodeFit : q.step.sites.id y<(volume u)^2) :
    let ix:=(q.step.sites.ord y).val
    let kp:=(P).kernel+ix*5
    let ip:=(P).motif+ix*6
    IncidenceRoom u (q.step.sites.id y) kp ip ∧ IncidenceOutside u (q.step.sites.id y) kp ip := by
  let z:=q.kernelSite y
  let n:=q.step.sites.id y
  let ix:=(q.step.sites.ord y).val
  let V:=volume u
  have large : 1024≤V := Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have node : n+1≤V^2:=nodeFit
  have sq : V^2*V^2=TickWorkspace.stride u:=by change V^2*V^2=V^4;ring
  have interior : (n+1)*V^2≤TickWorkspace.stride u:=sq ▸ Nat.mul_le_mul_right (V^2) node
  have cache : 8*(n+1)≤TickWorkspace.stride u:=by
    calc
      _≤(n+1)*V^2 := by rw [Nat.mul_comm 8];apply Nat.mul_le_mul_left;exact (by nlinarith)
      _≤_:=interior
  have s12:=TickWorkspace.apart (u:=u) (by decide : 12<18)
  have s13:=TickWorkspace.apart (u:=u) (by decide : 13<18)
  have s18:=TickWorkspace.apart (u:=u) (by decide : 18<19)
  have s44:=TickWorkspace.apart (u:=u) (by decide : 19<44)
  have w44:=TickWorkspace.word_space (i:=44) (by omega : 1≤u) (by change 44<V^4;nlinarith : 44<TickWorkspace.stride u)
  have outsideLarge (a:ℕ) (above : TickWorkspace.base u 19≤a) : OutsideNode u n a :=
    ⟨.inr (by change TickWorkspace.base u 12+(n+1)*V^2≤a;omega),.inr (by omega),Or.inr (.inl above)⟩
  have cursor : OutsideNode u n (TickWorkspace.base u 18) :=
    ⟨.inr (by change TickWorkspace.base u 12+(n+1)*V^2≤_;omega),.inr (by omega),Or.inr (.inr (.inl rfl))⟩
  have span (q₀:Records.Table) (k:Fin (q₀.cols deg)) :
      q.cursor.heap≤(P).dst q₀+ix*q₀.cols deg+k.val ∧ (P).dst q₀+ix*q₀.cols deg+k.val<q.entry.next.heap := by
    have ord : (Records.rowOrder deg q₀ (z,k)).val=ix*q₀.cols deg+k.val:=by
      rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,q.kernelSite_index]
      rfl
    simpa only [ord,Nat.add_assoc] using q.record_interval q₀ (Records.rowOrder deg q₀ (z,k))
  have k3:=span .kernel (3:Fin 5)
  have k4:=span .kernel (4:Fin 5)
  have m5:=span .motif (5:Fin 6)
  change q.cursor.heap≤(P).kernel+ix*5+3 ∧ (P).kernel+ix*5+3<q.entry.next.heap at k3
  change q.cursor.heap≤(P).kernel+ix*5+4 ∧ (P).kernel+ix*5+4<q.entry.next.heap at k4
  change q.cursor.heap≤(P).motif+ix*6+5 ∧ (P).motif+ix*6+5<q.entry.next.heap at m5
  have word:=cur.isLt
  refine ⟨⟨by omega,by change TickWorkspace.base u 44+8*n+5<_;omega,
      by omega,by omega,.inr (by omega),.inr (by omega),.inr (by omega),.inr (by omega)⟩,?_⟩
  exact ⟨cursor,outsideLarge _ (by omega),outsideLarge _ (high.trans k3.1),
    outsideLarge _ (high.trans k4.1),outsideLarge _ (high.trans m5.1)⟩

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal PhysicalStage LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.MotifSelector
open CompressorPacking MotifOuterTerms HistogramTileNetwork Expander
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F]

/-- The exact tile table, selector page and port catalogue used by a physical
refresh at a selected finite table index and a party port. -/
def issuedParty {s h pad : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (hh : 0<h) (rows : ∀ i,∑ j,c i j=h)
    (sym : ∀ i j,c i j=c j i) (conn : Bound (transition c h) ℝ γ)
    (i : Fin (T.last+1)) (j : Fin (2^s)) : Party F :=
  Party.ofTile (RefreshMotif.denseGraph _) (DoublePorts.connectedSupply c hh rows sym conn)
    j (T.base i) (T.block i) (RefreshParty.denseOrder j) (RefreshParty.sparseOrder c sym rows j)
    Fin.val Fin.val

section SelectedRow
variable (B : Block F) {height W base : ℕ} {mem : Memory W} (mounted : Mounted B height W base mem)
local notation "fam" => refreshFamily B base height
local notation "grid₀" => refreshGrid B

include mounted in
/-- The prior immutable catalogue installation recovers the exact selected
refresh kind and port row after following the supported literal motif table. -/
theorem issued_party_rom {s h pad : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (supported : B.publicTemplate (.refresh s h pad c C T))
    (hh : 0<h) (rows : ∀ i,∑ j,c i j=h) (sym : ∀ i j,c i j=c j i) (conn : Bound (transition c h) ℝ γ)
    (i : Fin (T.last+1)) (j : Fin (2^s)) :
    let row:=issuedParty T hh rows sym conn i j
    row∈(grid₀).rows ∧ (fam).parties=2^s ∧
      (∀ k : Fin 7,mem ((fam).kinds+7*(i.val*(2^s)+j.val)+k.val)=((row.kind (arity B)).words k:Word W)) ∧
      ∀ k : Fin (grid₀).stride,mem ((fam).ports+(grid₀).stride*(i.val*(2^s)+j.val)+k.val)=
        (row.port.at (grid₀).demand (grid₀).supply k.val:Word W) := by
  let identity : StaticMotif F→Prop := fun
    | .shrink .. => True
    | .refresh s h pad c C T =>
      ∀ {g:ℝ} (hh:0<h) (rows:∀ i,∑ j,c i j=h) (sym:∀ i j,c i j=c j i)
        (conn:Bound (transition c h) ℝ g) (i:Fin (T.last+1)) (j:Fin (2^s)),
        let row:=issuedParty T hh rows sym conn i j
        row∈(grid₀).rows ∧ (fam).parties=2^s ∧
          (∀ k : Fin 7,mem ((fam).kinds+7*(i.val*(2^s)+j.val)+k.val)=((row.kind (arity B)).words k:Word W)) ∧
          ∀ k : Fin (grid₀).stride,mem ((fam).ports+(grid₀).stride*(i.val*(2^s)+j.val)+k.val)=
            (row.port.at (grid₀).demand (grid₀).supply k.val:Word W)
  have fixed : identity (.refresh (B.exponent B.levels) B.h B.pad B.graph _ B.refresh) := by
    intro g hh rows sym conn i j
    have get:=grid_row (refreshParty B) i j
    have member : refreshParty B i j∈(grid₀).rows:=List.mem_of_getElem? get
    have page : grids B=List.ofFn (shrinkGrid B)++grid₀::[]:=rfl
    refine ⟨member,rfl,?_,?_⟩
    · intro k
      exact mounted.kindAt (f:=refreshParty B) page rfl i j k
    · intro k
      exact mounted.portAt (f:=refreshParty B) page rfl i j k
  have rowId:=B.public_refresh supported
  exact ((congrArg identity rowId).mpr fixed) hh rows sym conn i j

/-- Word spans of the actual catalogue at the two fields chosen by a real refresh
incidence. The on-disk kind index is the public binary winner of this very block. -/
theorem issued_kind_window {u s h pad:ℕ} {c:Fin (2^s)→Fin (2^s)→ℕ} {C:ℝ}
    (T:RefreshMotif.Table F c (1+h+pad) C) (supported:B.publicTemplate (.refresh s h pad c C T))
    (i:Fin (T.last+1)) (j:Fin (2^s))
    (whole:RAM.HistoryRefreshEmitter.archiveWindow u base (libraryWords B height)) :
    RAM.HistoryRefreshEmitter.archiveWindow u ((fam).kinds+7*(i.val*2^s+j.val)) 7 := by
  let family : StaticMotif F→Prop:=fun
    | .shrink ..=>True
    | .refresh l _ _ _ _ M=>∀ (a:Fin (M.last+1)) (b:Fin (2^l)),
      RAM.HistoryRefreshEmitter.archiveWindow u ((fam).kinds+7*(a.val*2^l+b.val)) 7
  have fixed:family (.refresh (B.exponent B.levels) B.h B.pad B.graph _ B.refresh):=by
    intro a b
    have roster:grids B=List.ofFn (shrinkGrid B)++grid₀::[]:=rfl
    exact (RAM.HistoryRefreshEmitter.selected_archive_windows u B (cells:=refreshParty B) roster rfl a b whole).2.2.2.1
  exact ((congrArg family (B.public_refresh supported)).mpr fixed) i j

end SelectedRow
end
end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt
open Computability.VPVNP.BurstRAM RAM RAM.HistoryStageBody.Physical RAM.HistoryRefreshEmitter
open PhysicalStage
open scoped Classical
noncomputable section
variable {F:Type} [Field F] [Fintype F] {u K:ℕ} {cur:Word (16*u^10)}
    (q:RefreshReceipt F K cur) (B:Block F) (rom height:ℕ)
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "grid" => refreshGrid B
local notation "fam" => refreshFamily B rom height
local notation "arc" => archive B rom height K
local notation "A" => layout u arc fam

/-- The fixed branch decoded at a physical refresh node, with the literal
ranges used by its native party initialization. -/
structure IssuedLayout : Prop where
  mode : (fam).mode=.refresh (2^q.s) q.h q.pad
  parties : (fam).parties=2^q.s
  oldPorts : (fam).oldPorts=2^q.s
  childBound : (fam).childBound=1
  motifs : (fam).motifs=1
  same : Same A (kernelTemplate grid)
  cap : ((fam).motifs+2)*((fam).parties+2)*8*32≤V
  mask : 2^(fam).parties<2^W
  gradeFit : q.tile.last+1≤2^W
  lut : (arc).lut+1<2^W
  step : (arc).lutStride<2^W
  pages : (arc).pages<2^W
  pageStep : (arc).pageStride<2^W
  counts : (arc).counts+1<2^W
  lutAway : TickWorkspace.base u 14+2*V+26≤(arc).lut
  countsAway : TickWorkspace.base u 14+2*V+26≤(arc).counts
  header : 3+5*(fam).demands+4*(fam).supplies≤V
  portEnd : HistoryGatherExecution.portsEnd A<2^W
  tags : Fintype.card ((Fin 3→Bool)→F)≤2^W

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
/-- Public motif provenance identifies all three geometry parameters. The
physical S38 library span and fixed catalogue coefficient cover the scalar,
compactor and gather address tests before the first elected party is run. -/
theorem issued_layout (supported:B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (age:16≤u) (intrinsic:blockPageRate B≤u) (high:TickWorkspace.base u 19≤rom)
    (fits:rom+libraryWords B height<2^W) : q.IssuedLayout B rom height := by
  classical
  let shape:StaticMotif F→HistoryGatherBody.Geometry
    | .refresh s h pad _ _ _ => .refresh (2^s) h pad
    | .shrink .. => .refresh 0 0 0
  have mode:(fam).mode=.refresh (2^q.s) q.h q.pad:=(congrArg shape (B.public_refresh supported)).symm
  let dim:HistoryGatherBody.Geometry→ℕ
    | .refresh m _ _ => m
    | .shrink _ => 0
  have parties:(fam).parties=2^q.s:=congrArg dim mode
  have rate:gridPageRate (arity B) grid≤u:=(grid_page_rate_le_block B (by simp [grids])).trans intrinsic
  have us:u≤V:=(Nat.le_of_lt u.lt_two_pow_self).trans
    (Nat.pow_le_pow_right (by decide:0<2) (Nat.le_self_pow (by decide) u))
  have hdr:3+5*(fam).demands+4*(fam).supplies≤u:=by
    change 3+5*(grid).demand+4*(grid).supply≤u
    unfold gridPageRate at rate;omega
  have cap:((fam).motifs+2)*((fam).parties+2)*8*32≤u:=by
    change ((grid).motifs+2)*((grid).parties+2)*8*32≤u
    unfold gridPageRate at rate;omega
  have mono:(fam).parties+2≤((fam).motifs+2)*((fam).parties+2):=Nat.le_mul_of_pos_left _ (by omega)
  have uw:u≤u^10:=Nat.le_self_pow (by decide) u
  have mask:2^(fam).parties<2^W:=Nat.pow_lt_pow_right (by decide) (by omega)
  have old:TickWorkspace.base u 18≤rom:=by
    have:=TickWorkspace.apart (u:=u) (by decide:18<19);omega
  have whole:archiveWindow u rom (libraryWords B height):=⟨fits,.inr old⟩
  have regs:=mounted_arch_registers u B whole
  have last:= (issued_kind_window B q.tile supported (Fin.last q.tile.last) (0:Fin (2^q.s)) whole).1
  have grade:q.tile.last+1≤2^W:=by
    change (fam).kinds+7*(q.tile.last*2^q.s+0)+7<2^W at last
    have mult:=Nat.le_mul_of_pos_right q.tile.last (Nat.two_pow_pos q.s)
    omega
  have cnt:rom+StableCompactROMNative.size height+staticSize B+1<2^W:=by
    unfold libraryWords HistoryCompactorCounts.size at fits
    omega
  have big:32≤V:=by
    calc
      32=2^5:=by decide
      _≤2^(u^10):=Nat.pow_le_pow_right (by decide:0<2) (by omega)
  have sq:32*V≤V^2:=by rw [pow_two];exact Nat.mul_le_mul_right V big
  have quart:V^2≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have sep:TickWorkspace.base u 14+2*V+26≤rom:=by
    have h:=TickWorkspace.apart (u:=u) (by decide:14<19)
    change TickWorkspace.base u 14+V^4≤TickWorkspace.base u 19 at h
    omega
  have wide:TickWorkspace.base u 17+V^4<2^W:=
    TickWorkspace.word_space (by omega : 1≤u) (by change 17<V^4;omega)
  have mfit:1+(fam).demands+(fam).supplies≤V:=by omega
  have portFit:HistoryGatherExecution.portsEnd A<2^W:=by
    change TickWorkspace.base u 17+(1+(fam).demands+(fam).supplies)*V<2^W
    have h:=Nat.mul_le_mul_right V mfit
    rw [←pow_two] at h
    omega
  exact ⟨mode,parties,parties,rfl,rfl,grid_kernel_same grid u _ arc,cap.trans us,mask,grade,
    by change rom+StableCompactROMNative.size height+1<_;omega,
    regs.2.1,regs.2.2.1,regs.2.2.2.1,cnt,
    by change _≤rom+StableCompactROMNative.size height;omega,
    by change _≤rom+StableCompactROMNative.size height+staticSize B;omega,
    hdr.trans us,portFit,block_tags_at_age B intrinsic⟩

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt


namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HistoryStageBody.Physical
open RAM.HistoryPartyBatchExec RAM.HistoryRefreshEmitter RAM.NavigationNodeRows PhysicalStage
open NavigationDirectory CompressorPacking Native RefreshDemandRows RefreshStageNav
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {u K heads : ℕ} {cur ctr : Word (16*u^10)}
    (q : RefreshReceipt F K cur) (B : Block F) {height base : ℕ} {mem final : Memory (16*u^10)}
    (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (mounted : Mounted B height (16*u^10) base mem) (y : (q.move.next q.term).Site)
local notation "W" => 16*u^10
local notation "fam" => refreshFamily B base height
local notation "A" => layout u (archive B base height K) fam
local notation "z" => q.chosenBlock y
local notation "role" => (q.kernelSite y).1.2
local notation "kindId" => q.tile.winner (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input) z
local notation "party" => issuedParty q.tile q.hh q.rowSum q.sym q.conn kindId role
local notation "J" => (rawArm A (role).val).party
local notation "raw" => numeric mem
local notation "P" => CursorSpace.recordPointers q.entry
local notation "record" => (P).motif+(q.step.sites.ord y).val*6
local notation "ix" => (q.chosenIndex y).val
local notation "Q" => refreshBinaryFamily q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn

include supported mounted in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
/-- Reconstruct the actual selected party boot operands, including its library
kind, true histcount pointer and multiplicity, at either live input memory. -/
theorem active_registers
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds : RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (retained : ∀ x,heads≤x→x<q.entry.next.heap→mem x=final x)
    (banks : Banks) (baseNodes : banks.nodes=TickWorkspace.base u 44)
    (row : HistoryStageSetup.DirectoryRow banks q.step.sites.layer (q.step.sites.ord y) mem)
    (current : raw (TickWorkspace.base u 18)-1=q.step.sites.id y)
    (mask : 2^(fam).parties<2^W) (gradeFit : q.tile.last+1≤2^W) :
    HistoryPartyBatch.occupied J raw ∧ HistoryPartyBatch.incident J raw=record ∧
      HistoryPartyBatch.copies J raw=refreshBinaryCopies q.tile q.input z ∧
      raw (record+1)=(P).counts+ix*K ∧
      (∀ a:Fin K,mem (raw (record+1)+a.val)=HistogramRegister.words ((Q).rows q.fit)
        ((Q).sequence q.fit q.branch) (q.chosenIndex y) a) ∧
      (∀ a:Fin 7,mem (HistoryPartyBatch.shape J raw+a.val)=
        (((party).kind (arity B)).words a:Word W)) ∧ party∈(refreshGrid B).rows := by
  have rom:=issued_party_rom B mounted q.tile supported q.hh q.rowSum q.sym q.conn kindId role
  have sk (x:ℕ) (lo:q.cursor.heap≤x) (hi:x<q.entry.next.heap) : mem x=final x := retained x (bounds.header.trans lo) hi
  have bound : heads≤q.cursor.heap ∧ q.entry.next.heap≤cur.val ∧ cur.val<ctr.val:=⟨bounds.header,bounds.controls⟩
  let win:=Fin.cast rom.2.1.symm role
  have r:=q.incidence_at_entry (saved := saved) (bounds := bound) (retained := sk)
    fam rom.2.1 y banks baseNodes row current mask
  have ke : HistoryPartyBatch.kernel J raw=(P).kernel+(q.step.sites.ord y).val*5 := by
    change raw (TickWorkspace.base u 44+8*(raw (TickWorkspace.base u 18)-1)+5)=_
    rw [current]
    exact r.kernel
  have inc : HistoryPartyBatch.incident J raw=record := by
    change raw (HistoryPartyBatch.kernel J raw+4)+6*0=_
    rw [ke,Nat.mul_zero,Nat.add_zero];exact r.incident
  have occ : HistoryPartyBatch.occupied J raw :=
    (batch_occupied A mem win (role).val (by rw [ke];exact r.count) (by rw [inc];exact r.mask)).2 rfl
  have quotaLimit:=q.histogram.1
  rw [refreshBinaryFamily_motifs] at quotaLimit
  have off:=Nat.mul_le_mul_left K (q.chosenIndex y).isLt.le
  have top:=bounds.controls.1
  have heap:q.cursor.heap≤q.entry.next.heap:=by unfold entry;rw [heap_step];omega
  have ptrFit : (P).counts+ix*K<2^W:=by
    change q.cursor.dense+ix*K<_
    rw [Nat.mul_comm ix K]
    have word:=cur.isLt;omega
  have values:=q.elected_at_entry saved bound sk y gradeFit ptrFit
  have count : raw (record+3)=refreshBinaryCopies q.tile q.input z:=values 3
  have hist : raw (record+1)=(P).counts+ix*K:=values 1
  have kind : raw (record+2)=(kindId).val:=values 2
  have sh : HistoryPartyBatch.shape J raw=(fam).kinds+7*((kindId).val*2^q.s+(role).val) := by
    change (fam).kinds+7*(raw (HistoryPartyBatch.incident J raw+2)*(fam).parties+(role).val)=_
    rw [inc,kind,rom.2.1]
  refine ⟨occ,inc,?_,hist,?_,?_,rom.1⟩
  · simp only [HistoryPartyBatch.copies,ite_eq_left occ,inc,count]
  · intro a
    rw [hist,Nat.mul_comm ix K]
    have savedWord:=q.saved_histogram saved bounds (q.chosenIndex y) a
    have lower:=bounds.quota
    have hi:=Nat.mul_le_mul_left K (q.chosenIndex y).isLt
    rw [Nat.mul_succ] at hi
    have address : heads≤(P).counts+K*ix+a.val ∧ (P).counts+K*ix+a.val<q.entry.next.heap := by
      change heads≤q.cursor.dense+K*ix+a.val ∧ q.cursor.dense+K*ix+a.val<q.entry.next.heap
      have ha:=a.isLt;omega
    exact (retained _ address.1 address.2).trans savedWord
  · intro a
    rw [sh]
    exact rom.2.2.1 a

local notation "r" => refreshBinaryCopies q.tile q.input z
local notation "ckKind" => (party).kind (arity B)
local notation "Y" ck => (⟨J,ck,ckKind,mem⟩:HistoryPartyBatchExec.Build W)
local notation "lib" => HistoryStaticArchive.all F (arity B)

include supported mounted in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2300000 in
/-- Both active party builds read the emitted multiplicity and the catalog
selected by the current node’s archive. The histogram values are decoded at
the same boot image and indexed by the actual branch letters. -/
theorem active_boot (ck:Bool) (t:Fin (height+1))
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds : RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (retained : ∀ x,heads≤x→x<q.entry.next.heap→mem x=final x)
    (banks : Banks) (baseNodes : banks.nodes=TickWorkspace.base u 44)
    (row : HistoryStageSetup.DirectoryRow banks q.step.sites.layer (q.step.sites.ord y) mem)
    (current : raw (TickWorkspace.base u 18)-1=q.step.sites.id y)
    (mask : 2^(fam).parties<2^W) (gradeFit : q.tile.last+1≤2^W)
    (level : t.val=HistogramTileNetwork.siteHeight r (party).maxDigit) (size : 2^t.val<2^W)
    (work : StableCompactNativeBudget.budget t.val<2^W)
    (seedFit : (J).seed+37<2^W) (strideFit : HistoryStaticArchive.stride (arity B)≤2^W)
    (kindFit : ∀ j:Fin 7,(ckKind).words j<2^W)
    (libHigh : (J).seed+37≤base) (kindHigh : (J).seed+37≤(fam).kinds)
    (incHigh : (J).seed+37≤(P).motif) (quotaHigh : (J).seed+37≤(P).counts) :
    HistoryPartySpecialization.Reads (Y ck).regs (numeric (Y ck).bootImage) lib r t ∧
      (∀ j:Fin 7,numeric (Y ck).bootImage ((Y ck).regs.grid+j.val)=(ckKind).words j) ∧
      (∀ a:Fin (@Fintype.card ((Q).alphabet (q.chosenIndex y)) ((Q).finiteAlphabet _)),
        numeric (Y ck).bootImage (numeric (Y ck).bootImage ((Y ck).regs.incident+1)+a.val)=
        (((refreshBinaryBranchOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch)
          ((refreshBlockOrder q.input).symm (q.chosenIndex y))).val
            ((@Fintype.equivFin ((Q).alphabet (q.chosenIndex y)) ((Q).finiteAlphabet _)).symm a)).val) := by
  obtain ⟨active,inc,copies,hist,_,word,_⟩:=
    q.active_registers B supported mounted y saved bounds retained banks baseNodes row current mask gradeFit
  have count : raw (HistoryPartyBatch.incident J raw+3)=r:=by
    simpa only [HistoryPartyBatch.copies,ite_eq_left active] using copies
  have kind (j:Fin 7) : raw (HistoryPartyBatch.shape J raw+j.val)=(ckKind).words j :=
    (congrArg Fin.val (word j)).trans (Fin.val_cast_of_lt (kindFit j))
  have digit : raw (HistoryPartyBatch.shape J raw+4)=(party).maxDigit:=kind 4
  have incFree : (J).seed+37≤HistoryPartyBatch.incident J raw := by rw [inc];omega
  have kindFree : (J).seed+37≤HistoryPartyBatch.shape J raw :=
    kindHigh.trans (Nat.le_add_right _ _)
  have libFree : (J).seed+37≤(J).lutBase := libHigh.trans (Nat.le_add_right _ _)
  have countsFree : (J).seed+37≤(J).countBase := (libHigh.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have boot:=elected_reads J ckKind mem ck lib r (party).maxDigit t active count digit level size seedFit rfl
    strideFit kind (stored_scalar B mounted.words) (stored_counts B mounted.words)
    (fun j=>(compactor_counts_le F t j).trans_lt work) (.inr incFree) (.inr kindFree) (.inr libFree) (.inr countsFree)
  refine ⟨boot.1,boot.2,?_⟩
  have ptr: raw (HistoryPartyBatch.incident J raw+1)=(P).counts+K*ix:=by
    rw [inc,hist,Nat.mul_comm ix K]
  apply elected_histogram J ckKind mem ck active seedFit ((P).counts+K*ix) _ _ ptr _
    (.inr incFree) (.inr (by omega))
  intro a
  have limit:=q.histogram.1
  rw [refreshBinaryFamily_motifs] at limit
  have quotaLower:=bounds.quota
  have heapEnd : q.cursor.heap≤q.entry.next.heap := by unfold entry;rw [heap_step];omega
  have seq:=Nat.mul_le_mul_left K (q.chosenIndex y).isLt
  rw [Nat.mul_succ] at seq
  have ha:=a.isLt.trans_le (q.fit.1 (q.chosenIndex y))
  have window : heads≤(P).counts+K*ix+a.val ∧ (P).counts+K*ix+a.val<q.entry.next.heap := by
    change heads≤q.cursor.dense+K*ix+a.val ∧ q.cursor.dense+K*ix+a.val<q.entry.next.heap;omega
  exact (congrArg Fin.val (retained _ window.1 window.2)).trans
    (q.saved_quota saved bounds (q.chosenIndex y) a)

include supported mounted in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
/-- Both physical batches of an issued refresh root have their literal finite seed and
table bounds. The predecessor's RAM supplies the selected count row and the archive
supplies the kind table and the two finite ROMs. -/
theorem active_seed (ck:Bool) (t:Fin (height+1))
    (saved:SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds:RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (retained:∀ x,heads≤x→x<q.entry.next.heap→mem x=final x)
    (banks:Banks) (baseNodes:banks.nodes=TickWorkspace.base u 44)
    (row:HistoryStageSetup.DirectoryRow banks q.step.sites.layer (q.step.sites.ord y) mem)
    (current:raw (TickWorkspace.base u 18)-1=q.step.sites.id y)
    (age:16≤u) (nodeFit:q.step.sites.id y<(volume u)^2)
    (cap:((fam).motifs+2)*((fam).parties+2)*8*32≤volume u)
    (mask:2^(fam).parties<2^W) (gradeFit:q.tile.last+1≤2^W)
    (headerHigh:TickWorkspace.base u 19≤heads) (libHigh:TickWorkspace.base u 19≤base)
    (libFit:base+libraryWords B height<2^W)
    (level:t.val=HistogramTileNetwork.siteHeight r (party).maxDigit) (size:2^t.val≤volume u)
    (work:StableCompactNativeBudget.budget t.val≤volume u) (countSmall:r≤volume u)
    (kindSmall:∀ a:Fin 7,(ckKind).words a≤volume u)
    (alphabet:(ckKind).letters≤K) :
    ElectedSeed u (Y ck) ∧
    HistoryPartySpecialization.Reads (Y ck).regs (numeric (Y ck).bootImage) lib r t ∧
    ∀ a:Fin (@Fintype.card ((Q).alphabet (q.chosenIndex y)) ((Q).finiteAlphabet _)),
      numeric (Y ck).bootImage (numeric (Y ck).bootImage ((Y ck).regs.incident+1)+a.val)=
        (((refreshBinaryBranchOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch)
          ((refreshBlockOrder q.input).symm (q.chosenIndex y))).val
            ((@Fintype.equivFin ((Q).alphabet (q.chosenIndex y)) ((Q).finiteAlphabet _)).symm a)).val := by
  let v:=volume u
  let loc:=q.step.sites.id y
  have rom:=issued_party_rom B mounted q.tile supported q.hh q.rowSum q.sym q.conn kindId role
  let win:Fin (fam).parties:=Fin.cast rom.2.1.symm role
  have mobs : 0 < (fam).motifs := Nat.zero_lt_one
  have winloc:PartyWindow u J:=PartyWindow.of_layout (archive B base height K) fam 0 (role).val age mobs
    (show (role).val < (fam).parties from (role).isLt.trans_eq rom.2.1.symm) cap
  have big:1024≤v:=Nat.pow_le_pow_right (by decide:0<2) ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) u))
  have slack:30*v≤TickWorkspace.stride u:=calc
    _≤v*v:=Nat.mul_le_mul_right v (by omega)
    _=v^2:=(pow_two v).symm
    _≤v^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have a14:=TickWorkspace.apart (u:=u) (by decide:14<18)
  have a18:=TickWorkspace.apart (u:=u) (by decide:18<19)
  have last:=TickWorkspace.word_space (u:=u) (i:=19) (by omega) (by omega)
  have wfit:v<2^W:=by omega
  have whole:archiveWindow u base (libraryWords B height):=⟨libFit,.inr (by omega)⟩
  have registers:=mounted_arch_registers u B whole
  have top:=bounds.controls.1
  have endHeap:q.cursor.heap≤q.entry.next.heap:=by change _≤(allocate K _ _).next.heap;rw [heap_step];omega
  have issued:=q.active_registers B supported mounted y saved bounds retained banks baseNodes row current mask gradeFit
  obtain ⟨live,inc,copyEq,histEq,quota,words,member⟩:=issued
  have copies:raw (HistoryPartyBatch.incident J raw+3)=r:=by
    simpa only [HistoryPartyBatch.copies,ite_eq_left live] using copyEq
  have kinds (a:Fin 7):raw (HistoryPartyBatch.shape J raw+a.val)=(ckKind).words a:=
    (congrArg Fin.val (words a)).trans (Fin.val_cast_of_lt ((kindSmall a).trans_lt wfit))
  have sk (x:ℕ) (lo:q.cursor.heap≤x) (hi:x<q.entry.next.heap):mem x=final x:=retained x (bounds.header.trans lo) hi
  have limit:heads≤q.cursor.heap ∧ q.entry.next.heap≤cur.val ∧ cur.val<ctr.val:=⟨bounds.header,bounds.controls⟩
  have incidence := q.incidence_at_entry (saved := saved) (bounds := limit) (retained := sk)
    fam rom.2.1 y banks baseNodes row current mask
  have geometry:=q.incidence_geometry y age (headerHigh.trans bounds.header) bounds.controls.1 nodeFit
  have fitRows:=q.histogram.1
  rw [refreshBinaryFamily_motifs] at fitRows
  have idxFit:=Nat.mul_le_mul_left K (q.chosenIndex y).isLt
  rw [Nat.mul_succ] at idxFit
  have histFit:(P).counts+ix*K<2^W:=by
    change q.cursor.dense+ix*K<2^W;rw [Nat.mul_comm ix K];have:=cur.isLt;omega
  have selected:=q.elected_at_entry saved limit sk y gradeFit histFit
  have kindIndex:raw (record+2)=(kindId).val:=selected 2
  have sh:HistoryPartyBatch.shape J raw=(fam).kinds+7*((kindId).val*2^q.s+(role).val):=by
    change (fam).kinds+7*(raw (HistoryPartyBatch.incident J raw+2)*(fam).parties+(role).val)=_
    rw [inc,kindIndex,rom.2.1]
  have gh:=issued_kind_window B q.tile supported kindId role whole
  have recordRange:archiveWindow u record 6:=by
    have tail:=q.record_interval .motif (Records.rowOrder (1+q.h+q.pad) .motif (q.kernelSite y,(5:Fin 6)))
    have ord:(Records.rowOrder (1+q.h+q.pad) .motif (q.kernelSite y,(5:Fin 6))).val=(q.step.sites.ord y).val*6+5:=by
      rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,q.kernelSite_index];rfl
    rw [ord] at tail
    change q.cursor.heap ≤ (P).motif+((q.step.sites.ord y).val*6+5) ∧
      (P).motif+((q.step.sites.ord y).val*6+5) < q.entry.next.heap at tail
    have beg:=q.record_interval .motif (Records.rowOrder (1+q.h+q.pad) .motif (q.kernelSite y,(0:Fin 6)))
    have ord₀:(Records.rowOrder (1+q.h+q.pad) .motif (q.kernelSite y,(0:Fin 6))).val=(q.step.sites.ord y).val*6:=by
      rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,q.kernelSite_index];rfl
    rw [ord₀] at beg
    change q.cursor.heap≤record ∧ _ at beg
    have:=bounds.header
    have:=cur.isLt
    exact ⟨by omega,.inr (by omega)⟩
  have quotaZone:archiveWindow u ((P).counts+ix*K) (ckKind).letters:=by
    change archiveWindow u (q.cursor.dense+ix*K) (ckKind).letters
    rw [Nat.mul_comm ix K]
    have:=cur.isLt;have:=bounds.quota;exact ⟨by omega,.inr (by omega)⟩
  have keepKind:archiveWindow u ((fam).kinds+7*((kindId).val*(fam).parties+win.val)) 7:=by
    change archiveWindow u ((fam).kinds+7*((kindId).val*(fam).parties+(role).val)) 7
    simpa only [rom.2.1] using gh
  have anchors:=IncidenceRead.elected u (archive B base height K) fam loc win mem _ _ incidence geometry.1 ck (kindId).val
    kindIndex recordRange keepKind
  have center:TickWorkspace.base u 19≤(P).motif:=by
    have bounds0:=CursorSpace.retained_addresses (c:=q.cursor) (K:=K) (v:=Fintype.card q.input.Base)
      (a:=q.s) (t:=q.rem) (h:=q.h) (pad:=q.pad)
    have shape:=CursorSpace.record_layout (c:=q.cursor) (K:=K) (v:=Fintype.card q.input.Base)
      (a:=q.s) (t:=q.rem) (h:=q.h) (pad:=q.pad)
    have low : q.cursor.heap+3*(Fintype.card q.input.Base*2^q.rem)≤(P).kernel:=bounds0.2.1
    have mid : (P).kernel+(Fintype.card q.input.Base*2^q.s*2^q.rem)*5=(P).motif:=shape.2.1
    have:=bounds.header;omega
  have shapeBegin:base≤(fam).kinds:=by
    change base≤base+StableCompactROMNative.size height+staticSize B+HistoryCompactorCounts.size height+
      ((List.ofFn (shrinkGrid B)).map Grid.size).sum;omega
  have boot:=q.active_boot B supported mounted y ck t saved bounds retained banks baseNodes row current mask gradeFit
    level (size.trans_lt wfit) (work.trans_lt wfit) winloc.seed_room registers.2.1.le
    (fun a=>(kindSmall a).trans_lt wfit)
    (by change TickWorkspace.base u 14+v+37≤base;omega)
    (by change TickWorkspace.base u 14+v+37≤(fam).kinds;omega)
    (by change TickWorkspace.base u 14+v+37≤(P).motif;omega)
    (by change TickWorkspace.base u 14+v+37≤q.cursor.dense;have:=bounds.quota;omega)
  let lib₀:=base+StableCompactROMNative.size height
  let count₀:=lib₀+staticSize B
  have hL:archiveWindow u lib₀ (staticSize B):=whole.sub (by dsimp [lib₀];omega)
    (by unfold libraryWords;dsimp [lib₀];omega)
  have hC:archiveWindow u count₀ (HistoryCompactorCounts.size height):=whole.sub (by dsimp [count₀,lib₀];omega)
    (by unfold libraryWords;dsimp [count₀,lib₀];omega)
  have hP:archiveWindow u base (StableCompactROMNative.size height):=whole.sub le_rfl (by unfold libraryWords;omega)
  let slot:=if ck then (ckKind).selectorPage else (ckKind).tilePage
  have valid:slot<HistoryStaticArchive.count F (arity B):=by
    have inhabited : 0 < HistoryStaticArchive.count F (arity B) := by
      change 0 < Fintype.card (HistoryStaticArchive.Entry F (arity B))
      exact Fintype.card_pos_iff.mpr ⟨⟨0, fun _ => 0⟩⟩
    cases ck <;> dsimp [slot,Party.kind] <;> split <;> first | exact Fin.isLt _ | exact inhabited
  have cut:=Nat.mul_le_mul_left (HistoryStaticArchive.stride (arity B)) valid
  rw [Nat.mul_succ,Nat.mul_comm (HistoryStaticArchive.stride (arity B)) (HistoryStaticArchive.count F (arity B))] at cut
  have strideFloor:2≤HistoryStaticArchive.stride (arity B):=by unfold HistoryStaticArchive.stride;omega
  have lutRead:archiveWindow u ((J).lutBase+(J).lutStride*slot) 2:=by
    apply hL.sub (by change lib₀≤lib₀+_;omega)
    change lib₀+HistoryStaticArchive.stride (arity B)*slot+2≤lib₀+HistoryStaticArchive.count F (arity B)*HistoryStaticArchive.stride (arity B)
    omega
  have countRead:archiveWindow u ((J).countBase+2*t.val) 2:=by
    apply hC.sub (by change count₀≤count₀+_;omega)
    change count₀+2*t.val+2≤count₀+2*(height+1);have:=t.isLt;omega
  have endPage : (J).compBase+(J).compStride*t.val<2^W:=by
    have ht:=Nat.mul_le_mul_left (StableCompactROMPool.page height 12) t.isLt
    rw [Nat.mul_succ,Nat.mul_comm (StableCompactROMPool.page height 12) (height+1)] at ht
    have h:=hP.1;change base+(height+1)*StableCompactROMPool.page height 12<2^W at h
    change base+StableCompactROMPool.page height 12*t.val<2^W;omega
  refine ⟨?_,boot.1,boot.2.2⟩
  apply elected_seed_of_reads u (archive B base height K) fam loc 0 win ck (Y ck) lib t r
    rfl rfl age nodeFit mobs cap current live copies kinds boot.1 boot.2.1 anchors.2.2.2
  · change archiveWindow u (HistoryPartyBatch.incident J raw) 4
    rw [inc]
    exact recordRange.sub le_rfl (by omega)
  · change archiveWindow u (HistoryPartyBatch.shape J raw) 7
    rw [sh]
    exact gh
  · exact lutRead
  · exact countRead
  · change archiveWindow u (raw (HistoryPartyBatch.incident J raw+1)) (ckKind).letters
    rw [inc,histEq]
    exact quotaZone
  · exact registers
  · exact endPage
  · exact countSmall
  · exact kindSmall
  · exact size
  · exact work
  · exact level

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HistoryGatherExecution RAM.HistoryGatherBody
open PhysicalStage NavigationDirectory CompressorPacking Native RefreshDemandRows RefreshStageNav RefreshTies
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W K endHeaders : ℕ} {cur ctr : Word W} (q : RefreshReceipt F K cur)
local notation "m" => 2^q.s
local notation "v" => Fintype.card q.input.Base
local notation "l" => 2^q.rem
local notation "C" => oldColumns q.cursor v m
local notation "bound" => q.entry.next.heap

/-- The input graph and its split columns are reopened with the header of this
refresh even when the traversal cursor points at a different stage. -/
theorem source_at_entry {final mem : Memory W}
    (saved : SavedFrame cur ctr endHeaders q.entry.next.header bound q.out final)
    (limits : endHeaders≤q.cursor.heap ∧ bound≤cur.val ∧ cur.val<ctr.val)
    (graphLow : endHeaders≤q.cursor.graph) (widthLow : endHeaders≤q.cursor.width)
    (body : ∀ i,(q.cursor.header ≤ i ∧ i<q.entry.next.header ∨ endHeaders ≤ i)→i<bound→mem i=final i)
    (r : Fin 7→Word W) (head : (r 0).val=q.cursor.header) :
    RefreshParty.Source mem r (numberedRefreshGraph q.input) C (q.entry.words 12)
      (numberedRefreshWidths q.input) := by
  have keep (i : ℕ) (range : q.cursor.header ≤ i ∧ i<q.entry.next.header ∨ endHeaders ≤ i) (last : i<bound) :
      mem i=q.out i := (body i range last).trans (saved i (by omega) (by omega) (range.imp And.right id) last)
  have oldEnd : q.cursor.heap≤bound:=by change _≤(allocate K _ _).next.heap;rw [heap_step];omega
  have span:=q.issued.oldRanges
  have order:=CursorSpace.ordered (c:=q.cursor) (K:=K) («v»:=v) (a:=q.s) (t:=q.rem) (h:=q.h) (pad:=q.pad)
  have headRoom:=q.issued.headerBelow
  apply (q.issued.archivedSource r head).reopen rfl
  · intro j hj hi
    rw [head]
    exact keep _ (.inl ⟨Nat.le_add_right ..,by change q.cursor.header+j<q.cursor.header+64;omega⟩) (by omega)
  · intro i lo hi
    exact keep i (.inr (graphLow.trans lo)) (hi.trans_le (span.1.trans oldEnd))
  · intro i lo hi
    exact keep i (.inr (widthLow.trans lo)) (hi.trans_le (span.2.trans oldEnd))
  · intro i lo hi
    have first:q.cursor.heap+3*(v*l)=q.entry.words 3:=order.1
    have next:q.entry.words 3+v*l*m*q.h=q.entry.words 12:=order.2.1
    have last:q.entry.words 12+3*(C).rows=(nextColumns q.entry v m q.h q.pad).graph:=order.2.2.1
    change q.entry.words 12 ≤ i at lo
    change i < q.entry.words 12+3*(C).rows at hi
    have splitStart : q.cursor.heap ≤ q.entry.words 12 :=
      ((Nat.le_add_right _ _).trans_eq first).trans ((Nat.le_add_right _ _).trans_eq next)
    have graphEnd : (nextColumns q.entry v m q.h q.pad).graph ≤
        (nextColumns q.entry v m q.h q.pad).widths :=
      (Nat.le_add_right _ _).trans_eq order.2.2.2.1
    have widthEnd : (nextColumns q.entry v m q.h q.pad).widths ≤ q.entry.next.heap :=
      (Nat.le_add_right _ _).trans order.2.2.2.2
    exact keep i (.inr (limits.1.trans (splitStart.trans lo)))
      ((hi.trans_eq last).trans_le (graphEnd.trans widthEnd))

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

end OAI
