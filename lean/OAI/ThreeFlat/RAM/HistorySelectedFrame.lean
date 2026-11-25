import OAI.ThreeFlat.RAM.HistoryStageResult
import OAI.ThreeFlat.RAM.HistorySelectedInterior

namespace OAI
/-! # Memory preserved by the selected physical stage at its fixed node index -/

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open HistoryPartyBatchExec HistoryStageBody HistoryStageSetup HistoryStageResult
open HistoryStageRoot HistoryBoundedBody HistoryReadyTape Diagonal.TickWorkspace
open scoped Fin.CommRing BigOperators
noncomputable section
variable {W : ℕ} (u i : ℕ) (archive : Archive) (family : Family) (m : Memory W)
local notation "A" => layout u archive family
local notation "cap" => family.childBound
local notation "V" => volume u
local notation "X" => HistoryStageSetup.run A cap m
local notation "T" => numInput A cap (numeric m)
local notation "count" => HistoryStageRoot.childCount T (numeric m)
local notation "start" => base u 12+i*V^2
local notation "stop" => base u 12+(i+1)*V^2

/-- At the actual word width one selected node, including its fixed scratch and
the S45 owner directory, lies strictly below the address modulus. -/
theorem selected_node_space (age : 2≤u) (node : i<V^2) (children : family.childBound≤V) :
    162≤V ∧ V+400+32*(cap+1)≤ Diagonal.TickWorkspace.stride u ∧ stop≤base u 13 ∧
    base u 13+8*i+8≤base u 14 ∧ base u 46<2^(16*u^10) := by
  have time : 8≤u^10 := by
    have h:=Nat.pow_le_pow_left age 10
    norm_num at h
    omega
  have scale : 256≤V := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) time
  have pos : 0<V:=by omega
  have sq : V^2≤ Diagonal.TickWorkspace.stride u := Nat.pow_le_pow_right pos (by decide : 2≤4)
  have mul : 35*V≤V^2 := by
    rw [pow_two];exact Nat.mul_le_mul_right V (by omega)
  have strideEq : Diagonal.TickWorkspace.stride u=V^2*V^2 := by change V^4=_;ring
  have off : (i+1)*V^2≤V^2*V^2 := Nat.mul_le_mul_right (V^2) (show i+1≤V^2 from node)
  have depth : 8≤V^2 := by
    have h:=Nat.le_self_pow (by decide : 2≠0) V;omega
  have upper:=Nat.mul_le_mul depth (show i+1≤V^2 from node)
  have counter : base u 46<2^(16*u^10) := by
    have exp : (4:ℕ)*u^10+12*u^10=16*u^10:=by ring
    rw [←exp,Nat.pow_add]
    have first : (2:ℕ)^(4*u^10)=V^4 := by rw [Nat.mul_comm 4 _,Nat.pow_mul];rfl
    have hi : 47<(2:ℕ)^(12*u^10) := lt_of_lt_of_le (by decide : 47<(2:ℕ)^6)
      (Nat.pow_le_pow_right (by decide) (by omega))
    rw [first]
    change 47*V^4<V^4*_
    rw [Nat.mul_comm 47]
    exact Nat.mul_lt_mul_of_pos_left hi (Nat.pow_pos pos)
  refine ⟨by omega,by omega,?_,?_,counter⟩
  · unfold base;rw [strideEq];omega
  · unfold base;rw [strideEq];omega

/-- The size obligations are about the genuine placement of the current stage. The
endpoint and relocation arrays are recorded in the physical stage's own order. -/
structure JoinRanges {F : Type*} {n : ℕ} {arity : Fin n→ℕ} (N : ∀ k,BitNetwork F (arity k))
    (q : Fin n→HistoryJoinScan.Header ℕ) : Prop where
  index : (T).id=i
  childCount : count≤cap
  scratch : V+400+32*(cap+1)≤ Diagonal.TickWorkspace.stride u
  arena : stop≤base u 13
  cache : base u 13+8*i+8≤base u 14
  words : base u 19<2^W
  ends : ∀ k,k<count → start≤Endpoints.toAddr T (numeric m) k ∧
    Endpoints.toAddr T (numeric m) k+Endpoints.width T (numeric m) k≤ stop
  pins : ∀ k,base u 18+2≤(q k).pins ∧ (q k).pins+arity k≤base u 19
  rows : ∀ k,start≤(q k).dest ∧ (q k).dest+4*(N k).cells≤ stop

variable {F : Type*} {n p h : ℕ} {arity : Fin n→ℕ} (N : ∀ k,BitNetwork F (arity k))
    (wire : ∀ k,Fin (arity k)→BitSource h p) (id : ((Fin 3→Bool)→F)→ℕ)
    (q : Fin n→HistoryJoinScan.Header ℕ)

/-- Build the physical write spans from the total endpoint, pin and cell volumes and
the genuine prefix offsets of the chronological join. The stream and external arrays use
sectors 160 and 161 of this node in the S12 arena. -/
theorem JoinRanges.of_layout (index : (T).id=i) (children : count≤cap) (large : 162≤V)
    (scratch : V+400+32*(cap+1)≤ Diagonal.TickWorkspace.stride u) (arena : stop≤base u 13)
    (cache : base u 13+8*i+8≤base u 14) (words : base u 19<2^W)
    (ext : HistoryStageRoot.prefix T (numeric m) count Result.extCount≤V)
    (pins : (∑ k,arity k)≤V) (cells : 4*(∑ k,(N k).cells)≤V)
    (pinAt : ∀ k,(q k).pins=(T).maps+Diagonal.HistoryContraction.Tree.before arity k)
    (rowAt : ∀ k,(q k).dest=(T).stream+4*Diagonal.HistoryContraction.Tree.before (fun j=>(N j).cells) k) :
    JoinRanges u i archive family m N q := by
  have sector (bank : ℕ) :
      HistoryScratch.sector family.motifs family.parties ⟨0,0,5,bank⟩=160+bank := by
    simp [HistoryScratch.sector]
  have endpoints : (T).ext=start+161*V := by
    change base u 12+((T).id*V+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,1⟩)*V+0=_
    rw [sector,index]
    ring
  have stream : (T).stream=start+160*V := by
    change base u 12+((T).id*V+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,0⟩)*V+0=_
    rw [sector,index]
    ring
  have sectors : start+162*V≤ stop := by
    have bound:=Nat.mul_le_mul_right V large
    nlinarith only [bound]
  have scratchSix : 6*V≤ Diagonal.TickWorkspace.stride u := by
    have positive : 0<V := by omega
    calc
      6*V≤V*V := Nat.mul_le_mul_right _ (by omega)
      _=V^2 := by ring
      _≤V^4 := Nat.pow_le_pow_right positive (by decide)
  refine ⟨index,children,scratch,arena,cache,words,?_,?_,?_⟩
  · intro k hk
    have endpointBound : HistoryStageRoot.prefix T (numeric m) k Result.extCount+
        Endpoints.width T (numeric m) k≤HistoryStageRoot.prefix T (numeric m) count Result.extCount := by
      unfold HistoryStageRoot.prefix Endpoints.width Endpoints.info
      rw [←Finset.sum_range_succ]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono hk)
    unfold Endpoints.toAddr
    rw [endpoints]
    constructor <;> omega
  · intro k
    rw [pinAt]
    have next:=Diagonal.HistoryContraction.Tree.prefix_next_le arity k
    change base u 18+2≤base u 18+5*V+_ ∧ base u 18+5*V+_+arity k≤base u 19
    unfold base
    constructor <;> omega
  · intro k
    rw [rowAt,stream]
    have next:=Nat.mul_le_mul_left 4
      (Diagonal.HistoryContraction.Tree.prefix_next_le (fun j=>(N j).cells) k)
    constructor <;> omega

/-- Endpoints, mapped input pins and compiled rows each occupy their own full-sector
slice. The three conclusions retain the sharper separation inside the current node. -/
theorem selected_slices
    (ext : HistoryStageRoot.prefix T (numeric m) count Result.extCount≤V)
    (pins : (∑ k,arity k)≤V) (cells : 4*(∑ k,(N k).cells)≤V)
    (pinAt : ∀ k,(q k).pins=(T).maps+Diagonal.HistoryContraction.Tree.before arity k)
    (rowAt : ∀ k,(q k).dest=(T).stream+4*Diagonal.HistoryContraction.Tree.before (fun j=>(N j).cells) k) :
    (∀ k,k<count→(T).ext≤Endpoints.toAddr T (numeric m) k ∧
      Endpoints.toAddr T (numeric m) k+Endpoints.width T (numeric m) k≤(T).ext+V) ∧
    (∀ k,(T).maps≤(q k).pins ∧ (q k).pins+arity k≤(T).maps+V) ∧
    ∀ k,(T).stream≤(q k).dest ∧ (q k).dest+4*(N k).cells≤(T).stream+V := by
  refine ⟨?_,?_,?_⟩
  · intro k hk
    have prefixBound : HistoryStageRoot.prefix T (numeric m) k Result.extCount+
        Endpoints.width T (numeric m) k≤HistoryStageRoot.prefix T (numeric m) count Result.extCount := by
      unfold HistoryStageRoot.prefix Endpoints.width Endpoints.info
      rw [←Finset.sum_range_succ]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono hk)
    unfold Endpoints.toAddr
    constructor <;> omega
  · intro k
    rw [pinAt]
    have h:=Diagonal.HistoryContraction.Tree.prefix_next_le arity k
    constructor <;> omega
  · intro k
    rw [rowAt]
    have h:=Nat.mul_le_mul_left 4 (Diagonal.HistoryContraction.Tree.prefix_next_le (fun j=>(N j).cells) k)
    constructor <;> omega

/-- The physical bank holding the just-completed kernel, before it is joined to the
old children. Bank zero holds its compiled rows and bank one its four metadata words. -/
def kernelLocal (mode : HistoryGatherBody.Geometry) (bank : ℕ) : HistoryScratch.Local :=
  match mode with
  | .shrink _ => ⟨0,0,4,bank⟩
  | .refresh .. => ⟨2,0,3,bank⟩

def kernelBase (bank : ℕ) :=
  HistoryScratch.atWord (base u 12) V family.motifs family.parties i (kernelLocal family.mode bank) 0

theorem kernel_pointer (index : (T).id=i) : (T).kernel=kernelBase u i family 1 := by
  cases tag : family.mode <;> simp only [numInput,layout,tag,kernelBase,kernelLocal] <;>
    change HistoryScratch.atWord _ _ _ _ (T).id _ 0=HistoryScratch.atWord _ _ _ _ i _ 0 <;> rw [index]

/-- Both kernel banks lie inside the same node. They are disjoint from the entire
new gate and endpoint sectors, on opposite sides of those sectors for the two modes. -/
theorem kernel_sectors (index : (T).id=i) (capacity : (family.motifs+2)*(family.parties+2)*8*32≤V)
    (refresh : ∀ x y z,family.mode=.refresh x y z→0<family.motifs) (bank : ℕ) (live : bank≤1) :
    let ptr:=kernelBase u i family bank
    start ≤ ptr ∧ ptr+V ≤ stop ∧ (ptr+V ≤ (T).stream ∨ (T).ext+V ≤ ptr) := by
  intro ptr
  let sect:=HistoryScratch.sector family.motifs family.parties (kernelLocal family.mode bank)
  have sch : sect<V := (HistoryScratch.sector_lt (x:=kernelLocal family.mode bank) (by
    cases tag : family.mode with
    | shrink k => simp [kernelLocal,HistoryScratch.Local.Valid]; omega
    | refresh x y z => have nonzero:=refresh x y z tag;simp [kernelLocal,HistoryScratch.Local.Valid]; omega)).trans_le capacity
  have separated : sect+1 ≤ 160 ∨ 162 ≤ sect := by
    cases tag : family.mode <;>
      simp only [sect,kernelLocal,tag,HistoryScratch.sector,Nat.zero_mul,Nat.zero_add,Nat.add_zero] <;> omega
  have ar : ptr=start+sect*V := by dsimp [ptr,kernelBase,sect,HistoryScratch.atWord];ring
  have addresses := stage_addresses u 0 cap archive family (numeric m) i index (Nat.zero_le i)
  have stream : (T).stream=start+160*V := by
    simpa only [streamAt, ite_eq_right (Nat.not_lt.mpr (Nat.zero_le i))] using addresses.1
  have ends : (T).ext=start+161*V := calc
    _ = streamAt u 0 i+V := addresses.2
    _ = start+161*V := by
      simp only [streamAt, ite_eq_right (Nat.not_lt.mpr (Nat.zero_le i))]
      ring
  have high:=Nat.mul_le_mul_right V sch
  rw [ar,stream,ends]
  refine ⟨by omega,by nlinarith only [high],?_⟩
  rcases separated with shrink|cloud
  · left;have h:=Nat.mul_le_mul_right V shrink;nlinarith only [h]
  · right;have h:=Nat.mul_le_mul_right V cloud;nlinarith only [h]

/-- A child ID read from the current S44 directory indexes a previous S13 record. -/
theorem previous_cache_before (index : (T).id=i) (k : ℕ)
    (earlier : (numeric m) ((numeric m) (HistoryStageRoot.node T+3)+k)< i) :
    childPtr T (numeric m) k+6≤bankBase A cap T .result := by
  change base u 13+8*((numeric m) ((numeric m) (HistoryStageRoot.node T+3)+k))+6≤base u 13+8*(T).id
  rw [index];omega

/-- Actual rows and endpoint words in an older selected node end by the beginning
of this node even for two consecutive chronological IDs. -/
theorem previous_stream_before {j address len : ℕ} (earlier : j< i)
    (parentRoom : address+len≤base u 12+(j+1)*V^2) : address+len ≤ start :=
  parentRoom.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ earlier) _)

private theorem end_range (B : JoinRanges u i archive family m N q)
    {job : Job W} (member : job∈(X).endpointJobs) : start≤job.start ∧ job.finish ≤ stop := by
  change job ∈ (List.range count).map _ at member
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp member
  exact B.ends k (List.mem_range.mp hk)

/-- All semantically unused variables in a job's word function drop out of its
write range. Pin maps occupy the later scratch and the gate rows occupy this node. -/
theorem join_late_writes (B : JoinRanges u i archive family m N q) {a : ℕ} (safe : OutsideNode u i a) :
    LateWrites X (Tape.tape N wire id q) a := by
  let S:=Diagonal.TickWorkspace.stride u
  have small : V+400+32*(cap+1)≤S := B.scratch
  have word : 20*S<2^W := B.words
  have countBound:=B.childCount
  have controlBound : loc A 22<2^W := by change 15*S+V+64+22<2^W;omega
  have seedBound : (A).party.seed+7<2^W := by change 15*S+V+7<2^W;omega
  have left (lo hi : ℕ) (startRange : 15*S≤lo) (stopRange : hi≤19*S) : a<lo ∨ hi≤a :=
    safe.scratch_range startRange (show hi≤20*S by omega) (Or.inl stopRange)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change a ≠ ((loc A 22 : ℕ) : Word W).val
    rw [Fin.val_cast_of_lt controlBound]
    have out:=left (loc A 22) (loc A 22+1) (by change 15*S≤15*S+V+64+22;omega)
      (by change 15*S+V+64+22+1≤19*S;omega)
    omega
  · intro job member
    have span:=end_range u i archive family m N q B member
    exact safe.arena_range span.1 span.2
  · change a<15*S+V ∨ 15*S+V+9≤a
    exact left _ _ (by omega) (by omega)
  · change a<16*S ∨ 16*S+14*(count+1)≤a
    exact left _ _ (by omega) (by omega)
  · change a<17*S ∨ 17*S+7*(count+1)≤a
    exact left _ _ (by omega) (by omega)
  · change a≠(((A).party.seed+7:ℕ):Word W).val
    rw [Fin.val_cast_of_lt seedBound]
    have out:=left ((A).party.seed+7) ((A).party.seed+7+1) (by change 15*S≤15*S+V+7;omega)
      (by change 15*S+V+7+1≤19*S;omega)
    omega
  · intro job member
    change job ∈ (List.finRange n).flatMap (fun k => Tape.jobs N wire id (q k) k) at member
    obtain ⟨k,_,hk⟩:=List.mem_flatMap.mp member
    simp only [Tape.jobs,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    · have afterCursor : 19*S+2 ≤ (q k).pins := (B.pins k).1
      have afterScratch : 15*S ≤ (q k).pins := by omega
      exact safe.scratch_range afterScratch (B.pins k).2 (Or.inr afterCursor)
    · exact safe.arena_range (B.rows k).1 (B.rows k).2

/-- Complete native stage-root memory transfer, from prelude through the generated
endpoint jobs, pin relocations and the final six-column S13 write. -/
theorem join_output_frame (B : JoinRanges u i archive family m N q)
    (src : SourceCells A cap T (numeric m) W) (a : ℕ) (safe : OutsideNode u i a) :
    adjust A cap T .result ((X).compiled.output (Tape.tape N wire id q)) a=m a := by
  let S:=Diagonal.TickWorkspace.stride u
  have small : V+400+32*(cap+1)≤S := B.scratch
  have word : 20*S<2^W := by simpa [base,S] using B.words
  have vpos : 0<S := by dsimp [S,Diagonal.TickWorkspace.stride];positivity
  have lim : limit A cap≤base u 15 := by
    change 15*S+V+64+55+4*(cap+1)+5*(cap+1)+3*cap+7*cap≤16*S;omega
  have argsLow : base u 14≤args A := by change 15*S≤15*S+V+64+0;omega
  have prep : External A cap a := safe.scratch_range argsLow
    (by change _≤20*S;change _≤16*S at lim;omega) (Or.inl (by change _≤19*S;change _≤16*S at lim;omega))
  have mountedAt:=((((((phase_frames A cap m B.childCount (src.node 4).2).2).2).2).2).2).2 a prep
  have key : bankBase A cap T .result=base u 13+8*i := by
    change base u 13+8*(T).id=base u 13+8*i
    rw [B.index]
  have counter : loc A 22<2^W := by change 15*S+V+64+22<2^W;omega
  have ptrJobs (job : Job W) (hj : job∈(X).endpointJobs) :
      HistoryStageBody.hub A+6<job.start ∨ job.finish≤HistoryStageBody.hub A+6 := by
    right
    have e:=(end_range u i archive family m N q B hj).2.trans B.arena
    change _≤14*S at e
    change _≤15*S+V+64+48+6;omega
  have pointer:=compiled_base A cap m src B.childCount (by omega : 1<2^W)
    (by change base u 13+8*(T).id<2^W;rw [B.index];have c:=B.cache;change _≤15*S at c;omega)
    (by rw [Fin.val_cast_of_lt counter];change 15*S+V+64+48+6≠15*S+V+64+22;omega) ptrJobs
  have cache6 : apart (bankBase A cap T .result) 6 a := by
    rw [key];exact safe.cache_range le_rfl (by omega)
  have cache4 : apart (X).compiled.outputBase 4 a := by
    rw [pointer,key];exact safe.cache_range le_rfl (by omega)
  have joined:=output_at X (Tape.tape N wire id q) a
    (join_late_writes u i archive family m N wire id q B safe) cache4
  have off : ¬(bankBase A cap T .result≤a ∧ a<bankBase A cap T .result+
      bankSize T (numeric ((X).compiled.output (Tape.tape N wire id q))) .result) := by
    change ¬(_≤a ∧ a<_+6);rcases cache6 with h|h <;> omega
  simpa only [adjust,fillSegment,ite_eq_right off] using joined.trans mountedAt


/-- The post-join S13 update evaluates its six fields in the completed output memory.
All operands of the numerical result still have their original values there. -/
theorem result_stable (ops : List (Job W)) (layout : ResultSpace A cap m ops)
    (src : SourceCells A cap T (numeric m) W) (children : count≤cap) (wide : 1<2^W) :
    result T (numeric ((X).compiled.output ops))=result T (numeric m) := by
  let out:=(X).compiled.output ops
  let old:=numeric m
  let new:=numeric out
  have target:=compiled_base A cap m src children wide (by have h:=layout.cacheRoom;omega)
    layout.pointerCounter layout.pointerJobs
  have frame := ((((((phase_frames A cap m children (src.node 4).2).2).2).2).2).2).2
  have read (addr : ℕ) (whereAt : SourceAt A T old addr) (outside : External A cap addr) : new addr=old addr := by
    apply congrArg Fin.val
    have small:=outside_cache A cap m ops layout whereAt
    have preserved:=output_at X ops addr (layout.late _ whereAt) (by
      rw [target]
      change addr<(T).resultBase+8*(T).id ∨ (T).resultBase+8*(T).id+4≤addr
      rcases small with left|right
      · exact Or.inl left
      · exact Or.inr (by omega))
    exact preserved.trans (frame _ outside)
  have node (j : Fin 8) := read _ (.node j) (src.node j).2
  have degree : childCount T new=childCount T old := node 4
  have listAddr : new (HistoryStageRoot.node T+3)=old (HistoryStageRoot.node T+3) := node 3
  have row (k) (hk : k<count) : childPtr T new k=childPtr T old k := by
    simp only [childPtr,listAddr,read _ (.child k hk) (src.child k hk).2]
  have resultAt (addr : ℕ) (h : ∀ j : Fin 6,new (addr+j.val)=old (addr+j.val)) :
      atResult new addr=atResult old addr := by
    unfold atResult
    congr 1 <;> first | exact h 0 | exact h 1 | exact h 2 | exact h 3 | exact h 4 | exact h 5
  have kr:=resultAt (T).kernel fun j=>read _ (.kernel j) (src.kernel j).2
  have child (k) (hk : k<count) : atResult new (childPtr T new k)=atResult old (childPtr T old k) := by
    rw [row k hk];exact resultAt _ fun j=>read _ (.old k hk j) (src.old k hk j).2
  have sums (f : Result→ℕ) :
      HistoryStageRoot.prefix T new (childCount T old) f=HistoryStageRoot.prefix T old (childCount T old) f := by
    unfold HistoryStageRoot.prefix
    exact Finset.sum_congr rfl fun k hk=>congrArg f (child k (Finset.mem_range.mp hk))
  let hdr:=old (HistoryStageRoot.node T+6)
  have hh : new (HistoryStageRoot.node T+6)=hdr := node 6
  have hlen : new hdr=old hdr := by simpa [hdr] using read _ (.incident 0) (src.incident 0).2
  have first : new (hdr+1)=old (hdr+1) := read _ (.incident 1) (src.incident 1).2
  have half : halfWidth T new=halfWidth T old := by
    change (let v:=new (HistoryStageRoot.node T+6);let len:=new v;let tail:=new (v+1)+4*(len-1)
            if len=0 then 0 else new (tail+3)+new (tail+2))=_
    dsimp only
    rw [hh,hlen,first]
    change (if old hdr=0 then 0 else _)=if old hdr=0 then 0 else _
    by_cases nz : old hdr=0
    · simp only [ite_eq_left nz]
    · simp only [ite_eq_right nz]
      have existsLast : 0<old hdr:=by omega
      have last (j : ℕ) (lo : 2≤j) (hi : j≤3) :=
        read _ (.last existsLast j lo hi) (src.last existsLast j lo hi).2
      rw [show new (old (hdr+1)+4*(old hdr-1)+3)=old (old (hdr+1)+4*(old hdr-1)+3) from last 3 (by decide) le_rfl,
        show new (old (hdr+1)+4*(old hdr-1)+2)=old (old (hdr+1)+4*(old hdr-1)+2) from last 2 le_rfl (by decide)]
  have outerEq : outer T new=outer T old := node 7
  change result T new=result T old
  simp only [HistoryStageRoot.result,degree,kr,outPins,outerEq,half,HistoryStageRoot.hidden,sums]

/-- Every last S13 column is read from the final writer, including its two physical
pointers and its exact counts. This equality uses unsigned integer extraction. -/
theorem result_header (ops : List (Job W)) (layout : ResultSpace A cap m ops)
    (src : SourceCells A cap T (numeric m) W) (children : count≤cap) (wide : 1<2^W)
    (index : (T).id=i) (v : NodeValue F) (shape : result T (numeric m)=
      ![v.stream,v.pins,v.net.cells,v.net.internal,v.ext,v.external])
    (word : ∀ j : Fin 6,result T (numeric m) j<2^W) :
    atResult (numeric (adjust A cap T .result ((X).compiled.output ops))) (base u 13+8*i)=v.info := by
  let out:=(X).compiled.output ops
  have target : bankBase A cap T .result=base u 13+8*i := by
    change base u 13+8*(T).id=base u 13+8*i;rw [index]
  have original:=result_stable u archive family m ops layout src children wide
  have rows (j : Fin 6) :
      numeric (adjust A cap T .result out) (base u 13+8*i+j.val)=result T (numeric m) j := by
    have published:=HistoryStageSetup.adjust_at A cap T out .result 0 (by change 0<1; decide) j
    change adjust A cap T .result out (bankBase A cap T .result+(6*0+j.val))=
      (result T (numeric out) j:Word W) at published
    simp only [target,Nat.mul_zero,Nat.zero_add] at published
    rw [show result T (numeric out)=result T (numeric m) from original] at published
    exact (congrArg Fin.val published).trans (Fin.val_cast_of_lt (word j))
  have field (j : Fin 6) := (rows j).trans (congrFun shape j)
  change atResult (numeric (adjust A cap T .result out)) (base u 13+8*i)=v.info
  unfold atResult NodeValue.info
  congr 1 <;> first | exact field 0 | exact field 1 | exact field 2 | exact field 3 | exact field 4 | exact field 5

/-- Unlike the general outside-node frame, a copied endpoint is inside this writer's
node. It survives because the gate rows use the preceding sector, while all generated
map, command, and argument writes use scratch. -/
theorem endpoint_after (B : JoinRanges u i archive family m N q)
    (layout : ResultSpace A cap m (Tape.tape N wire id q))
    (src : SourceCells A cap T (numeric m) W) (large : 162≤V)
    (sliced : ∀ k,(q k).dest+4*(N k).cells≤(T).stream+V) (j : ℕ) (live : j<V) :
    adjust A cap T .result ((X).compiled.output (Tape.tape N wire id q)) ((T).ext+j)=(X).extReady ((T).ext+j) := by
  let z := (T).ext+j
  let ops : List (Job W) := Tape.tape N wire id q
  let S := Diagonal.TickWorkspace.stride u
  have sector (bank : ℕ) :
      HistoryScratch.sector family.motifs family.parties ⟨0,0,5,bank⟩=160+bank := by
    simp [HistoryScratch.sector]
  have shape : (T).ext=start+161*V := by
    change base u 12+((T).id*V+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,1⟩)*V+0=_
    rw [sector,B.index]
    ring
  have stream : (T).stream=start+160*V := by
    change base u 12+((T).id*V+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,0⟩)*V+0=_
    rw [sector,B.index]
    ring
  have sec : start+162*V ≤ stop := by
    have h:=Nat.mul_le_mul_right V large;nlinarith only [h]
  have below : z<base u 13 := by have h:=B.arena;dsimp only [z];rw [shape];omega
  have above : (T).stream+V≤z := by dsimp only [z];rw [shape,stream];omega
  have small : V+400+32*(cap+1) ≤ S := B.scratch
  have bound : 20*S<2^W := B.words
  have low : z<14*S := below
  have seedRoom : (A).party.seed+7<2^W := by change 15*S+V+7<2^W;omega
  have cacheAt : bankBase A cap T .result=base u 13+8*i := by change base u 13+8*(T).id=_;rw [B.index]
  have ptr := compiled_base A cap m src B.childCount (by omega : 1<2^W) (by have h:=layout.cacheRoom;omega)
    layout.pointerCounter layout.pointerJobs
  have far (lo len : ℕ) (v : ℕ→Word W) (input : Memory W) (sep : z<lo) :
      fillSegment lo len v input z=input z := by
    simp [fillSegment,show ¬(lo≤z ∧ z<lo+len) by omega]
  have free (job : Job W) (member : job∈ops) : z<job.start ∨ job.finish≤z := by
    change job ∈ (List.finRange n).flatMap (fun k => Tape.jobs (W:=W) N wire id (q k) k) at member
    obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp member
    simp only [Tape.jobs,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl
    · left
      change z < (q k).pins
      have h : 19*S+2 ≤ (q k).pins := (B.pins k).1
      omega
    · right;exact (sliced k).trans above
  have counter : z≠(X).compiled.control.val := by
    change z≠(((A).party.seed+7:ℕ):Word W).val
    rw [Fin.val_cast_of_lt seedRoom]
    change z≠15*S+V+7;omega
  have cacheSep : z<bankBase A cap T .result := by rw [cacheAt];omega
  have outputSep : z<(X).compiled.outputBase := by rw [ptr];exact cacheSep
  have argsSep : z<(X).compiled.hub.arguments := by change z<17*S;omega
  have commandsSep : z<(X).compiled.layout.commands := by change z<16*S;omega
  have seedSep : z<(X).compiled.layout.seed := by change z<15*S+V;omega
  change adjust A cap T .result ((X).compiled.output ops) z=(X).extReady z
  unfold adjust Build.output
  rw [far _ _ _ _ cacheSep,far _ _ _ _ outputSep]
  unfold Build.reached
  rw [after_away _ _ _ _ counter free]
  unfold Build.entered Build.commands Build.seeded
  rw [far _ _ _ _ argsSep,far _ _ _ _ commandsSep,far _ _ _ _ seedSep]
  rfl

/-- Actual final S13 metadata, compiled rows, and every S12 inherited external word
form the next cached node. A source address is specified by its real child ordinal and
its coordinate inside that child's endpoint array. -/
theorem cached_at (B : JoinRanges u i archive family m N q)
    (layout : ResultSpace A cap m (Tape.tape N wire id q))
    (src : SourceCells A cap T (numeric m) W) (large : 162≤V) (head : (X).Header)
    (sliced : ∀ k,(q k).dest+4*(N k).cells≤(T).stream+V)
    (val : NodeValue F) (shape : result T (numeric m)=
      ![val.stream,val.pins,val.net.cells,val.net.internal,val.ext,val.external])
    (word : ∀ j : Fin 6,result T (numeric m) j<2^W)
    (span : val.ext=(T).ext) (fitsExt : val.external≤V)
    (ancestry : ∀ j : Fin val.external,∃ k : Fin count,∃ z : Fin (Endpoints.width T (numeric m) k.val),
      val.ext+j.val=Endpoints.toAddr T (numeric m) k.val+z.val ∧
      m (Endpoints.srcAddr T (numeric m) k.val+z.val)=(val.endpoint j:Word W) ∧
      External A cap (Endpoints.srcAddr T (numeric m) k.val+z.val))
    (rows : HistoryCompiledRows.Records id val.net val.stream
      (adjust A cap T .result ((X).compiled.output (Tape.tape N wire id q)))) :
    val.Cached id u i (adjust A cap T .result ((X).compiled.output (Tape.tape N wire id q))) := by
  have wide : 1<2^W := by
    have wordRoom:=B.words;change 20*(Diagonal.TickWorkspace.stride u)<_ at wordRoom
    have pos : 0<Diagonal.TickWorkspace.stride u := by unfold Diagonal.TickWorkspace.stride;positivity
    omega
  refine ⟨result_header u i archive family m _ layout src B.childCount wide B.index val shape word,rows,?_⟩
  intro j
  obtain ⟨k,z,offset,code,safe⟩:=ancestry j
  have saved:=head.copies.copied k z
  have hold:=((((((phase_frames A cap m B.childCount (src.node 4).2).2).2).2).2).2).2 _ safe
  rw [span] at offset ⊢
  rw [endpoint_after u i archive family m N wire id q B layout src large sliced j.val (j.isLt.trans_le fitsExt),offset]
  exact saved.trans (hold.trans code)

/-- Use the exact native kernel and its charged memory as the input of the root join.
The frame conclusion applies to the whole selected body after its cursor increment. -/
theorem selected_stage_frame (B : JoinRanges u i archive family m N q)
    (src : SourceCells A cap T (numeric m) W) (entry : Memory W) (kernelTime : ℕ)
    (kernelExec : (HistoryMotifJoin.kernelProcedure A W cap).Exec entry m kernelTime)
    (kernelFrame : ∀ a,OutsideNode u i a→m a=entry a)
    (mapping : Fin n→Tape.MapRow) (head : (X).Header)
    (source : Build.Source (X).compiled (Tape.tape N wire id q))
    (resident : Build.Resident (X).compiled N wire id q mapping (T).stream)
    (late : BankInput A cap T .result 12 ((X).compiled.output (Tape.tape N wire id q)))
    (rows : (T).stream+4*(BitNetwork.Ordered.glue N wire).cells ≤ stop) :
    let ops : List (Job W) := Tape.tape N wire id q
    let written:=(X).compiled.output ops
    let out:=adjust A cap T .result written
    (HistoryStageBody.procedure A cap W).Exec entry out
        (kernelTime+((X).prepareCost+(X).compiled.ticks ops+writeCost A cap T .result written)) ∧
      HistoryCompiledRows.Records id (BitNetwork.Ordered.glue N wire) (T).stream out ∧
      ∀ a,OutsideNode u i a→ out a=entry a := by
  intro ops written out
  have keep : (T).stream+4*(BitNetwork.Ordered.glue N wire).cells≤bankBase A cap T .result := by
    change _≤base u 13+8*(T).id
    exact (rows.trans B.arena).trans (Nat.le_add_right _ _)
  obtain ⟨join,records⟩:=(X).join_run N wire id q mapping (T).stream head source resident late (Or.inr keep)
  exact ⟨kernelExec.then join,records,fun a ha=>
    (join_output_frame u i archive family m N wire id q B src a ha).trans (kernelFrame a ha)⟩

/-- Earlier stored trees use words below this node's S12 allocation or before its
S13 cache row. Both alternatives exclude the forward cursor and all scratch. -/
theorem NodeValue.earlier_outside {j a : ℕ} (v : NodeValue F) (earlier : j< i)
    (arena : stop≤base u 13) (cache : base u 13+8*i+8≤base u 14)
    (rows : v.stream+4*v.net.cells≤base u 12+(j+1)*V^2)
    (ends : v.ext+v.external≤base u 12+(j+1)*V^2)
    (used : v.uses u j a) : OutsideNode u i a ∧ a<base u 14 := by
  have seq : start ≤ stop := Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  rcases v.uses_before earlier rows ends used with header|low
  · exact ⟨⟨Or.inr (arena.trans header.1),Or.inl header.2,Or.inl (by omega)⟩,by omega⟩
  · exact ⟨⟨Or.inl low,Or.inl (by omega),Or.inl (by omega)⟩,by omega⟩

namespace Ledger
open HistoryNodeDirectory HistoryNodeDirectory.Selected

/-- When the physical kernel has finished but the current S13 row is still being
assembled, the original selected child rows are already available in that exact memory. -/
theorem producer_frame {total : ℕ} {before mid : Memory W} {j : Fin total}
    (v : NodeValue F) (earlier : j.val< i) (arena : stop≤base u 13) (cache : base u 13+8*i+8≤base u 14)
    (word : base u 18<2^W)
    (rows : v.stream+4*v.net.cells≤base u 12+(j.val+1)*V^2)
    (ends : v.ext+v.external≤base u 12+(j.val+1)*V^2)
    (kernel : ∀ a,OutsideNode u i a→mid a=bump (ownerData W u) before a)
    (a : ℕ) (use : v.uses u j.val a) : mid a=before a := by
  have beforeNode:=v.earlier_outside u i earlier arena cache rows ends use
  have apart : a≠((ownerData W u) 0).val := by
    have main : ((ownerData W u) 0).val=base u 18:=Fin.val_cast_of_lt word
    rw [main]
    have ordered : base u 14≤base u 18 := by unfold base;omega
    have low:=beforeNode.2
    omega
  rw [kernel a beforeNode.1]
  simp only [bump,writeMemory,ite_eq_right apart]

/-- The physical owner directory uses S45 ancestors, S11 root assignments and the
two selected group/slot words in S1. All five addresses are outside every node writer. -/
theorem owner_words {total : ℕ} (D : Directory W total) (room : base u 46 < 2^W)
    (extent : 4 ≤ Diagonal.TickWorkspace.stride u) (length : total ≤ Diagonal.TickWorkspace.stride u)
    (roots : ∀ j,2*(D.root j).val+2 ≤ Diagonal.TickWorkspace.stride u/4)
    (arena : stop ≤ base u 13) (cache : base u 13+8*i+8 ≤ base u 14) :
    ∀ j k,let x:=(addresses (ownerData W u) D j k).val
       OutsideNode u i x ∧ x≠base u 18 := by
  let S:=Diagonal.TickWorkspace.stride u
  have bound : 47*S < 2^W := room
  have low (x : ℕ) (small : x < base u 12) : OutsideNode u i x ∧ x≠base u 18 := by
    have b12 : base u 12 ≤ base u 13 := by change 13*S ≤ 14*S;omega
    have b13 : base u 13 ≤ base u 14 := by change 14*S ≤ 15*S;omega
    have b14 : base u 14 ≤ base u 18 := by change 15*S ≤ 19*S;omega
    exact ⟨⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩,by omega⟩
  have high (x : ℕ) (big : base u 45 ≤ x) : OutsideNode u i x ∧ x≠base u 18 := by
    have t1 : base u 14 ≤ base u 45 := by change 15*S ≤ 46*S;omega
    have t2 : base u 19 ≤ base u 45 := by change 20*S ≤ 46*S;omega
    have t3 : base u 18 < base u 45 := by change 19*S < 46*S;change 4 ≤ S at extent;omega
    have t4 : base u 13 ≤ base u 45 := by change 14*S ≤ 46*S;omega
    exact ⟨⟨Or.inr (by omega),Or.inr (by omega),Or.inr (Or.inl (by omega))⟩,by omega⟩
  let ok (x : ℕ) := OutsideNode u i x ∧ x≠base u 18
  intro j k
  change ok (addresses (ownerData W u) D j k).val
  let owner:=TickPhysicalABI.directory u 1+((D.root j).val+(D.root j).val)
  have os : owner+2 ≤ base u 12 := by
    have r:=roots j
    change 12*S+1*(S/4)+((D.root j).val+(D.root j).val)+2 ≤ 13*S
    change 2*(D.root j).val+2 ≤ S/4 at r
    omega
  have small : base u 12 < 2^W := by change 13*S < _;omega
  have digits : ((ownerData W u) 2+(D.root j+D.root j):Word W)=(owner:Word W) := by
    change ((TickPhysicalABI.directory u 1:ℕ):Word W)+(_+_)=(owner:Word W)
    simp only [owner,Nat.cast_add,Fin.cast_val_eq_self]
  have size : base u 45+j.val < 2^W := by
    have hj:=j.isLt
    change total ≤ S at length
    change 46*S+j.val < 2^W;omega
  have seed : base u 1+3 < base u 12 := by
    change 2*S+3 < 13*S;change 4 ≤ S at extent;omega
  fin_cases k
  · change ok ((((base u 45:ℕ):Word W)+(j.val:Word W)).val)
    rw [←Nat.cast_add,Fin.val_cast_of_lt size]
    exact high _ (Nat.le_add_right _ _)
  · change ok (((ownerData W u) 2+(D.root j+D.root j)).val)
    rw [digits,Fin.val_cast_of_lt (by omega : owner < 2^W)]
    exact low _ (by omega)
  · change ok ((((ownerData W u) 2+(D.root j+D.root j))+1).val)
    rw [digits,←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt (by omega : owner+1 < 2^W)]
    exact low _ (by omega)
  · change ok (((base u 1:ℕ):Word W).val)
    rw [Fin.val_cast_of_lt (by omega : base u 1 < 2^W)]
    exact low _ (by omega)
  · change ok ((((base u 1:ℕ):Word W)+3).val)
    rw [←Nat.cast_ofNat (R:=Word W) (n:=3),←Nat.cast_add,Fin.val_cast_of_lt (by omega : base u 1+3 < 2^W)]
    exact low _ seed

/-- A forward visit advances precisely once. The numerical frame of its emitted
body carries the ownership directory, frozen data and every previously cached record. -/
theorem emitted {total : ℕ} {D : Directory W total} {v : Fin total→NodeValue F}
    {keep : ℕ→Prop} {initial before after : Memory W}
    (L : Ledger u D id v keep initial i before) (hi : i<total) (word : total<2^W)
    (active : base u 19<2^W) (arena : stop≤base u 13) (cache : base u 13+8*i+8≤base u 14)
    (owners : ∀ j k,let x:=(addresses (ownerData W u) D j k).val
      OutsideNode u i x ∧ x≠base u 18)
    (persistent : ∀ x,keep x→OutsideNode u i x ∧ x≠base u 18)
    (limits : ∀ j : Fin total,j.val< i→picked D j.val=true→
      (v j).stream+4*(v j).net.cells≤base u 12+(j.val+1)*V^2 ∧
      (v j).ext+(v j).external≤base u 12+(j.val+1)*V^2)
    (frame : ∀ x,OutsideNode u i x→after x=bump (ownerData W u) before x)
    (written : (v ⟨i,hi⟩).Cached id u i after) : Ledger u D id v keep initial (i+1) after := by
  let S:=Diagonal.TickWorkspace.stride u
  have spos : 0<S := by dsimp [S,Diagonal.TickWorkspace.stride];positivity
  have bound : 20*S<2^W := active
  have cr : ((ownerData W u) 0).val=base u 18 := Fin.val_cast_of_lt (by change 19*S<2^W;omega)
  have cr' : ((ownerData W u) 0+1).val=base u 18+1 := by
    change (((base u 18:ℕ):Word W)+1).val=_
    rw [←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt (by change 19*S+1<2^W;omega)]
  have unchanged (x : ℕ) (good : OutsideNode u i x) (neq : x≠base u 18) : after x=before x := by
    rw [frame x good]
    simp [bump,writeMemory,cr,neq]
  have control (off : ℕ) (small : off≤1) : OutsideNode u i (base u 18+off) := by
    have geo : base u 14≤base u 18 := by change 15*S≤19*S;omega
    have edge : base u 13≤base u 14 := by change 14*S≤15*S;omega
    refine ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (Or.inr ?_)⟩
    omega
  apply L.next
  · have inc : ((cur (ownerData W u) before+1:Word W)).val=i+1 := by
      have cursor : cur (ownerData W u) before=(i : Word W) := by
        apply Fin.ext
        rw [Fin.val_cast_of_lt (hi.trans word)]
        exact L.cursor
      rw [cursor,←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt (show i+1<2^W by omega)]
    change (after ((ownerData W u) 0).val).val=i+1
    rw [frame _ (by simpa [cr] using control 0 (by decide))]
    simpa [cur,bump,writeMemory] using inc
  · have copy:=unchanged (base u 18+1) (control 1 (by decide)) (by omega)
    simpa only [cr',copy] using L.stop
  · intro j k
    rw [unchanged _ (owners j k).1 (owners j k).2]
    exact L.directory j k
  · exact fun x hx=>unchanged x (persistent x hx).1 (persistent x hx).2
  · intro j earlier pickedAt x hx
    have past := (v j).earlier_outside u i earlier arena cache (limits j earlier pickedAt).1
      (limits j earlier pickedAt).2 hx
    apply unchanged x past.1
    have := past.2
    change x<15*S at this
    change x≠19*S
    omega
  · intro j eq chosen
    obtain rfl : j=⟨i,hi⟩:=Fin.ext eq
    exact written

end Ledger


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
