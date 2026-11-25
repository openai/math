import OAI.ThreeFlat.RAM.HistoryStageSetup

namespace OAI
/-! # Emitting the current S13 result after the bounded join has completed -/

namespace ThreeFlat.RAM.HistoryStageResult

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalProcedure HistoryPartyBatchExec
open HistoryStageBody HistoryStageRoot HistoryStageSetup HistoryBoundedBody HistoryReadyTape
open scoped Fin.CommRing BigOperators
noncomputable section
variable {W : ℕ}

def apart (lo n x : ℕ) := x<lo ∨ lo+n≤x

/-- Physical sources of the final scan. Its header uses only controls 0 through 11,
24 and 25, and the endpoint loop advances control 22. -/
inductive SourceAt (A : HistoryGatherBody.Layout) (S : Input) (raw : ℕ→ℕ) : ℕ→Prop
  | control (j : ℕ) (live : j≤11 ∨ j=24 ∨ j=25) : SourceAt A S raw (args A+j)
  | cursor : SourceAt A S raw A.nodePorts.cursor
  | node (j : Fin 8) : SourceAt A S raw (HistoryStageRoot.node S+j.val)
  | child (i : ℕ) (h : i<childCount S raw) : SourceAt A S raw (raw (HistoryStageRoot.node S+3)+i)
  | kernel (j : Fin 6) : SourceAt A S raw (S.kernel+j.val)
  | old (i : ℕ) (h : i<childCount S raw) (j : Fin 6) : SourceAt A S raw (childPtr S raw i+j.val)
  | incident (j : Fin 2) : SourceAt A S raw (raw (HistoryStageRoot.node S+6)+j.val)
  | last (h : 0<raw (raw (HistoryStageRoot.node S+6))) (j : ℕ) (lo : 2≤j) (hi : j≤3) :
    SourceAt A S raw (HistoryStageBounds.lastIncident S raw+j)

/-- Actual write spans and the two advancing loop counters prior to S13 publication. -/
structure LateWrites (X : StageRun W) (ops : List (Job W)) (x : ℕ) : Prop where
  extCounter : x≠(loc X.layout 22:Word W).val
  endpoints : ∀ j∈X.endpointJobs,x<j.start ∨ j.finish≤x
  seed : apart X.compiled.layout.seed 9 x
  commands : apart X.compiled.layout.commands (14*X.compiled.hub.argc) x
  arguments : apart X.compiled.hub.arguments (7*X.compiled.hub.argc) x
  tapeCounter : x≠X.compiled.control.val
  tape : ∀ j∈ops,x<j.start ∨ j.finish≤x

/-- All endpoint jobs lie in one contiguous output interval. -/
theorem endpoints_outside (X : StageRun W) (x : ℕ)
    (small : x<X.inputs.ext ∨ Endpoints.toAddr X.inputs X.childRaw (childCount X.inputs X.childRaw)≤x) :
    ∀ job∈X.endpointJobs,x<job.start ∨ job.finish≤x := by
  intro job hj
  change job∈(List.range (childCount X.inputs X.childRaw)).map _ at hj
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hj
  have live:=List.mem_range.mp hi
  rcases small with h|h
  · left
    exact h.trans_le (Nat.le_add_right ..)
  · right
    change Endpoints.toAddr X.inputs X.childRaw i+Endpoints.width X.inputs X.childRaw i≤x
    rw [←Endpoints.dest_next]
    exact (Endpoints.dest_monotone i.succ _ live).trans h

private theorem fill_off (m : Memory W) (lo n x : ℕ) (word : ℕ→Word W) (h : apart lo n x) :
    fillSegment lo n word m x=m x := by
  have dis : ¬(lo≤x ∧ x<lo+n) := by rcases h with h|h <;> omega
  simp only [fillSegment,ite_eq_right dis]

theorem output_at (X : StageRun W) (ops : List (Job W)) (x : ℕ)
    (h : LateWrites X ops x) (cache : apart X.compiled.outputBase 4 x) :
    X.compiled.output ops x=X.mounted x := by
  unfold Build.output
  rw [fill_off _ _ _ _ _ cache]
  unfold Build.reached
  rw [after_away _ _ _ _ h.tapeCounter h.tape]
  unfold Build.entered
  rw [fill_off _ _ _ _ _ h.arguments]
  unfold Build.commands
  rw [fill_off _ _ _ _ _ h.commands]
  unfold Build.seeded
  rw [fill_off _ _ _ _ _ h.seed]
  exact after_away _ _ _ _ h.extCounter h.endpoints

variable (A : HistoryGatherBody.Layout) (cap : ℕ) (m : Memory W)
local notation "X" => HistoryStageSetup.run A cap m
local notation "S" => numInput A cap (numeric m)
local notation "count" => childCount S (numeric m)
local notation "cacheAt" => (Input.resultBase S+8*Input.id S : ℕ)
local notation "hubPointer" => (HistoryStageBody.hub A+6)

/-- Every enumerated child precedes this cache ID. Resident scratch and S44 records
lie outside the six current result words and the actual command output intervals. -/
structure ResultSpace (ops : List (Job W)) : Prop where
  cacheRoom : cacheAt+6<2^W
  earlier : ∀ i,i<count→numeric m (numeric m (HistoryStageRoot.node S+3)+i)<(S).id
  args : ∀ j, j≤11 ∨ j=24 ∨ j=25 → apart cacheAt 6 (HistoryStageBody.args A+j)
  cursor : apart cacheAt 6 A.nodePorts.cursor
  node : ∀ j : Fin 8, apart cacheAt 6 (HistoryStageRoot.node S+j.val)
  child : ∀ i,i<count→apart cacheAt 6 (numeric m (HistoryStageRoot.node S+3)+i)
  kernel : ∀ j : Fin 6, apart cacheAt 6 ((S).kernel+j.val)
  incident : ∀ j : Fin 2, apart cacheAt 6 (numeric m (HistoryStageRoot.node S+6)+j.val)
  last : 0<numeric m (numeric m (HistoryStageRoot.node S+6))→∀ j,2≤j→j≤3→
    apart cacheAt 6 (HistoryStageBounds.lastIncident S (numeric m)+j)
  pointerCounter : hubPointer≠(loc A 22:Word W).val
  pointerJobs : ∀ job∈(X).endpointJobs,hubPointer<job.start ∨ job.finish≤hubPointer
  late : ∀ x, SourceAt A S (numeric m) x → LateWrites X ops x

theorem outside_cache (ops : List (Job W)) (s : ResultSpace A cap m ops)
    {x : ℕ} (h : SourceAt A S (numeric m) x) : apart cacheAt 6 x := by
  cases h with
  | control j live => exact s.args j live
  | cursor => exact s.cursor
  | node j => exact s.node j
  | child i hi => exact s.child i hi
  | kernel j => exact s.kernel j
  | old i hi j =>
    have priorWord (base child current slot : ℕ) (earlier : child<current) (small : slot<6) :
        base+8*child+slot<base+8*current := by omega
    exact Or.inl (priorWord (S).resultBase _ (S).id j.val (s.earlier i hi) j.isLt)
  | incident j => exact s.incident j
  | last h j lo hi=>exact s.last h j lo hi

include cap in
private theorem cache_eval (mem : Memory W) (p : Word W) (room : A.nodePorts.cursor<2^W) (wide : 1<2^W)
    (held : mem A.nodePorts.cursor=m A.nodePorts.cursor) :
    (HistoryStageBody.cache A).eval Fin.elim0 mem (fun _=>p)=
      ((A.nodePorts.cache+8*(numInput A cap (numeric m)).id:ℕ):Word W) := by
  have idRead : (nodeId A).eval Fin.elim0 mem (fun _=>p)=((numInput A cap (numeric m)).id:Word W) :=
    (HistoryStageSetup.id_word A cap mem p room wide).trans
      (congrArg (fun w : Word W => ((w.val-1:ℕ):Word W)) held)
  simp only [HistoryStageBody.cache,HistoryStageBody.a,HistoryStageBody.times,HistoryStageBody.l,
    Term.eval_binary,Term.eval_literal,idRead,
    BinaryOp.eval,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]

private theorem headerImage_head (term : Term W 0 1) (start : ℕ) (mem : Memory W) :
    HistoryMotifJoin.headerImage term start 1 mem start=term.eval Fin.elim0 mem (fun _=>(start:Word W)) := by
  simp only [HistoryMotifJoin.headerImage,fillSegment,ite_eq_left (show start ≤ start ∧ start<start+1 by omega)]

set_option maxHeartbeats 800000 in
theorem compiled_base (src : SourceCells A cap S (numeric m) W) (children : count≤cap) (wide : 1<2^W)
    (room : cacheAt<2^W) (different : hubPointer≠(loc A 22:Word W).val)
    (outside : ∀ j∈(X).endpointJobs,hubPointer<j.start ∨ j.finish≤hubPointer) :
    (X).compiled.outputBase=bankBase A cap S .result := by
  obtain ⟨_,_,_,_,_,before,_⟩:=phase_frames A cap m children (src.node 4).2
  have held : (X).withCommands A.nodePorts.cursor=m A.nodePorts.cursor:=before _ src.cursor.2
  have first : (X).mounted hubPointer=(cacheAt:Word W) := by
    have layoutAt : (X).layout=A := rfl
    rw [StageRun.mounted,layoutAt,headerImage_head]
    exact cache_eval (A:=A) (cap:=cap) (m:=m) (X).withCommands ((HistoryStageBody.hub A+6 : ℕ) : Word W) src.cursor.1 wide held
  have keep : (X).extReady hubPointer=(X).mounted hubPointer :=
    after_away _ _ _ _ different outside
  change ((X).extReady hubPointer).val=_
  rw [keep,first,Fin.val_cast_of_lt room]
  rfl

set_option maxRecDepth 18000 in
/-- The final bank is computed in the real output RAM of the physical bounded join.
Its six words overwrite the current cache row after the old-child lookups. -/
theorem make_result_bank (ops : List (Job W)) (layout : ResultSpace A cap m ops)
    (src : SourceCells A cap S (numeric m) W) (inputRoom : ∀ f,(S).words f<2^W)
    (children : count≤cap) (space : limit A cap<2^W) :
    BankInput A cap S .result 12 ((X).compiled.output ops) := by
  let out:=(X).compiled.output ops
  have hr : args A+26<2^W := by unfold limit extCommands extArgs mapArgs links loc at space;unfold args loc;omega
  have big : 11<2^W:=by omega
  have cp : cap<2^W:=by unfold limit extCommands extArgs mapArgs links loc at space;omega
  have base : (X).compiled.outputBase=cacheAt := compiled_base A cap m src children (by omega)
    (by have:=layout.cacheRoom;omega) layout.pointerCounter layout.pointerJobs
  have held (x : ℕ) (use : SourceAt A S (numeric m) x) : out x=(X).mounted x := by
    apply output_at X ops x (layout.late x use)
    rw [base]
    have outside:=outside_cache A cap m ops layout use
    rcases outside with h|h
    · exact .inl h
    · exact .inr (by omega)
  obtain ⟨_,_,_,_,_,_,ctrl⟩:=phase_controls A cap m src.cursor.1 (src.node 4).1 hr
  obtain ⟨_,_,_,_,_,_,frame⟩:=phase_frames A cap m children (src.node 4).2
  have same (x : ℕ) (use : SourceAt A S (numeric m) x) (ext : External A cap x) :
      numeric out x=numeric m x := congrArg Fin.val ((held x use).trans (frame x ext))
  have ns (j : Fin 8) := same _ (.node j) (src.node j).2
  have childEq : childCount S (numeric out)=count:=ns 4
  have listEq : numeric out (HistoryStageRoot.node S+3)=numeric m (HistoryStageRoot.node S+3):=ns 3
  have incEq : numeric out (HistoryStageRoot.node S+6)=numeric m (HistoryStageRoot.node S+6):=ns 6
  have childAt (i : ℕ) (hi : i<count) : childPtr S (numeric out) i=childPtr S (numeric m) i := by
    simp only [childPtr,listEq,same _ (.child i hi) (src.child i hi).2]
  have ih0 := same _ (.incident 0) (src.incident 0).2
  have ih1 := same _ (.incident 1) (src.incident 1).2
  change numeric out (numeric m (HistoryStageRoot.node S+6)+1)=
    numeric m (numeric m (HistoryStageRoot.node S+6)+1) at ih1
  simp only [Fin.val_zero,Nat.add_zero] at ih0
  have obs (j : ℕ) (h : j≤11 ∨ j=24 ∨ j=25) :
      out (args A+j)=(X).mounted (args A+j):=held _ (.control j h)
  have inputs (f : Fin 11) : numeric out (args A+f.val)=(S).words f :=
    (congrArg Fin.val (obs f.val (.inl (by have:=f.isLt;omega)))).trans (ControlsAt.input A cap ctrl inputRoom f)
  have endHeader := ControlsAt.scan A cap ctrl hr (by
    exact congrArg Fin.val (frame _ (src.node 4).2)) Bank.result
  have word (f : ℕ) (h : f=12 ∨ f=13) :
      HeaderScan.headerWord out (loc A 11:Word W) f=HeaderScan.headerWord (X).mounted (loc A 11:Word W) f := by
    have ptr := ctrl (11:Fin 26)
    change (X).mounted (args A+11)=(loc A 12:Word W) at ptr
    have e11 : loc A 11=args A+11 := by simp [loc,args]
    have e12 : loc A 12=args A+12 := by simp [loc,args]
    unfold HeaderScan.headerWord
    rw [Fin.val_cast_of_lt (by omega : loc A 11<2^W),e11,obs 11 (.inl le_rfl),ptr,←Nat.cast_add,
      Fin.val_cast_of_lt (by omega : loc A 12+f<2^W),e12,Nat.add_assoc]
    apply obs
    rcases h with rfl|rfl <;> decide
  have cursorSame := (held _ .cursor).trans (frame _ src.cursor.2)
  have locOut (p : Word W) : (destination A cap .result).eval Fin.elim0 out (fun _=>p)=(cacheAt:Word W) :=
    cache_eval (A:=A) (cap:=cap) (m:=m) out p src.cursor.1
      (lt_trans (by decide : 1<11) big) cursorSame
  have small : childCount S (numeric out)≤cap := by rw [childEq];exact children
  have within : bankBase A cap S .result+bankSize S (numeric out) .result<2^W:=by
    simpa [bankBase,bankSize,rowCount,Bank.width] using layout.cacheRoom
  have cell (x : ℕ) (use : SourceAt A S (numeric m) x) (bound : x<2^W) :
      HistoryStageBounds.Cell W (HistoryStageBounds.BankOutside A cap S out .result) x := by
    have no:=outside_cache A cap m ops layout use
    simpa [HistoryStageBounds.Cell,HistoryStageBounds.BankOutside,bankBase,bankSize,rowCount,Bank.width,
      apart] using And.intro bound no
  have slots : HistoryStageBounds.BankCells A cap S out .result := by
    constructor
    · exact fun _=>cell _ .cursor src.cursor.1
    · intro j;exact cell _ (.control j.val (.inl (by have:=j.isLt;omega))) (by have:=j.isLt;omega)
    · intro j;exact cell _ (.node j) (src.node j).1
    · intro i hi
      rw [childEq] at hi
      rw [listEq];exact cell _ (.child i hi) (src.child i hi).1
    · intro j;exact cell _ (.kernel j) (src.kernel j).1
    · intro i hi j
      rw [childEq] at hi
      rw [childAt i hi];exact cell _ (.old i hi j) (src.old i hi j).1
    · intro j;rw [incEq];exact cell _ (.incident j) (src.incident j).1
    · intro h j lo hi
      rw [incEq,ih0] at h
      simpa only [HistoryStageBounds.lastIncident,incEq,ih0,ih1] using
        cell _ (.last h j lo hi) (src.last h j lo hi).1
  have checked:=HistoryStageBounds.formula_checks A cap S out .result inputs locOut within small cp big slots
  exact ⟨(word 12 (.inl rfl)).trans endHeader.1,(word 13 (.inr rfl)).trans endHeader.2,
    inputs,locOut,within,small,checked.1,checked.2⟩


end
end ThreeFlat.RAM.HistoryStageResult

end OAI
