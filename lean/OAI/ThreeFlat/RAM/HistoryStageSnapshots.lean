import OAI.ThreeFlat.RAM.HistoryStageResult

namespace OAI
/-! # The real bounded-join hub, link and operand tables -/

namespace ThreeFlat.RAM.HistoryStageSnapshots

open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody HistoryStageRoot HistoryStageSetup HistoryPartyBatchExec
open HistoryReadyTape HistoryBoundedBody
open scoped Fin.CommRing BigOperators
noncomputable section
variable {W : ℕ}

structure Snapshot (A : HistoryGatherBody.Layout) (cap : ℕ) (S : Input) (raw : ℕ→ℕ)
    (mem : Memory W) : Prop where
  hub : ∀ j : Fin 6,mem (HistoryStageBody.hub A+j.val)=((HistoryStageRoot.hub S raw).words j:Word W)
  link : ∀ i : Fin (childCount S raw+1),∀ j : Fin 4,
    mem (links A+(4*i.val+j.val))=((HistoryStageRoot.link S raw i.val).words j:Word W)
  operand : ∀ i : Fin (childCount S raw+1),∀ j : Fin 5,
    mem (mapArgs A cap+(5*i.val+j.val))=(HistoryStageRoot.operands S raw i.val j:Word W)

private structure Values (S : Input) (raw now : ℕ→ℕ) : Prop where
  count : childCount S now=childCount S raw
  outer : HistoryStageRoot.outer S now=HistoryStageRoot.outer S raw
  width : halfWidth S now=halfWidth S raw
  kernel : atResult now S.kernel=atResult raw S.kernel
  child : ∀ i,i<childCount S raw→childPtr S now i=childPtr S raw i
  result : ∀ i,i<childCount S raw→atResult now (childPtr S now i)=atResult raw (childPtr S raw i)

private theorem at_result {m n : ℕ→ℕ} (a : ℕ) (h : ∀ j : Fin 6,m (a+j.val)=n (a+j.val)) :
    atResult m a=atResult n a := by
  have h0 : m a=n a:=by simpa using h 0
  have h1 : m (a+1)=n (a+1) := h 1
  have h2 : m (a+2)=n (a+2) := h 2
  have h3 : m (a+3)=n (a+3) := h 3
  have h4 : m (a+4)=n (a+4) := h 4
  have h5 : m (a+5)=n (a+5) := h 5
  simp only [atResult,h0,h1,h2,h3,h4,h5]

private theorem input_values {A : HistoryGatherBody.Layout} {cap : ℕ} {S : Input} {orig now : Memory W}
    (cells : SourceCells A cap S (numeric orig) W) (keep : Retains A cap orig now) :
    Values S (numeric orig) (numeric now) := by
  let o:=numeric orig
  let n:=numeric now
  have h (x : ℕ) (out : x<2^W ∧ External A cap x) : n x=o x:=congrArg Fin.val (keep x out.2)
  have node (j : Fin 8) := h _ (cells.node j)
  have l : n (HistoryStageRoot.node S+3)=o (HistoryStageRoot.node S+3):=node 3
  have head : n (HistoryStageRoot.node S+6)=o (HistoryStageRoot.node S+6):=node 6
  have c0 : n (o (HistoryStageRoot.node S+6))=o (o (HistoryStageRoot.node S+6)):=by
    simpa using h _ (cells.incident 0)
  have c1 : n (o (HistoryStageRoot.node S+6)+1)=o (o (HistoryStageRoot.node S+6)+1):=h _ (cells.incident 1)
  have c (i : ℕ) (hi : i<childCount S o) : childPtr S n i=childPtr S o i:=by
    simp only [childPtr,l]
    exact congrArg (fun j => S.resultBase+8*j) (h _ (cells.child i hi))
  refine ⟨node 4,node 7,?_,at_result _ (fun j=>h _ (cells.kernel j)),c,?_⟩
  · change halfWidth S n=halfWidth S o
    simp only [halfWidth,head,c0,c1]
    by_cases empty : o (o (HistoryStageRoot.node S+6))=0
    · simp [empty]
    · have hi : 0<o (o (HistoryStageRoot.node S+6)):=by omega
      simp only [ite_eq_right empty]
      exact congrArg₂ (·+·) (h _ (cells.last hi 3 (by decide) le_rfl))
        (h _ (cells.last hi 2 le_rfl (by decide)))
  · intro i hi
    rw [c i hi]
    exact at_result _ (fun j=>h _ (cells.old i hi j))

private theorem Values.sums {S : Input} {o n : ℕ→ℕ} (h : Values S o n)
    (f : Result→ℕ) (t : ℕ) (small : t≤childCount S o) :
    HistoryStageRoot.prefix S n t f=HistoryStageRoot.prefix S o t f := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [h.result k ((Finset.mem_range.mp hk).trans_le small)]

private theorem Values.hub {S : Input} {o n : ℕ→ℕ} (h : Values S o n) :
    HistoryStageRoot.hub S n=HistoryStageRoot.hub S o := by
  simp only [HistoryStageRoot.hub,outPins,HistoryStageRoot.hidden,h.outer,h.width,h.count,
    h.sums oldHalf _ le_rfl]

private theorem Values.link {S : Input} {o n : ℕ→ℕ} (h : Values S o n)
    (i : ℕ) (small : i≤childCount S o) :
    HistoryStageRoot.link S n i=HistoryStageRoot.link S o i := by
  cases i with
  | zero=>simp [HistoryStageRoot.link,HistoryStageRoot.ptr,mapPtr]
  | succ k=>
    have lt : k<childCount S o:=small
    simp only [HistoryStageRoot.link,HistoryStageRoot.ptr,mapPtr,Nat.succ_ne_zero,ite_false,
      Nat.add_sub_cancel,h.child k lt,h.kernel,h.sums Result.pins k lt.le]

private theorem Values.operand {S : Input} {o n : ℕ→ℕ} (h : Values S o n)
    (i : ℕ) (small : i≤childCount S o) : operands S n i=operands S o i := by
  cases i with
  | zero=>
    simp only [operands,HistoryStageRoot.ptr,ite_true,outPins,HistoryStageRoot.hidden,h.outer,h.width,h.count,
      h.sums oldHalf _ le_rfl,h.kernel]
  | succ k=>
    have lt : k<childCount S o:=small
    simp only [operands,HistoryStageRoot.ptr,mapPtr,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,
      outPins,h.width,h.outer,h.result k lt,h.kernel,h.sums Result.pins k lt.le,
      h.sums Result.extCount k lt.le,h.sums oldHalf k lt.le]

variable (A : HistoryGatherBody.Layout) (cap : ℕ) (m : Memory W)
local notation "S" => numInput A cap (numeric m)
local notation "X" => HistoryStageSetup.run A cap m
local notation "n" => childCount S (numeric m)

/-- Exact source rectangles. None of these includes the separate cache-pointer word
between the hub and links. -/
inductive Address (A : HistoryGatherBody.Layout) (cap count : ℕ) : ℕ→Prop
  | hub (j : Fin 6) : Address A cap count (HistoryStageBody.hub A+j.val)
  | link (i : Fin (count+1)) (j : Fin 4) : Address A cap count (links A+(4*i.val+j.val))
  | operand (i : Fin (count+1)) (j : Fin 5) : Address A cap count (mapArgs A cap+(5*i.val+j.val))

private theorem before_fill (mem : Memory W) (start len x : ℕ) (word : ℕ→Word W)
    (off : x<start ∨ start+len≤x) : fillSegment start len word mem x=mem x := by
  have h : ¬(start≤x ∧ x<start+len) := by rcases off with h|h <;> omega
  simp [fillSegment,h]

private theorem after_header (term : DescriptorExpr.Term W 0 1) (start x : ℕ) (mem : Memory W)
    (different : x≠start) : HistoryMotifJoin.headerImage term start 1 mem x=mem x := by
  exact before_fill mem start 1 x _ (by omega)

private theorem before_adjust (layout : HistoryGatherBody.Layout) (capacity : ℕ) (src : Input)
    (bank : Bank) (mem : Memory W) (x : ℕ) (left : x<bankBase layout capacity src bank) :
    adjust layout capacity src bank mem x=mem x :=
  before_fill mem (bankBase layout capacity src bank) _ x _ (.inl left)

set_option maxHeartbeats 1000000 in
private theorem after_prelude (Y : StageRun W) (x : ℕ) (left : x<extArgs Y.layout Y.cap)
    (gap : x≠HistoryStageBody.hub Y.layout+6) : Y.mounted x=Y.withMap x := by
  have cmd : x<extCommands Y.layout Y.cap := left.trans_le (by unfold extCommands; omega)
  calc
    Y.mounted x = Y.withCommands x :=
      after_header (cache Y.layout : DescriptorExpr.Term W 0 1) (HistoryStageBody.hub Y.layout+6) x Y.withCommands gap
    _ = Y.withSources x := before_adjust Y.layout Y.cap Y.inputs .extCommand Y.withSources x cmd
    _ = Y.withMap x := before_adjust Y.layout Y.cap Y.inputs .extArgs Y.withMap x left

/-- Readback of the three bank fills before running the endpoint copy jobs. -/
theorem mounted (cells : SourceCells A cap S (numeric m) W) (owned : n≤cap) :
    Snapshot A cap S (numeric m) (X).mounted := by
  obtain ⟨h0,h1,h2,_,_,_,_⟩:=phase_frames A cap m owned (cells.node 4).2
  have f0:=input_values cells h0
  have f1:=input_values cells h1
  have f2:=input_values cells h2
  have hubOff (j : Fin 6) : HistoryStageBody.hub A+j.val<links A := by
    have:=j.isLt;unfold HistoryStageBody.hub links loc;omega
  have linkLow : links A≤ mapArgs A cap:=by unfold mapArgs;omega
  have mapLow : mapArgs A cap≤extArgs A cap:=by unfold extArgs;omega
  have hubLimit (j : Fin 6) := (hubOff j).trans_le (linkLow.trans mapLow)
  have linkLimit (i : Fin (n+1)) (j : Fin 4) : links A+(4*i.val+j.val)< mapArgs A cap := by
    have hi:=i.isLt;have hj:=j.isLt;unfold mapArgs;omega
  have right : HistoryStageBody.hub A+6<links A:=by unfold HistoryStageBody.hub links loc;omega
  constructor
  · intro j
    rw [after_prelude (X) _ (hubLimit j) (by
      change HistoryStageBody.hub A+j.val ≠ HistoryStageBody.hub A+6
      have index := j.isLt
      omega)]
    change fillSegment (mapArgs A cap) _ _ (X).withLinks _=_
    rw [before_fill _ _ _ _ _ (.inl ((hubOff j).trans_le linkLow))]
    change fillSegment (links A) _ _ (X).withHub _=_
    rw [before_fill _ _ _ _ _ (.inl (hubOff j))]
    change adjust A cap S .hub (X).initialized _=_
    have read:=adjust_at A cap S (X).initialized .hub 0 (by change 0<1; decide) j
    simpa only [bankBase,Bank.width,Nat.mul_zero,Nat.zero_add,Bank.word,f0.hub] using read
  · intro i j
    rw [after_prelude (X) _ ((linkLimit i j).trans_le mapLow) (by
      change links A+(4*i.val+j.val) ≠ HistoryStageBody.hub A+6
      exact (right.trans_le (Nat.le_add_right _ _)).ne')]
    change fillSegment (mapArgs A cap) _ _ (X).withLinks _=_
    rw [before_fill _ _ _ _ _ (.inl (linkLimit i j))]
    have bound : i.val<rowCount (childCount S (numeric (X).withHub)) .link := by
      rw [f1.count];exact i.isLt
    change adjust A cap S .link (X).withHub _=_
    have read:=adjust_at A cap S (X).withHub .link i.val bound j
    simpa only [bankBase,Bank.width,Bank.word,f1.link _ (Nat.lt_succ_iff.mp i.isLt)] using read
  · intro i j
    have last : mapArgs A cap+(5*i.val+j.val)<extArgs A cap := by
      have hi:=i.isLt;have hj:=j.isLt;unfold extArgs;omega
    rw [after_prelude (X) _ last (by
      change mapArgs A cap+(5*i.val+j.val) ≠ HistoryStageBody.hub A+6
      exact (right.trans_le (linkLow.trans (Nat.le_add_right _ _))).ne')]
    have bound : i.val<rowCount (childCount S (numeric (X).withLinks)) .mapArgs := by
      rw [f2.count];exact i.isLt
    change adjust A cap S .mapArgs (X).withLinks _=_
    have read:=adjust_at A cap S (X).withLinks .mapArgs i.val bound j
    simpa only [bankBase,Bank.width,Bank.word,f2.operand _ (Nat.lt_succ_iff.mp i.isLt)] using read

structure BootSpace : Prop where
  endpointCounter : ∀ x, Address A cap n x → x≠(loc A 22:Word W).val
  endpoints : ∀ x, Address A cap n x → ∀ job∈(X).endpointJobs,x<job.start ∨ job.finish≤x
  seed : ∀ x, Address A cap n x → x<(X).compiled.layout.seed ∨ (X).compiled.layout.seed+9≤x
  commands : ∀ x, Address A cap n x → x<(X).compiled.layout.commands ∨
    (X).compiled.layout.commands+14*(X).compiled.hub.argc≤x
  arguments : ∀ x, Address A cap n x → x<(X).compiled.hub.arguments ∨
    (X).compiled.hub.arguments+7*(X).compiled.hub.argc≤x

/-- Four arena bounds discharge every address-enumeration condition in the boot snapshots. -/
theorem BootSpace.of_intervals (owned : n≤cap) (cursor : loc A 22<2^W)
    (endpoints : Endpoints.toAddr S (numeric m) n≤HistoryStageBody.hub A ∨ extArgs A cap≤(S).ext)
    (cmd : (X).compiled.layout.commands+14*(X).compiled.hub.argc≤HistoryStageBody.hub A ∨
      extArgs A cap≤(X).compiled.layout.commands)
    (arg : (X).compiled.hub.arguments+7*(X).compiled.hub.argc≤HistoryStageBody.hub A ∨
      extArgs A cap≤(X).compiled.hub.arguments) : BootSpace A cap m := by
  have region (x : ℕ) (a : Address A cap n x) : HistoryStageBody.hub A≤x ∧ x<extArgs A cap := by
    cases a with
    | hub j => have:=j.isLt;unfold HistoryStageBody.hub extArgs mapArgs links loc;omega
    | link i j => have:=i.isLt;have:=j.isLt;unfold HistoryStageBody.hub extArgs mapArgs links loc;omega
    | operand i j => have:=i.isLt;have:=j.isLt;unfold HistoryStageBody.hub extArgs mapArgs links loc;omega
  constructor
  · intro x h
    rw [Fin.val_cast_of_lt cursor]
    have low:=(region x h).1
    unfold HistoryStageBody.hub loc at *;omega
  · intro x h
    apply HistoryStageResult.endpoints_outside X x
    have within:=region x h
    rcases endpoints with e|e
    · exact .inr (e.trans within.1)
    · exact .inl (within.2.trans_le e)
  · intro x h
    right
    have low:=(region x h).1
    change A.party.seed+9≤x
    unfold HistoryStageBody.hub loc at low
    omega
  · intro x h
    have within:=region x h
    rcases cmd with c|c
    · exact .inr (c.trans within.1)
    · exact .inl (within.2.trans_le c)
  · intro x h
    have within:=region x h
    rcases arg with a|a
    · exact .inr (a.trans within.1)
    · exact .inl (within.2.trans_le a)

theorem Snapshot.transfer {A : HistoryGatherBody.Layout} {cap : ℕ} {src : Input} {raw : ℕ→ℕ}
    {old now : Memory W} (h : Snapshot A cap src raw old)
    (same : ∀ x,Address A cap (childCount src raw) x→now x=old x) : Snapshot A cap src raw now :=
  ⟨fun j=>(same _ (.hub j)).trans (h.hub j),
    fun i j=>(same _ (.link i j)).trans (h.link i j),
    fun i j=>(same _ (.operand i j)).trans (h.operand i j)⟩

theorem snapshots (cells : SourceCells A cap S (numeric m) W) (owned : n≤cap) (physical : BootSpace A cap m) :
    Snapshot A cap S (numeric m) (X).compiled.input ∧ Snapshot A cap S (numeric m) (X).compiled.seeded ∧
    Snapshot A cap S (numeric m) (X).compiled.commands ∧ Snapshot A cap S (numeric m) (X).compiled.entered := by
  have converted : Snapshot A cap S (numeric m) (X).compiled.input := (mounted A cap m cells owned).transfer
    (fun x h=>after_away _ _ _ _ (physical.endpointCounter x h) (physical.endpoints x h))
  have seeded : Snapshot A cap S (numeric m) (X).compiled.seeded := converted.transfer
    (fun x h=>before_fill _ _ _ _ _ (physical.seed x h))
  have commands : Snapshot A cap S (numeric m) (X).compiled.commands := seeded.transfer
    (fun x h=>before_fill _ _ _ _ _ (physical.commands x h))
  exact ⟨converted,seeded,commands,commands.transfer (fun x h=>before_fill _ _ _ _ _ (physical.arguments x h))⟩

/-- The four resident words of the kernel and each actual old result, before and
after generation of command and argument tables. -/
def CachedInfo (src : Input) (raw : ℕ→ℕ) (mem : Memory W) :=
  ∀ i : Fin (childCount src raw+1),
    HistoryBoundedJoin.read (HistoryStageRoot.ptr src raw i.val) (numeric mem)=
      HistoryBoundedJoin.read (HistoryStageRoot.ptr src raw i.val) raw

/-- One source address avoids the actual writes before the join tape starts. -/
structure BootCell (addr : ℕ) : Prop where
  counter : addr≠(loc A 22:Word W).val
  endpoints : addr<(S).ext ∨ Endpoints.toAddr S (numeric m) n≤addr
  seed : addr<(X).compiled.layout.seed ∨ (X).compiled.layout.seed+9≤addr
  commands : addr<(X).compiled.layout.commands ∨ (X).compiled.layout.commands+14*(X).compiled.hub.argc≤addr
  arguments : addr<(X).compiled.hub.arguments ∨ (X).compiled.hub.arguments+7*(X).compiled.hub.argc≤addr

theorem boot_cell (addr : ℕ) (cell : BootCell A cap m addr) :
    (X).compiled.input addr=(X).mounted addr ∧ (X).compiled.seeded addr=(X).mounted addr ∧
    (X).compiled.commands addr=(X).mounted addr ∧ (X).compiled.entered addr=(X).mounted addr := by
  have h : (X).compiled.input addr=(X).mounted addr:=
    after_away _ _ _ _ cell.counter (HistoryStageResult.endpoints_outside X addr cell.endpoints)
  have s : (X).compiled.seeded addr=(X).mounted addr:=(before_fill _ _ _ _ _ cell.seed).trans h
  have c : (X).compiled.commands addr=(X).mounted addr:=(before_fill _ _ _ _ _ cell.commands).trans s
  exact ⟨h,s,c,(before_fill _ _ _ _ _ cell.arguments).trans c⟩

private theorem read_eq_at (now old : Memory W) (addr : ℕ)
    (word : ∀ j : Fin 4, now (addr + j.val) = old (addr + j.val)) :
    HistoryBoundedJoin.read addr (numeric now) = HistoryBoundedJoin.read addr (numeric old) := by
  have h0 : numeric now addr = numeric old addr := by
    change (now addr).val = (old addr).val
    simpa only [Fin.val_zero, Nat.add_zero] using congrArg Fin.val (word 0)
  have h1 : numeric now (addr + 1) = numeric old (addr + 1) := congrArg Fin.val (word 1)
  have h2 : numeric now (addr + 2) = numeric old (addr + 2) := congrArg Fin.val (word 2)
  have h3 : numeric now (addr + 3) = numeric old (addr + 3) := congrArg Fin.val (word 3)
  unfold HistoryBoundedJoin.read
  rw [h0, h1, h2, h3]

theorem cache_infos (cells : SourceCells A cap S (numeric m) W) (owned : n≤cap)
    (physical : ∀ i : Fin (n+1),∀ j : Fin 4,BootCell A cap m (HistoryStageRoot.ptr S (numeric m) i.val+j.val)) :
    CachedInfo S (numeric m) (X).compiled.input ∧ CachedInfo S (numeric m) (X).compiled.seeded ∧
      CachedInfo S (numeric m) (X).compiled.commands ∧ CachedInfo S (numeric m) (X).compiled.entered := by
  have keep:=(phase_frames A cap m owned (cells.node 4).2).2.2.2.2.2.2
  have ext (i : Fin (n+1)) (j : Fin 4) : External A cap (HistoryStageRoot.ptr S (numeric m) i.val+j.val) := by
    by_cases h : i.val=0
    · rw [HistoryStageRoot.ptr,ite_eq_left h];exact (cells.kernel (j.castLE (by decide))).2
    · rw [HistoryStageRoot.ptr,ite_eq_right h]
      exact (cells.old (i.val-1) (by have:=i.isLt;omega) (j.castLE (by decide))).2
  have recover (mem : Memory W) (eq : ∀ i : Fin (n+1),∀ j : Fin 4,
      mem (HistoryStageRoot.ptr S (numeric m) i.val+j.val)=(X).mounted (HistoryStageRoot.ptr S (numeric m) i.val+j.val)) :
      CachedInfo S (numeric m) mem := by
    intro i
    exact read_eq_at mem m (HistoryStageRoot.ptr S (numeric m) i.val)
      (fun j => (eq i j).trans (keep _ (ext i j)))
  exact ⟨recover _ (fun i j=>(boot_cell A cap m _ (physical i j)).1),
    recover _ (fun i j=>(boot_cell A cap m _ (physical i j)).2.1),
    recover _ (fun i j=>(boot_cell A cap m _ (physical i j)).2.2.1),
    recover _ (fun i j=>(boot_cell A cap m _ (physical i j)).2.2.2)⟩

section
variable {G : HistoryGatherBody.Layout} {cap₀ : ℕ} {T : Input} {raw : ℕ→ℕ} {mem : Memory W}
variable (s : Snapshot G cap₀ T raw mem)
include s

theorem Snapshot.hub_value (j : Fin 6) (small : (HistoryStageRoot.hub T raw).words j<2^W) :
    numeric mem (HistoryStageBody.hub G+j.val)=(HistoryStageRoot.hub T raw).words j :=
  (congrArg Fin.val (s.hub j)).trans (Fin.val_cast_of_lt small)

theorem Snapshot.link_value (i : Fin (childCount T raw+1)) (j : Fin 4)
    (small : (HistoryStageRoot.link T raw i.val).words j<2^W) :
    numeric mem (links G+(4*i.val+j.val))=(HistoryStageRoot.link T raw i.val).words j :=
  (congrArg Fin.val (s.link i j)).trans (Fin.val_cast_of_lt small)

theorem Snapshot.operand_value (i : Fin (childCount T raw+1)) (j : Fin 5)
    (small : operands T raw i.val j<2^W) :
    numeric mem (mapArgs G cap₀+(5*i.val+j.val))=operands T raw i.val j :=
  (congrArg Fin.val (s.operand i j)).trans (Fin.val_cast_of_lt small)

theorem Snapshot.readHub (L : HistoryBoundedBody.Layout) (loc : L.hub=HistoryStageBody.hub G)
    (fits : ∀j,(HistoryStageRoot.hub T raw).words j<2^W) :
    HistoryBoundedBody.readHub L (numeric mem)=HistoryStageRoot.hub T raw := by
  have h0:=s.hub_value 0 (fits 0);have h1:=s.hub_value 1 (fits 1);have h2:=s.hub_value 2 (fits 2)
  have h3:=s.hub_value 3 (fits 3);have h4:=s.hub_value 4 (fits 4);have h5:=s.hub_value 5 (fits 5)
  simp only [Fin.val_zero,Nat.add_zero] at h0
  change numeric mem (HistoryStageBody.hub G+1)=_ at h1
  change numeric mem (HistoryStageBody.hub G+2)=_ at h2
  change numeric mem (HistoryStageBody.hub G+3)=_ at h3
  change numeric mem (HistoryStageBody.hub G+4)=_ at h4
  change numeric mem (HistoryStageBody.hub G+5)=_ at h5
  unfold HistoryBoundedBody.readHub
  rw [loc,h0,h1,h2,h3,h4,h5]
  rfl

theorem Snapshot.readChild (loc : T.links=links G) (i : Fin (childCount T raw+1))
    (fits : ∀j,(HistoryStageRoot.link T raw i.val).words j<2^W) :
    HistoryBoundedJoin.child (HistoryStageRoot.hub T raw) (numeric mem) i.val=HistoryStageRoot.link T raw i.val := by
  have cell (j : Fin 4) : numeric mem (links G+4*i.val+j.val)=(HistoryStageRoot.link T raw i.val).words j :=
    by rw [Nat.add_assoc];exact s.link_value i j (fits j)
  have h0:=cell 0;have h1:=cell 1;have h2:=cell 2;have h3:=cell 3
  simp only [Fin.val_zero,Nat.add_zero] at h0
  change numeric mem (links G+4*i.val+1)=_ at h1
  change numeric mem (links G+4*i.val+2)=_ at h2
  change numeric mem (links G+4*i.val+3)=_ at h3
  change HistoryBoundedJoin.Child.mk (numeric mem (T.links+4*i.val)) (numeric mem (T.links+4*i.val+1))
    (numeric mem (T.links+4*i.val+2)) (numeric mem (T.links+4*i.val+3))=_
  rw [loc,h0,h1,h2,h3]
  rfl

end

end
end ThreeFlat.RAM.HistoryStageSnapshots

end OAI
