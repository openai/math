import OAI.ThreeFlat.RAM.HistorySelectedOwnerData
import OAI.ThreeFlat.RAM.HistorySeedWindow
import OAI.ThreeFlat.RAM.HistoryNodeAddress
import OAI.ThreeFlat.RAM.HistoryMotifJoin
import OAI.ThreeFlat.RAM.HistoryInitialBody
import OAI.ThreeFlat.RAM.HistorySelectedCharge
import OAI.ThreeFlat.RAM.PhysicalProcedureIf
import OAI.ThreeFlat.RAM.TickPhysicalABI

namespace OAI
/-! # Executing the kernel/old-child join at a real physical stage -/

namespace ThreeFlat.RAM.HistoryStageBody

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalProcedure PhysicalPinsExpr HistoryStageRoot
open scoped Fin.CommRing

noncomputable section
variable {W : ℕ}

private abbrev T (W : ℕ) := Term W 0 1
def l (x : ℕ) : T W := .literal (x : Word W)
def a (x y : T W) : T W := .binary .add x y
def times (x y : T W) : T W := .binary .mul x y
def cut (x y : T W) : T W := .select .lt x y (l 0) (.binary .sub x y)
def select (key : T W) : ℕ → List (T W) → T W
  | _,[] => l 0
  | i,x::xs => .select .eq key (l i) x (select key (i+1) xs)

variable (A : HistoryGatherBody.Layout) (cap : ℕ)

def nodeId : T W := HeaderScan.closed (HistoryNodePorts.id A.nodePorts)
def cn : T W := HeaderScan.closed (HistoryNodePorts.childCount A.nodePorts)
def cache : T W := a (l A.nodePorts.cache) (times (l 8) (nodeId A))
def ptr (k : HistoryScratch.Local) : T W := a (l A.party.arena)
  (times (a (times (nodeId A) (l A.party.V)) (l (HistoryScratch.sector A.party.motifs A.party.parties k))) (l A.party.V))

def loc (k : ℕ) := A.party.seed+64+k
def args := loc A 0
def hub := loc A 48
def links := loc A 55
def mapArgs := links A+4*(cap+1)
def extArgs := mapArgs A cap+5*(cap+1)
def extCommands := extArgs A cap+3*cap

def input : List (T W) :=
  let kernel := match A.mode with
    | .shrink _ => ptr A ⟨0,0,4,1⟩
    | .refresh .. => ptr A ⟨2,0,3,1⟩
  [nodeId A,l A.nodePorts.nodes,l A.nodePorts.cache,kernel,ptr A ⟨0,0,5,0⟩,l A.party.maps,
    l (mapArgs A cap),ptr A ⟨0,0,5,1⟩,l (links A),l A.party.arguments,l (extArgs A cap)]

/-- The range header starts at offset 12. Six pairs locate the generated
descriptor banks, the next two activate the ext-copy controller, and
the last pair writes the result directly into the shared chronological cache. -/
def fields : List (T W) :=
  let n := cn A
  let s := a n (l 1)
  input A cap ++ [l (loc A 12),
    l (hub A),l 6,l (links A),times (l 4) s,l (mapArgs A cap),times (l 5) s,
    l (extArgs A cap),times (l 3) n,l (extCommands A cap),times (l 7) n,
    l (extCommands A cap),a (l (extCommands A cap)) (times (l 7) n),cache A,l 6]

def destination (b : Bank) : T W := match b with
  | .hub => l (hub A)
  | .link => l (links A)
  | .mapArgs => l (mapArgs A cap)
  | .extArgs => l (extArgs A cap)
  | .extCommand => l (extCommands A cap)
  | .result => cache A

def fieldProgram (W : ℕ) (b : Bank) : T W :=
  (HeaderScan.closed (HistoryStageRoot.formula cap b)).instantiate
    (fun i => if i=0 then l (args A) else if i=5 then cut (.result 0) (destination A cap b) else l 0)

def scan (W : ℕ) (b : Bank) (off : ℕ) : Procedure W :=
  HeaderScan.procedure ((loc A 11 : ℕ):Word W) off (off+1) (fieldProgram A cap W b)


def joinHeader (W : ℕ) : T W := select (cut (.result 0) (l (args A))) 0 (fields A cap)

open private select_binds binary_binds from
  OAI.ThreeFlat.RAM.HistoryGatherBody
open private id_field_cost count_field_cost from
  OAI.ThreeFlat.RAM.HistoryMotifJoin

private theorem literal_cost (v : ℕ) : (l (W := W) v).binds = 1 := rfl
private theorem cursor_cost : (Term.result 0 : T W).binds = 0 := rfl

local macro "stage_costs" : tactic => `(tactic|
  simp only [cut, cache, ptr, nodeId, cn, a, times, select_binds, binary_binds,
    literal_cost, cursor_cost, HeaderScan.binds_closed, id_field_cost, count_field_cost])

private theorem select_cost {U : ℕ} (x : T W) (y : T U) (i j : ℕ)
    (xs : List (T W)) (ys : List (T U)) (key : x.binds = y.binds)
    (rows : xs.map Term.binds = ys.map Term.binds) :
    (select x i xs).binds = (select y j ys).binds := by
  induction xs generalizing i j ys with
  | nil => cases ys with
    | nil => rfl
    | cons b ys => simp at rows
  | cons a xs ih => cases ys with
    | nil => simp at rows
    | cons b ys =>
      simp only [List.map_cons, List.cons.injEq] at rows
      simp only [select, select_binds, literal_cost, key, rows.1, ih (i+1) (j+1) ys rows.2]

theorem joinHeader_work (B : HistoryGatherBody.Layout) (W U : ℕ) (h : A.mode=B.mode) :
    (joinHeader A cap W).binds=(joinHeader B cap U).binds := by
  apply select_cost (W := W) (U := U)
    (cut (.result 0) (l (args A))) (cut (.result 0) (l (args B)))
    0 0 (fields A cap) (fields B cap)
  · stage_costs
  · cases ha : A.mode <;> have hb := h.symm.trans ha <;>
      simp only [fields, input, ha, hb, List.map_append, List.map_cons, List.map_nil] <;>
      stage_costs

theorem field_bound (W : ℕ) (b : Bank) :
    (fieldProgram A cap W b).binds≤(HistoryStageRoot.formula cap b).work+5000 := by
  rw [fieldProgram,Term.binds_instantiate,HeaderScan.binds_closed]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _ : Fin 13, 100 := by
      apply Finset.sum_le_sum
      intro i _
      split
      · simp only [literal_cost]
        decide
      · split
        · cases b <;> simp only [destination] <;> stage_costs <;> decide
        · simp only [literal_cost]
          decide
    _ ≤ 5000 := by simp

/-- All parent child records are materialized before storing the new cache.
The tensor kernel is the first linked child; physical old factors follow in
the native ownership list. The child endpoint copy and the factor joins use
the same real seven-word sweep on their separately generated rectangles. -/
def join (W : ℕ) : Procedure W :=
  let vals := fields (W:=W) A cap
  let init := PhysicalInputPhases.writing (joinHeader A cap W)
    Fin.elim0 (args A) vals.length
  let q := ((init.seq (scan A cap W .hub 0)).seq (scan A cap W .link 2)).seq (scan A cap W .mapArgs 4)
  let q := (q.seq (scan A cap W .extArgs 6)).seq (scan A cap W .extCommand 8)
  let cachePtr := PhysicalInputPhases.writing (cache A : T W) Fin.elim0 (hub A+6) 1
  let ext := HistoryReadyTape.execute (HistorySelectedOps.rows (.literal (0:Word W) : Term W 0 4) [])
    (Fin.last 0) (fun _ => ((loc A 22 : ℕ):Word W))
  let joined := HistoryBoundedBody.procedure W ⟨hub A,A.party.seed,A.party.commands⟩ (cap+1)
  ((q.seq cachePtr).seq ext).seq (joined.seq (scan A cap W .result 12))

def procedure (W : ℕ) : Procedure W := (HistoryMotifJoin.kernelProcedure A W cap).seq (join A cap W)


section Execution
open Computability.VPVNP.BurstRAM.PrivateRAM HistoryPartyBatchExec HistoryBoundedBody HistoryReadyTape HistoryJoinScan
open scoped BigOperators

def numInput (m : ℕ→ℕ) : Input :=
  let id := m A.nodePorts.cursor-1
  let atNode (r : HistoryScratch.Local) := HistoryScratch.atWord A.party.arena A.party.V A.party.motifs A.party.parties id r 0
  let kr := match A.mode with | .shrink _=> atNode ⟨0,0,4,1⟩ | .refresh ..=>atNode ⟨2,0,3,1⟩
  ⟨id,A.nodePorts.nodes,A.nodePorts.cache,kr,atNode ⟨0,0,5,0⟩,A.party.maps,
    mapArgs A cap,atNode ⟨0,0,5,1⟩,links A,A.party.arguments,extArgs A cap⟩

def bankBase (A : HistoryGatherBody.Layout) (cap : ℕ) (T : Input) : Bank→ℕ
  | .hub => hub A | .link => links A | .mapArgs=>mapArgs A cap | .extArgs=>extArgs A cap
  | .extCommand=>extCommands A cap | .result=>T.resultBase+8*T.id

def rowCount (n : ℕ) : Bank→ℕ
  | .hub | .result=>1 | .link | .mapArgs=>n+1 | .extArgs | .extCommand=>n

def bankSize (T : Input) (raw : ℕ→ℕ) (b : Bank) := b.width * rowCount (HistoryStageRoot.childCount T raw) b

def bankWord (T : Input) (raw : ℕ→ℕ) (b : Bank) (start a : ℕ) : Word W :=
  let key := a-start
  (b.word T raw (key/b.width) ⟨key%b.width,Nat.mod_lt _ (by cases b <;> decide)⟩ : ℕ)

def regs (start key : ℕ) (j : Fin 13) := if j=0 then start else if j=5 then key else 0

theorem field_value (T : Input) (raw : ℕ→ℕ) (m : Memory W) (b : Bank) (dest i : ℕ) (j : Fin b.width)
    (word : raw=numeric m) (room : dest+b.width*i+j.val<2^W)
    (atDest : ∀ a : Word W,(destination A cap b).eval Fin.elim0 m (fun _=>a)=(dest:Word W))
    (header : ∀ f : Fin 11,raw (args A+f.val)=T.words f)
    (n : i≤cap) (count : HistoryStageRoot.childCount T raw≤cap)
    (fit : (HistoryStageRoot.formula cap b).Fits W (fun _=>0) raw (regs (args A) (b.width*i+j.val))) :
    (fieldProgram A cap W b).eval Fin.elim0 m (fun _=>((dest+(b.width*i+j.val):ℕ):Word W))=
      (b.word T raw i j:Word W) := by
  let key := b.width*i+j.val
  let a : Word W := ((dest+key:ℕ):Word W)
  have da := atDest a
  have leq : ¬a<(dest:Word W) := by
    change ¬a.val<(dest:Word W).val
    rw [show a.val=dest+key from Fin.val_cast_of_lt (by dsimp [key];omega),
      Fin.val_cast_of_lt (by omega : dest<2^W)]
    omega
  unfold fieldProgram
  rw [Term.eval_instantiate]
  have argEq :
      (fun z : Fin 13=>(if z=0 then l (args A) else if z=5 then cut (.result 0) (destination A cap b) else l 0).eval
         Fin.elim0 m (fun _=>a)) = (fun z=>(regs (args A) key z:Word W)) := by
    funext z
    by_cases zero : z = 0
    · simp only [ite_eq_left zero, regs, l, Term.eval_literal]
    by_cases five : z = 5
    · have cursor : (Term.result 0 : Term W 0 1).eval Fin.elim0 m (fun _ => a) = a := rfl
      simp only [ite_eq_right zero, ite_eq_left five, regs, cut, Term.eval_select, Term.eval_binary,
        cursor, da, Comparison.test, BinaryOp.eval, decide_eq_true_eq, ite_eq_right leq]
      simp [a, Nat.cast_add]
    · simp only [ite_eq_right zero, ite_eq_right five, regs, l, Term.eval_literal]
  rw [argEq]
  have actual := closed_eval (HistoryStageRoot.formula cap b) raw (regs (args A) key) fit
  have memory : (fun addr => (raw addr : Word W)) = m := by
    rw [word, word_numeric]
  rw [memory] at actual
  exact actual.trans (congrArg (fun k : ℕ => (k : Word W))
    (HistoryStageRoot.bank_word W cap T (args A) _ raw _ b i j header
      (by simp [regs]) (by simp [regs, key]) n count))

/-- A generated bank phase has no callback. Every column is the physical stage
formula evaluated on the resident original node and previously written child rows. -/
theorem bank_exec (T : Input) (m : Memory W) (b : Bank) (off dest : ℕ)
    (head0 : HeaderScan.headerWord m ((loc A 11 : ℕ):Word W) off=(dest:Word W))
    (head1 : HeaderScan.headerWord m ((loc A 11 : ℕ):Word W) (off+1)=(bankSize T (numeric m) b:Word W))
    (header : ∀ f : Fin 11,numeric m (args A+f.val)=T.words f)
    (atDest : ∀ a : Word W,(destination A cap b).eval Fin.elim0 m (fun _=>a)=(dest:Word W))
    (space : dest+bankSize T (numeric m) b<2^W)
    (count : HistoryStageRoot.childCount T (numeric m)≤cap)
    (safe : Protected (fieldProgram A cap W b) m dest (bankSize T (numeric m) b))
    (fit : ∀ i : Fin (rowCount (HistoryStageRoot.childCount T (numeric m)) b), ∀ j : Fin b.width,
      (HistoryStageRoot.formula cap b).Fits W (fun _=>0) (numeric m) (regs (args A) (b.width*i.val+j.val))) :
    (scan A cap W b off).Exec m
      (fillSegment dest (bankSize T (numeric m) b) (bankWord T (numeric m) b dest) m)
      (13+bankSize T (numeric m) b*(2*(fieldProgram A cap W b).binds+4)) := by
  apply scan_exec _ _ _ _ _ _ _ _ space safe head0 head1
  intro a lo hi
  have nonzero : 0<b.width := by cases b <;> decide
  let key := a.val-dest
  have range : key<b.width*rowCount (HistoryStageRoot.childCount T (numeric m)) b := by
    change a.val<dest+b.width*rowCount (HistoryStageRoot.childCount T (numeric m)) b at hi
    dsimp [key];omega
  let i : Fin (rowCount (HistoryStageRoot.childCount T (numeric m)) b) :=
    ⟨key/b.width,(Nat.div_lt_iff_lt_mul nonzero).mpr (by simpa [Nat.mul_comm] using range)⟩
  let j : Fin b.width := ⟨key%b.width,Nat.mod_lt _ nonzero⟩
  have eqKey : b.width*i.val+j.val=key := Nat.div_add_mod key b.width
  have eqAddr : dest+(b.width*i.val+j.val)=a.val := by rw [eqKey];dsimp [key];omega
  have bound : i.val≤cap := by
    have := i.isLt
    cases b <;> simp only [rowCount] at this <;> omega
  have val := field_value A cap T (numeric m) m b dest i.val j rfl (by omega) atDest header bound count (fit i j)
  rw [eqAddr,Fin.cast_val_eq_self] at val
  exact val

namespace Endpoints

def info (T : Input) (raw : ℕ→ℕ) (i : ℕ) := atResult raw (childPtr T raw i)

def srcAddr (T : Input) (raw : ℕ→ℕ) (i : ℕ) := (info T raw i).ext
def width (T : Input) (raw : ℕ→ℕ) (i : ℕ) := (info T raw i).extCount
def toAddr (T : Input) (raw : ℕ→ℕ) (i : ℕ) := T.ext+HistoryStageRoot.prefix T raw i Result.extCount

def job (T : Input) (raw : ℕ→ℕ) (initial : Memory W) (i : ℕ) : Job W :=
  ⟨toAddr T raw i,width T raw i,fun a=>initial (srcAddr T raw i+(a-toAddr T raw i))⟩

def jobs (T : Input) (raw : ℕ→ℕ) (initial : Memory W) :=
  (List.range (HistoryStageRoot.childCount T raw)).map (job T raw initial)

def survives (T : Input) (raw : ℕ→ℕ) (a : ℕ) := ∀ i, i<HistoryStageRoot.childCount T raw →
  a<toAddr T raw i ∨ toAddr T raw i+width T raw i≤a

structure Banks (T : Input) (raw : ℕ→ℕ) (cmd ptr : ℕ) (m : Memory W) : Prop where
  room : cmd+7*HistoryStageRoot.childCount T raw<2^W
  argsRoom : T.extArguments+3*HistoryStageRoot.childCount T raw<2^W
  sources : ∀ i,i<HistoryStageRoot.childCount T raw→srcAddr T raw i+width T raw i<2^W
  destinations : ∀ i,i<HistoryStageRoot.childCount T raw→toAddr T raw i+width T raw i<2^W
  wide : 12≤2^W
  first : ptr+2≤cmd
  argsSeparate : ∀ i,i<HistoryStageRoot.childCount T raw→∀ j : Fin 3,
    T.extArguments+(3*i+j.val)≠ptr ∧ survives T raw (T.extArguments+(3*i+j.val))
  srcSeparate : ∀ i,i<HistoryStageRoot.childCount T raw→∀ j : Fin (width T raw i),
    srcAddr T raw i+j.val≠ptr ∧ survives T raw (srcAddr T raw i+j.val)
  cursorSeparate : ∀ i,i<HistoryStageRoot.childCount T raw→
    toAddr T raw i+width T raw i≤ptr ∨ ptr+2≤toAddr T raw i
  cmdSeparate : ∀ i,i<HistoryStageRoot.childCount T raw→
    toAddr T raw i+width T raw i≤cmd ∨ cmd+7*HistoryStageRoot.childCount T raw≤toAddr T raw i
  head : m ptr=(cmd:Word W)
  stop : m (ptr+1)=((cmd+7*HistoryStageRoot.childCount T raw:ℕ):Word W)
  command : ∀ i,i<HistoryStageRoot.childCount T raw→∀ j : Fin 7,
    m (cmd+7*i+j.val)=(endpointCommand T raw i j:Word W)
  arguments : ∀ i,i<HistoryStageRoot.childCount T raw→∀ j : Fin 3,
    m (T.extArguments+(3*i+j.val))=(endpointWords T raw i j:Word W)

theorem Banks.loaded {T : Input} {raw : ℕ→ℕ} {cmd ptr : ℕ} {m : Memory W} (B : Banks T raw cmd ptr m) :
    Loaded cmd (jobs T raw m) m := by
  intro z
  have hz : z.val<HistoryStageRoot.childCount T raw := by simpa [jobs] using z.isLt
  have start := B.command z.val hz (1:Fin 7)
  have last := B.command z.val hz (6:Fin 7)
  have entry : (jobs T raw m).get z = job T raw m z.val := by
    have inRange : z.val < (List.range (HistoryStageRoot.childCount T raw)).length := by
      simpa only [List.length_range] using hz
    exact (List.getElem_map (job T raw m) (l:=List.range (HistoryStageRoot.childCount T raw))
      (i:=z.val) (h:=z.isLt)).trans (congrArg (job T raw m) (List.getElem_range inRange))
  rw [entry]
  simpa [job,endpointCommand,endpointWords,toAddr,width,info,Job.finish]
    using And.intro start last

theorem Banks.reads {T : Input} {raw : ℕ→ℕ} {cmd ptr : ℕ} {m : Memory W} (B : Banks T raw cmd ptr m) :
    readJobs (HistoryBoundedBody.Tape.expr W) (fun _=>(ptr:Word W)) (ptr:Word W) (jobs T raw m) m := by
  let c := HistoryStageRoot.childCount T raw
  have room : ptr+1<2^W := by have := B.first; have := B.room;omega
  have ctrl : (ptr:Word W).val=ptr := Fin.val_cast_of_lt (by omega)
  have single (l : List ℕ) : l.flatMap (fun i=>[job T raw m i])=l.map (job T raw m) := by
    induction l with | nil=>rfl | cons a l ih=>simp [ih]
  rw [jobs,←single]
  apply read_children
  intro earlier i later eqn
  have live : i<c := List.mem_range.mp (by rw [eqn];simp)
  have rank : earlier.length=i := by
    simpa only [List.getElem_range] using List.getElem_of_append eqn rfl
  let emitted := earlier.flatMap fun j=>[job T raw m j]
  let before := after (ptr:Word W) emitted m
  have inc (x) (hx : x∈emitted) : ∃ t,t<c ∧ x=job T raw m t := by
    obtain ⟨t,ht,e⟩ := List.mem_flatMap.mp hx
    refine ⟨t,List.mem_range.mp (by rw [eqn];simp [ht]),?_⟩
    simpa using e
  have frame (a : ℕ) (nc : a≠ptr) (apart : survives T raw a) : before a=m a := by
    apply after_away (ptr:Word W) emitted m a (by rwa [ctrl])
    intro x hx
    obtain ⟨t,ht,rfl⟩ := inc x hx
    exact apart t ht
  have cursor : before ptr=((cmd+7*i:ℕ):Word W) := by
    have afterR := HistoryPartyTapeRun.cursor_after (m:=m) (xs:=emitted) (ptr:Word W) (by
      intro x hx
      obtain ⟨t,ht,rfl⟩ := inc x hx
      rw [ctrl]
      have := B.cursorSeparate t ht
      change ptr<toAddr T raw t ∨ toAddr T raw t+width T raw t≤ptr
      omega)
    have len : emitted.length=i := by dsimp [emitted]; rw [single,List.length_map,rank]
    simpa only [before,ctrl,B.head,len,Nat.cast_add] using afterR
  constructor
  · intro a mem lo hi same
    change toAddr T raw i≤a.val at lo
    change a.val<toAddr T raw i+width T raw i at hi
    let j : Fin (width T raw i) := ⟨a.val-toAddr T raw i,by omega⟩
    have sameAt (x : ℕ) (safe : x≠ptr ∧ survives T raw x) : mem x=m x :=
      (same x (safe.2 i live)).trans (frame x safe.1 safe.2)
    have cmdAt (f : Fin 7) : mem (cmd+7*i+f.val)=(endpointCommand T raw i f:Word W) := by
      rw [sameAt _ ⟨by have := B.first;omega,by
        intro k hk;have := B.cmdSeparate k hk;have := f.isLt;omega⟩,B.command i live]
    have ptrAt : mem (ptr:Word W).val=((cmd+7*i:ℕ):Word W) := by
      have safe : ptr<toAddr T raw i ∨ toAddr T raw i+width T raw i≤ptr := by
        have := B.cursorSeparate i live
        omega
      rw [ctrl]
      exact (same ptr safe).trans cursor
    have ptrValid : cmd+7*i+2<2^W := by have := B.room;dsimp [c] at live;omega
    have oper : HistorySelectedOps.operandPointer (K:=0) (fun _=>(ptr:Word W)) mem=((T.extArguments+3*i:ℕ):Word W) := by
      change mem (mem (ptr:Word W).val).val=_
      rw [ptrAt,Fin.val_cast_of_lt (by omega)]
      simpa [endpointCommand] using cmdAt (0:Fin 7)
    have tag : HistorySelectedOps.tag (K:=0) (fun _=>(ptr:Word W)) mem=10 := by
      change (mem (mem (ptr:Word W).val+2).val).val=_
      rw [ptrAt,←Nat.cast_ofNat (R:=Word W) (n:=2),←Nat.cast_add,Fin.val_cast_of_lt ptrValid]
      have t := cmdAt (2:Fin 7)
      change mem (cmd+7*i+2)=(10:Word W) at t
      rw [t]
      change 10 % (2^W)=10
      exact Nat.mod_eq_of_lt (by have := B.wide;omega)
    have args (f : Fin 3) : mem (((T.extArguments+3*i:ℕ):Word W)+(f.val:Word W)).val=(endpointWords T raw i f:Word W) := by
      rw [←Nat.cast_add,Fin.val_cast_of_lt (by have := B.argsRoom;have := f.isLt;dsimp [c] at live;omega),Nat.add_assoc,
        sameAt _ (B.argsSeparate i live f),B.arguments i live]
    have src := B.sources i live
    have hj := j.isLt
    have eqA : a=((toAddr T raw i+j.val:ℕ):Word W) := by rw [show toAddr T raw i+j.val=a.val by dsimp [j];omega,Fin.cast_val_eq_self]
    have read := HistorySelectedOps.map_word (.literal (0:Word W) : Term W 0 4) [] (fun _=>(ptr:Word W)) mem (fun _=>a)
      10 (toAddr T raw i) (srcAddr T raw i) 0 0 j.val B.wide tag (Or.inr (Or.inl rfl))
      (by rw [oper];simpa [endpointWords,toAddr] using args 0)
      (by rw [oper];simpa [endpointWords,srcAddr,info] using args 2)
      (by intro h; omega) (by intro h; omega) eqA
      (by omega) (by omega) (by omega)
    simpa [HistoryBoundedBody.Tape.expr,job,j,sameAt (srcAddr T raw i+j.val) (B.srcSeparate i live j)] using read
  · trivial

theorem Banks.execute {T : Input} {raw : ℕ→ℕ} {cmd ptr : ℕ} {m : Memory W} (B : Banks T raw cmd ptr m) :
    let c : Word W := (ptr:Word W)
    let e := HistoryBoundedBody.Tape.expr W
    let ops := jobs T raw m
    (HistoryReadyTape.execute e (Fin.last 0) (fun _=>c)).Exec m (after c ops m) (cost e.binds ops) := by
  let c : Word W := (ptr:Word W)
  let ops := jobs T raw m
  have length : ops.length=HistoryStageRoot.childCount T raw := by simp [ops,jobs]
  have ctrl : c.val=ptr := Fin.val_cast_of_lt (by have := B.first;have := B.room;omega)
  have out (x : Job W) (hx : x∈ops) : ∃ i,i<HistoryStageRoot.childCount T raw ∧ x=job T raw m i := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact ⟨i,List.mem_range.mp hi,rfl⟩
  change (HistoryReadyTape.execute (HistoryBoundedBody.Tape.expr W) (Fin.last 0) (fun _=>c)).Exec
    m (after c ops m) (cost (HistoryBoundedBody.Tape.expr W).binds ops)
  intro P R K machine pc reg pub exit installed params cfg incoming start initial
  subst incoming
  refine HistoryReadyTape.execute_spec (HistoryBoundedBody.Tape.expr W) (Fin.last 0) (fun _=>c)
    (fun z=>z=m) ops cmd (by rw [ctrl]; exact B.first)
    (by rw [length]; exact B.room) ?_ ?_ ?_ ?_ machine pc reg pub exit installed params cfg m start rfl
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := out x hx
    simpa [ctrl,job,Job.finish] using B.cursorSeparate i hi
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := out x hx
    simpa [length,job,Job.finish] using B.cmdSeparate i hi
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := out x hx
    exact B.destinations i hi
  · intro incoming same
    subst incoming
    refine ⟨by rw [ctrl]; exact B.head, ?_, B.loaded, B.reads⟩
    have next : (c+1).val=ptr+1 := by
      change (((ptr:ℕ):Word W)+1).val=_
      rw [←Nat.cast_one (R:=Word W), ←Nat.cast_add,
        Fin.val_cast_of_lt (by have := B.first; have := B.room; omega)]
    rw [next, length]
    exact B.stop

theorem dest_monotone {T : Input} {raw : ℕ→ℕ} (i j : ℕ) (order : i≤j) : toAddr T raw i≤toAddr T raw j := by
  unfold toAddr HistoryStageRoot.prefix
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum_of_subset (Finset.range_mono order)

theorem dest_next (T : Input) (raw : ℕ→ℕ) (i : ℕ) :
    toAddr T raw (i+1)=toAddr T raw i+width T raw i := by
  simp [toAddr,HistoryStageRoot.prefix,width,info,Finset.sum_range_succ,Nat.add_assoc]

/-- Every physical endpoint word of a live child survives through the endpoint
concatenation at the very offset used by the mathematical inherited pin order. -/
theorem Banks.copied {T : Input} {raw : ℕ→ℕ} {cmd ptr : ℕ} {m : Memory W} (B : Banks T raw cmd ptr m)
    (i : Fin (HistoryStageRoot.childCount T raw)) (j : Fin (width T raw i.val)) :
    after (ptr:Word W) (jobs T raw m) m (toAddr T raw i.val+j.val) = m (srcAddr T raw i.val+j.val) := by
  let addr := toAddr T raw i.val+j.val
  have fit : ptr<2^W := by have := B.first;have := B.room;omega
  have hc : addr≠(ptr:Word W).val := by
    rw [Fin.val_cast_of_lt fit]
    have := B.cursorSeparate i.val i.isLt;have := j.isLt;dsimp [addr];omega
  have isMem : i.val∈List.range (HistoryStageRoot.childCount T raw) := List.mem_range.mpr i.isLt
  obtain ⟨left,right,all,uniq⟩ := List.eq_append_cons_of_mem isMem
  have notRight : i.val∉right := by
    have clean : (List.range (HistoryStageRoot.childCount T raw)).Nodup := List.nodup_range
    rw [all,List.nodup_append] at clean
    exact (List.nodup_cons.mp clean.2.1).1
  have away (x : Job W) (hx : x∈right.map (job T raw m)) : addr<x.start ∨ x.finish≤addr := by
    obtain ⟨k,member,rfl⟩ := List.mem_map.mp hx
    have ne : i.val≠k := by rintro rfl;exact notRight member
    rcases lt_or_gt_of_ne ne with left|right
    · have mo := dest_monotone (T:=T) (raw:=raw) (i.val+1) k left
      rw [dest_next] at mo
      have := j.isLt
      change addr<toAddr T raw k ∨ _
      dsimp [addr];omega
    · have mo := dest_monotone (T:=T) (raw:=raw) (k+1) i.val right
      rw [dest_next] at mo
      right;change toAddr T raw k+width T raw k≤addr;dsimp [addr];omega
  change after _ (jobs T raw m) m addr=_
  rw [jobs,all,List.map_append,List.map_cons,after_append,HistoryReadyTape.after,after_away _ _ _ _ hc away]
  have inside : toAddr T raw i.val≤addr ∧ addr<toAddr T raw i.val+width T raw i.val := by
    have := j.isLt;dsimp [addr];omega
  have offset : addr-toAddr T raw i.val=j.val := by dsimp only [addr]; omega
  simp only [HistoryJoinController.bumpMemory,writeMemory,ite_eq_right hc,job,fillSegment,ite_eq_left inside,offset]


section NativePorts
open Diagonal.HistoryContraction
variable {F Pins : Type*} [CommSemiring F] {S : Diagonal.HistoryContraction.Shape}
  {R : Rewrite S F} {t : Fin R.count}
  {L : PortLayout S Pins} {V : PortLayout (R.target t) Pins} {count : (R.target t).Site→ℕ}
  {order : ∀ v,Fin (count v)≃{j // R.owner t j=v}} {v : (R.target t).Site}
  {T : Input} {raw : ℕ→ℕ} {cmd ptr p : ℕ} {m : Memory W}

/-- The result is indexed by the genuine inherited pin type of the next
stage. Each entry is the physical tick source pointer carried by its child. -/
theorem Banks.inherited (B : Banks T raw cmd ptr m) (ports : Ports L V count order v T raw)
    (src : ∀ u,Fin (L.ext u)→Fin p)
    (resident : ∀ (i : Fin (count v)) (j : Fin (L.ext (order v i).val)),
      m (srcAddr T raw i.val+j.val)=((2+(src (order v i).val j).val:ℕ):Word W))
    (x : Fin ((L.inherit V count order).ext v)) :
    HistoryReadyTape.after (ptr:Word W) (jobs T raw m) m (T.ext+x.val)=
      ((2+(L.inheritedSources V count order src v x).val:ℕ):Word W) := by
  obtain ⟨⟨i,j⟩,rfl⟩ := finSigmaFinEquiv.surjective x
  change HistoryReadyTape.after (ptr:Word W) (jobs T raw m) m
      (T.ext+(L.inheritedIndex V count order v i j).val)=
      ((2+(L.inheritedSources V count order src v (L.inheritedIndex V count order v i j)).val:ℕ):Word W)
  have pref := HistoryStageRoot.prefix_value (T:=T) (m:=raw) Result.extCount (fun z : Fin (count v)=>L.ext (order v z).val)
    ports.childExt i.val i.isLt.le
  have widthEq : width T raw i.val=L.ext (order v i).val := ports.childExt i
  have copied : HistoryReadyTape.after (ptr:Word W) (jobs T raw m) m (toAddr T raw i.val+j.val) =
      m (srcAddr T raw i.val+j.val) := B.copied (i.cast ports.degree.symm) (j.cast widthEq.symm)
  have address : T.ext+(L.inheritedIndex V count order v i j).val = toAddr T raw i.val+j.val := by
    rw [L.inherited_offset V count order v i j,toAddr,pref,Nat.add_assoc]
  rw [address,L.inheritedSources_at V count order src v i j]
  exact copied.trans (resident i j)

end NativePorts

/-- Each child is visited once and every externally inherited address is copied once. -/
theorem tape_cost (T : Input) (raw : ℕ→ℕ) (m : Memory W) :
    cost (HistoryBoundedBody.Tape.expr W).binds (jobs T raw m)=
      6+19*HistoryStageRoot.childCount T raw+
      HistoryStageRoot.prefix T raw (HistoryStageRoot.childCount T raw) Result.extCount*
        (2*(HistoryBoundedBody.Tape.expr W).binds+4) := by
  set K := (HistoryBoundedBody.Tape.expr W).binds
  have exactCost (xs : List ℕ) : cost K (xs.map (job T raw m))=
      6+19*xs.length+(xs.map (width T raw)).sum*(2*K+4) := by
    induction xs with
    | nil => simp [cost]
    | cons x xs ih => simp [cost,job,ih,Nat.mul_add,Nat.add_mul];omega
  have lengths (n : ℕ) : ((List.range n).map (width T raw)).sum=HistoryStageRoot.prefix T raw n Result.extCount := by
    induction n with
    | zero=>simp [HistoryStageRoot.prefix]
    | succ n ih=>simp [List.range_succ,List.map_append,List.sum_append,HistoryStageRoot.prefix,Finset.sum_range_succ,
        ←show (∑ k∈Finset.range n,(atResult raw (childPtr T raw k)).extCount)=((List.range n).map (width T raw)).sum from ih.symm,width,info]
  simpa only [jobs,List.length_range,lengths] using exactCost (List.range (HistoryStageRoot.childCount T raw))


end Endpoints

/-- Memory of each of the actual six generated arrays at a physical node.
The raw data seen by a phase are always the output of the preceding phase. -/
def adjust (A : HistoryGatherBody.Layout) (cap : ℕ) (T : Input) (b : Bank) (m : Memory W) :=
  let lo := bankBase A cap T b
  fillSegment lo (bankSize T (numeric m) b) (bankWord T (numeric m) b lo) m

structure BankInput (T : Input) (b : Bank) (off : ℕ) (m : Memory W) : Prop where
  dest : HeaderScan.headerWord m ((loc A 11:ℕ):Word W) off=(bankBase A cap T b:Word W)
  length : HeaderScan.headerWord m ((loc A 11:ℕ):Word W) (off+1)=(bankSize T (numeric m) b:Word W)
  input : ∀ f : Fin 11,numeric m (args A+f.val)=T.words f
  loc : ∀ a : Word W,(destination A cap b).eval Fin.elim0 m (fun _=>a)=(bankBase A cap T b:Word W)
  space : bankBase A cap T b+bankSize T (numeric m) b<2^W
  children : HistoryStageRoot.childCount T (numeric m)≤cap
  reads : Protected (fieldProgram A cap W b) m (bankBase A cap T b) (bankSize T (numeric m) b)
  fits : ∀ i : Fin (rowCount (HistoryStageRoot.childCount T (numeric m)) b), ∀ j : Fin b.width,
    (HistoryStageRoot.formula cap b).Fits W (fun _=>0) (numeric m) (regs (args A) (b.width*i.val+j.val))

def writeCost (T : Input) (b : Bank) (m : Memory W) :=
  13+bankSize T (numeric m) b*(2*(fieldProgram A cap W b).binds+4)

theorem BankInput.run {T : Input} {b : Bank} {off : ℕ} {m : Memory W} (p : BankInput A cap T b off m) :
    (scan A cap W b off).Exec m (adjust A cap T b m) (writeCost A cap T b m) :=
  bank_exec A cap T m b off _ p.dest p.length p.input p.loc p.space p.children p.reads p.fits

structure StageRun (W : ℕ) where
  layout : HistoryGatherBody.Layout
  cap : ℕ
  inputs : Input
  memory : Memory W

namespace StageRun
variable (X : StageRun W)
local notation "a" => X.layout
local notation "c" => X.cap
local notation "t" => X.inputs

def initialized := HistoryMotifJoin.headerImage (joinHeader a c W) (args a) (fields (W:=W) a c).length X.memory
def withHub := adjust a c t .hub X.initialized
def withLinks := adjust a c t .link X.withHub
def withMap := adjust a c t .mapArgs X.withLinks
def withSources := adjust a c t .extArgs X.withMap
def withCommands := adjust a c t .extCommand X.withSources
def mounted := HistoryMotifJoin.headerImage (cache a : Term W 0 1) (hub a+6) 1 X.withCommands
def childRaw := numeric X.memory
def endpointJobs := Endpoints.jobs t X.childRaw X.mounted
def extReady := after (loc a 22:Word W) X.endpointJobs X.mounted
def compiled : HistoryBoundedBody.Build W :=
  ⟨⟨hub a,(a).party.seed,(a).party.commands⟩,HistoryStageRoot.hub t X.childRaw,c+1,X.extReady⟩

structure Header : Prop where
  fixedRoom : args a+(fields (W:=W) a c).length<2^W
  fixedFrame : Protected (joinHeader a c W) X.memory (args a) (fields (W:=W) a c).length
  hub : BankInput a c t .hub 0 X.initialized
  children : BankInput a c t .link 2 X.withHub
  maps : BankInput a c t .mapArgs 4 X.withLinks
  tuples : BankInput a c t .extArgs 6 X.withMap
  commands : BankInput a c t .extCommand 8 X.withSources
  resultRoom : HistoryStageBody.hub a+7<2^W
  resultFrame : Protected (cache a : Term W 0 1) X.withCommands (HistoryStageBody.hub a+6) 1
  copies : Endpoints.Banks t X.childRaw (extCommands a c) (loc a 22) X.mounted

def bootCost := 4+(fields (W:=W) a c).length*(2*(joinHeader a c W).binds+4)
def copyCost := HistoryReadyTape.cost (HistoryBoundedBody.Tape.expr W).binds X.endpointJobs
def prepareCost := (((((X.bootCost+writeCost a c t .hub X.initialized)+
      writeCost a c t .link X.withHub)+writeCost a c t .mapArgs X.withLinks)+writeCost a c t .extArgs X.withMap)+
      writeCost a c t .extCommand X.withSources)+(4+1*(2*(cache a:T W).binds+4))+X.copyCost

private def prelude :=
    let initial:=PhysicalInputPhases.writing (joinHeader a c W) Fin.elim0 (args a) (fields (W:=W) a c).length
    let n:=(((initial.seq (scan a c W .hub 0)).seq (scan a c W .link 2)).seq (scan a c W .mapArgs 4))
    let n:=(n.seq (scan a c W .extArgs 6)).seq (scan a c W .extCommand 8)
    let q:=PhysicalInputPhases.writing (cache a : Term W 0 1) Fin.elim0 (hub a+6) 1
    (n.seq q).seq (HistoryReadyTape.execute (HistoryBoundedBody.Tape.expr W) (Fin.last 0) (fun _=>(loc a 22:Word W)))

theorem prepare (H : X.Header) : X.prelude.Exec X.memory X.extReady X.prepareCost := by
  have headerRun : (PhysicalInputPhases.writing (joinHeader X.layout X.cap W) Fin.elim0
      (args X.layout) (fields (W:=W) X.layout X.cap).length).Exec X.memory X.initialized X.bootCost :=
    HistoryMotifJoin.write_header _ _ _ _ H.fixedRoom H.fixedFrame
  have save : (PhysicalInputPhases.writing (cache X.layout : T W) Fin.elim0 (hub X.layout+6) 1).Exec
      X.withCommands X.mounted (4+1*(2*(cache X.layout : T W).binds+4)) :=
    HistoryMotifJoin.write_header _ _ _ _ (by simpa only [Nat.add_assoc] using H.resultRoom) H.resultFrame
  intro labels registers slots machine
  exact Procedure.Exec.then
    (Procedure.Exec.then
      (Procedure.Exec.then
        (Procedure.Exec.then
          (Procedure.Exec.then
            (Procedure.Exec.then
              (Procedure.Exec.then headerRun (BankInput.run X.layout X.cap H.hub))
              (BankInput.run X.layout X.cap H.children))
            (BankInput.run X.layout X.cap H.maps))
          (BankInput.run X.layout X.cap H.tuples))
        (BankInput.run X.layout X.cap H.commands))
      save)
    (Endpoints.Banks.execute H.copies) machine

/-- Execution of the entire native stage-root operation, including the endpoint array and
the six-column cache record produced after relocating the mathematical child glue. -/
theorem join_run {F : Type*} {n p h : ℕ} {arity : Fin n→ℕ} (N : ∀ i,BitNetwork F (arity i))
    (wire : ∀ i,Fin (arity i)→BitSource h p) (id : ((Fin 3→Bool)→F)→ℕ)
    (q : Fin n→HistoryJoinScan.Header ℕ) (mapping : Fin n→Tape.MapRow)
    (base : ℕ) (head : X.Header) (source : HistoryBoundedBody.Build.Source X.compiled (Tape.tape (W:=W) N wire id q))
    (resident : HistoryBoundedBody.Build.Resident X.compiled N wire id q mapping base)
    (endHeader : BankInput a c t .result 12 (X.compiled.output (Tape.tape (W:=W) N wire id q)))
    (keep : let ops:=Tape.tape (W:=W) N wire id q
      let m:=X.compiled.output ops
      let out:=bankBase a c t .result
      out+bankSize t (numeric m) .result≤base ∨ base+4*(BitNetwork.Ordered.glue N wire).cells≤out) :
    let ops:=Tape.tape (W:=W) N wire id q
    let m:=X.compiled.output ops
    let out:=adjust a c t .result m
    (join a c W).Exec X.memory out (X.prepareCost+X.compiled.ticks ops+writeCost a c t .result m) ∧
      HistoryCompiledRows.Records id (BitNetwork.Ordered.glue N wire) base out := by
  let ops:=Tape.tape (W:=W) N wire id q
  let m:=X.compiled.output ops
  have compiled:=HistoryBoundedBody.Build.complete X.compiled N wire id q mapping base source resident
  refine ⟨?_,?_⟩
  · rw [Nat.add_assoc]
    exact Procedure.Exec.then (X.prepare head) (Procedure.Exec.then compiled.1 endHeader.run)
  · intro r j
    have hr:=r.isLt
    have hj:=j.isLt
    have outside : ¬(bankBase a c t .result≤base+(4*r.val+j.val) ∧
      base+(4*r.val+j.val)<bankBase a c t .result+bankSize t (numeric m) .result) := by
      change bankBase a c t .result + bankSize t (numeric m) .result ≤ base ∨
          base + 4*(BitNetwork.Ordered.glue N wire).cells ≤ bankBase a c t .result at keep
      omega
    calc
      adjust a c t .result m (base+(4*r.val+j.val)) = m (base+(4*r.val+j.val)) := by
        unfold adjust fillSegment
        rw [ite_eq_right outside]
      _ = _ := compiled.2 r j

/-- Single chronological step with the semantic output used by the actual
multistage contraction. A root and each old child have the order published by
the stage itself. -/
theorem join_stage {F Pins : Type*} [CommSemiring F] {S : Diagonal.HistoryContraction.Shape}
    {R : Diagonal.HistoryContraction.Rewrite S F} {b : Fin R.count}
    {old : Diagonal.HistoryContraction.Form S Pins} {newForm : Diagonal.HistoryContraction.Form (R.target b) Pins}
    (D : Diagonal.HistoryContraction.Stage R b old newForm) (forest : Diagonal.HistoryContraction.Forest F old)
    (v : (R.target b).Site) (id : ((Fin 3→Bool)→F)→ℕ)
    (q : Fin (D.count v+1)→HistoryJoinScan.Header ℕ) (mapping : Fin (D.count v+1)→Tape.MapRow)
    (head : X.Header)
    (source : HistoryBoundedBody.Build.Source X.compiled (Tape.tape (W:=W) (fun i=>(D.tapeFactor forest v i).compile) (D.tapePin forest v) id q))
    (resident : HistoryBoundedBody.Build.Resident X.compiled (fun i=>(D.tapeFactor forest v i).compile) (D.tapePin forest v) id q mapping (t).stream)
    (endHeader : let ops:=Tape.tape (W:=W) (fun i=>(D.tapeFactor forest v i).compile) (D.tapePin forest v) id q
      BankInput a c t .result 12 (X.compiled.output ops))
    (sorted : (t).stream+4*(D.assemble forest v).rows≤bankBase a c t .result) :
    let ops:=Tape.tape (W:=W) (fun i=>(D.tapeFactor forest v i).compile) (D.tapePin forest v) id q
    let m:=X.compiled.output ops
    let out:=adjust a c t .result m
    (join a c W).Exec X.memory out (X.prepareCost+X.compiled.ticks ops+writeCost a c t .result m) ∧
      HistoryCompiledRows.Records id (D.assemble forest v).compile (t).stream out := by
  rw [D.assemble_compile forest v]
  apply X.join_run (fun i=>(D.tapeFactor forest v i).compile) (D.tapePin forest v) id q mapping
    (t).stream head source resident endHeader
  right
  change (t).stream+4*(D.assemble forest v).compile.cells≤_
  rwa [Diagonal.HistoryContraction.Tree.compiled_rows]


end StageRun

end Execution


end
end ThreeFlat.RAM.HistoryStageBody

namespace ThreeFlat.RAM.HistoryStageBody.Physical

open Computability.VPVNP.BurstRAM PhysicalPinsExpr PhysicalProcedure Diagonal.TickWorkspace
open scoped Fin.CommRing
noncomputable section

/-- One member of the finite set of actual degree/grid types. The immutable
addresses point into the common S38 advice bank installed by navigation. -/
structure Family where
  mode : HistoryGatherBody.Geometry
  oldPorts : ℕ
  childBound : ℕ
  motifs : ℕ
  parties : ℕ
  demands : ℕ
  supplies : ℕ
  digits : ℕ
  kinds : ℕ
  ports : ℕ

structure Archive where
  lut : ℕ
  lutStride : ℕ
  pages : ℕ
  pageStride : ℕ
  counts : ℕ
  histStride : ℕ

def nodes (u : ℕ) : HistoryNodePorts.Layout :=
  ⟨base u 18,base u 44,base u 13,base u 18+3*volume u⟩

def layout (u : ℕ) (A : Archive) (f : Family) : HistoryGatherBody.Layout :=
  let B : HistoryPartyBatch.Layout :=
    ⟨base u 18,base u 44,volume u,base u 12,f.motifs,f.parties,0,0,f.kinds,
      seed u,base u 14+2*volume u,base u 15,base u 16,base u 18+5*volume u,
      A.lut,A.lutStride,A.pages,A.pageStride,A.counts⟩
  ⟨B,nodes u,f.mode,A.histStride,base u 17,f.demands,f.supplies,f.digits,f.ports,base u 18+4*volume u⟩

def kind : HistoryGatherBody.Geometry→ℕ | .shrink _ => 1 | .refresh .. => 2

def enabled (u : ℕ) (f : Family) : Formula 1 :=
  let site := HistoryNodePorts.node (nodes u)
  let flags := HistoryNodePorts.kernel (nodes u)
  let stage := Formula.load flags
  eqz (.load site) (.lit (kind f.mode))
    (eqz (.load (add stage (.lit 48))) (.lit f.oldPorts) (.lit 1) (.lit 0)) (.lit 0)

private def enabledAt (cursor nodes code oldPorts : ℕ) : Formula 1 :=
  let atNode := add (.lit nodes) (mul (.lit 8) (.cut (.load (.lit cursor)) (.lit 1)))
  let atStage := Formula.load (.load (add atNode (.lit 5)))
  eqz (.load atNode) (.lit code)
    (eqz (.load (add atStage (.lit 48))) (.lit oldPorts) (.lit 1) (.lit 0)) (.lit 0)

private theorem enabled_eq (u : ℕ) (f : Family) :
    enabled u f = enabledAt (base u 18) (base u 44) (kind f.mode) f.oldPorts := rfl

theorem enabled_value (u W : ℕ) (f : Family) (pub : Param→ℕ) (m : ℕ→ℕ) (x : Fin 1→ℕ) :
    let n := base u 44+8*(m (base u 18)-1)
    (enabled u f).natural W pub m x=if m n=kind f.mode ∧ m (m (m (n+5))+48)=f.oldPorts then 1 else 0 := by
  let n := base u 44+8*(m (base u 18)-1)
  change (enabled u f).natural W pub m x =
    if m n=kind f.mode ∧ m (m (m (n+5))+48)=f.oldPorts then 1 else 0
  rw [enabled_eq]
  change (if decide (m n=kind f.mode) then
    (if decide (m (m (m (n+5))+48)=f.oldPorts) then 1 else 0) else 0) = _
  by_cases tagged : m n=kind f.mode <;> simp [tagged]

def body (W u : ℕ) (archive : Archive) (shape : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word W) (families : List Family) : Procedure W :=
  families.foldr (fun f next => ifValue (enabled u f) (HistoryStageBody.procedure (layout u archive f) f.childBound W) next)
    (HistoryInitialSeed.procedure W (initial u shape) pub)

/-- The guard physically reads the retained schedule and reverse-owner
directories. All selected roots and ancestors execute the genuine native
leaf or stage procedure and publish their common cache in S13. -/
def selected (W u : ℕ) (archive : Archive) (shape : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word W) (families : List Family) : Procedure W :=
  HistoryNodeDirectory.Selected.procedure (ownerData W u) (body W u archive shape pub families)

end
end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.RAM.HistoryStageBody.Physical

open Computability.VPVNP.BurstRAM PhysicalPinsExpr PhysicalProcedure Diagonal.TickWorkspace
open scoped Fin.CommRing
open private rd l from OAI.ThreeFlat.RAM.HistoryNodePorts

variable {W : ℕ}

def nodeAddress (u : ℕ) (m : Memory W) := base u 44+8*((m (base u 18)).val-1)

/-- The node's kernel pointer leads to the current stage information. Column 48 contains
the old port count that selects a concrete member of the finite family. -/
def stageAddress (u : ℕ) (m : Memory W) := (m (m (nodeAddress u m+5)).val).val

def matchesFamily (u : ℕ) (m : Memory W) (f : Family) : Bool :=
  decide ((m (nodeAddress u m)).val=kind f.mode ∧ (m (stageAddress u m+48)).val=f.oldPorts)

theorem ifWord_enabled (u : ℕ) (m : Memory W) (f : Family)
    (wide : 2<2^W) (cursor : base u 18<2^W) (node : nodeAddress u m+5<2^W)
    (stage : (m (nodeAddress u m)).val=kind f.mode → stageAddress u m+48<2^W ∧ f.oldPorts<2^W) :
    ifWord (enabled u f) m = if matchesFamily u m f then 1 else 0 := by
  let raw := fun a => (m a).val
  let z := fun _ : Fin 1 => (0:ℕ)
  have kind_le (g : HistoryGatherBody.Geometry) : kind g ≤ 2 := by
    cases g <;> simp only [kind] <;> decide
  have fk := (kind_le f.mode).trans_lt wide
  have nodeEq : base u 44+8*((m (base u 18)).val-1)=nodeAddress u m := rfl
  have stageEq : (m (m (nodeAddress u m+5)).val).val=stageAddress u m := rfl
  have cv := (m (base u 18)).isLt
  have nk := (m (nodeAddress u m)).isLt
  have kp := (m (nodeAddress u m+5)).isLt
  have wp := (m (stageAddress u m+48)).isLt
  have fit : (enabled u f).Fits W (fun _=>0) raw z := by
    rw [enabled_eq]
    by_cases same : (m (nodeAddress u m)).val=kind f.mode
    · obtain ⟨sf,old⟩ := stage same
      have nn : nodeAddress u m < 2^W := (Nat.le_add_right ..).trans_lt node
      have one : 1 < 2^W := by omega
      simp only [enabledAt,eqz,add,mul,Formula.Fits,Formula.natural,opFits,natOp,natTest,raw,
        nodeEq,stageEq,decide_eq_true_eq,ite_eq_left same,ite_self,cursor,cv,one,nn,node,kp,nk,fk,sf,old,wp,
        and_true]
    · simp only [enabledAt,eqz,add,mul,Formula.Fits,Formula.natural,opFits,natOp,natTest,raw,
        nodeEq,stageEq,decide_eq_true_eq,ite_eq_right same,true_and,and_true]
      omega
  have h := (enabled u f).value_eq_natural (fun _=>0) raw z fit
  rw [enabled_value] at h
  by_cases yes : (m (nodeAddress u m)).val=kind f.mode ∧ (m (stageAddress u m+48)).val=f.oldPorts <;>
    simpa [ifWord,matchesFamily,raw,z,nodeEq,stageEq,yes] using h

/-- Inspect the guards in order and pay for precisely the procedures and tests that execute. -/
def bodyCost (u : ℕ) (m : Memory W) (initialCost : ℕ) (arm : Family → ℕ) : List Family → ℕ
  | [] => initialCost
  | f::fs => 2*(enabled u f).work+4+(if matchesFamily u m f then arm f else bodyCost u m initialCost arm fs)

/-- The caller provides the real initial-node procedure or the uniquely selected occurrence
of a fixed stage arm. The guard sequence can start from arbitrary register and private state. -/
theorem body_spec (W u : ℕ) (archive : Archive) (shape : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word W) (roster : List Family) (m : Memory W)
    (post : Memory W→Memory W→Prop) (initialCost : ℕ) (arm : Family→ℕ)
    (wide : 2<2^W) (cursor : base u 18<2^W) (node : nodeAddress u m+5<2^W)
    (stage : ∀ f∈roster,(m (nodeAddress u m)).val=kind f.mode →
      stageAddress u m+48<2^W ∧ f.oldPorts<2^W)
    (matched : ∀ f,roster.find? (matchesFamily u m)=some f →
      (HistoryStageBody.procedure (layout u archive f) f.childBound W).Spec (·=m) post (arm f))
    (leaf : roster.find? (matchesFamily u m)=none →
      (HistoryInitialSeed.procedure W (initial u shape) pub).Spec (·=m) post initialCost) :
    (body W u archive shape pub roster).Spec (·=m) post (bodyCost u m initialCost arm roster) := by
  induction roster with
  | nil => exact leaf rfl
  | cons f fs ih =>
    have gate := ifWord_enabled u m f wide cursor node (stage f (List.mem_cons_self ..))
    have one : (1:Word W)≠0 := by
      intro eq
      have t := congrArg Fin.val eq
      have h : (1:Word W).val=1 := Fin.val_cast_of_lt (by omega : 1<2^W)
      simp only [h,Fin.val_zero] at t
      omega
    change (ifValue (enabled u f) _ (body W u archive shape pub fs)).Spec _ _ _
    cases h : matchesFamily u m f with
    | true =>
      simp [h] at gate
      refine ifValue_spec _ _ _ _ post (fun _=>arm f) _ (fun _ _=>by simp [bodyCost,h]) ?_ ?_
      · rintro _ rfl _
        exact matched f (by simp [h])
      · rintro _ rfl hz
        exact (one (gate.symm.trans hz)).elim
    | false =>
      simp [h] at gate
      refine ifValue_spec _ _ _ _ post (fun _=>bodyCost u m initialCost arm fs) _
        (fun _ _=>by simp [bodyCost,h]) ?_ ?_
      · rintro _ rfl nz
        exact (nz gate).elim
      · rintro _ rfl _
        apply ih (fun g hg=>stage g (List.mem_cons_of_mem _ hg))
        · intro g hg
          apply matched g
          simpa only [List.find?_cons,h] using hg
        · intro none
          apply leaf
          simpa only [List.find?_cons,h] using none


end ThreeFlat.RAM.HistoryStageBody.Physical


namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal.TickWorkspace HistoryScratch
variable {u node x M P : ℕ}
local notation "V" => volume u

/-- Every active party and motif writes its bounded local result inside its own S12 node page. -/
theorem OutsideNode.private_range (safe : OutsideNode u node x) (capacity : (M+2)*(P+2)*8*32≤V)
    (loc : Local) (valid : loc.Valid M P) (len : ℕ) (size : len≤V) :
    let p:=atWord (base u 12) V M P node loc 0
    x<p ∨ p+len≤x := by
  have slot:=(sector_lt valid).trans_le capacity
  have block:=Nat.mul_le_mul_right V slot
  rw [Nat.succ_mul] at block
  apply safe.arena_range
  · simp only [atWord,Nat.add_zero,Nat.add_mul,pow_two,←Nat.mul_assoc]
    omega
  · simp only [atWord,Nat.add_zero,Nat.add_mul,Nat.one_mul,pow_two,←Nat.mul_assoc]
    omega


end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
