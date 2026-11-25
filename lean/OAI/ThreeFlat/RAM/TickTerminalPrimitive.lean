import OAI.ThreeFlat.RAM.HistoryCommandParameter
import OAI.ThreeFlat.RAM.HistoryJoinScan
import OAI.ThreeFlat.RAM.HistoryReadyTape
import OAI.ThreeFlat.RAM.HistoryTerminalTape

namespace OAI
/-! # Three fixed terminal opcodes, addressing genuine endpoint, wire, and metadata words -/

namespace ThreeFlat.RAM.TickTerminalPrimitive

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr HistoryCommandParameter
open scoped Fin.CommRing

variable {w : ℕ}
private abbrev E (w : ℕ) := Term w 1 1
private def cmd : E w := Term.load (.parameter 0)
private def rd (a : E w) (j : ℕ) : E w := Term.load (.binary .add a (.literal (j:Word w)))
private def source : E w :=
  let pointer : E w := cmd.load
  .binary .add (rd pointer 2) (.binary .sub (.result 0) (rd pointer 0))

def expression (w : ℕ) : E w :=
  let tag : E w := rd cmd 2
  let join : E w := replace (fun _ : Fin 1 => (Term.parameter (0 : Fin 1)).load) (HistoryJoinScan.term (0 : Fin 1))
  .select .eq tag (.literal 1) join (.select .eq tag (.literal 10) source.load source)

def pointer (ctrl : Word w) (m : Memory w) := m (m ctrl.val).val
def tag (ctrl : Word w) (m : Memory w) := m (m ctrl.val + 2).val
def address (ctrl : Word w) (m : Memory w) (a : Word w) :=
  let p := pointer ctrl m
  m (p+2).val + (a-m (p+0).val)

theorem eval (data : Fin 1→Word w) (m : Memory w) (a : Word w) :
    (expression w).eval data m (fun _ => a) =
      if tag (data 0) m=1 then HistoryJoinScan.readWord (HistoryJoinScan.fetch (pointer (data 0) m) m) m a
      else if tag (data 0) m=10 then m (address (data 0) m a).val else address (data 0) m a := by
  simp only [expression,Term.eval_select,eval_replace,HistoryJoinScan.eval_term,Term.eval,rd,cmd,source,
    Term.eval_load,Term.eval_parameter,Term.eval_binary,Term.eval_literal,Comparison.test,BinaryOp.eval,
    beq_iff_eq,tag,pointer,address]
  all_goals rfl

open HistoryTerminalTape HistoryReadyTape DescriptorScan HistoryJoinController

/-- Every half-port contributes one consecutive run of wire addresses. -/
def pinJob (T : Root) (raw : ℕ → ℕ) (initial : Memory w) (i : ℕ) : Job w :=
  if i=0 then
    ⟨T.map,T.ext,fun a => initial (T.endpoints+(a-T.map))⟩
  else
    ⟨interval T raw (i-1),(half T raw (i-1)).width,
     fun a => ((HistoryTerminalTape.source T raw (i-1)+(a-interval T raw (i-1)) : ℕ) : Word w)⟩

def pinJobs (T : Root) (raw : ℕ → ℕ) (initial : Memory w) (i n : ℕ) :=
  (List.range' i n).map (pinJob T raw initial)

def joinArgument (T : Root) := T.arguments+7*(T.halves+1)

def joinedJob (T : Root) (pins : Memory w) : Job w :=
  ⟨T.meta,4*T.rows,fun a => HistoryJoinScan.readWord (HistoryJoinScan.fetch
    (joinArgument T : Word w) pins) pins (a : Word w)⟩

def jobs (T : Root) (raw : ℕ → ℕ) (ctrl : Word w) (initial : Memory w) : List (Job w) :=
  let xs := pinJobs T raw initial 0 (T.halves+1)
  xs ++ [joinedJob T (after ctrl xs initial)]

/-- Physical contents of both seven-word banks before the sweep. -/
structure Tables (T : Root) (raw : ℕ → ℕ) (commands : ℕ) (m : Memory w) : Prop where
  command : ∀ i, i<T.halves+2 → ∀ j : Fin 7,
    m (commands+7*i+j.val)=(HistoryTerminalTape.command T raw i j : Word w)
  arguments : ∀ i, i<T.halves+2 → ∀ j : Fin 7,
    m (T.arguments+7*i+j.val)=(HistoryTerminalTape.arguments T raw i j : Word w)

def Outside (lo hi a : ℕ) := a<lo ∨ hi≤a

/-- The control word and both immutable tapes are outside the rows a job fills. -/
structure Protected (T : Root) (commands : ℕ) (ctrl : Word w) (lo hi : ℕ) : Prop where
  cursorApart : hi≤ctrl.val ∨ ctrl.val+2≤lo
  commandApart : hi≤commands ∨ commands+7*(T.halves+2)≤lo
  argumentApart : hi≤T.arguments ∨ T.arguments+7*(T.halves+2)≤lo

private theorem Protected.cursor {T : Root} {commands lo hi : ℕ} {ctrl : Word w}
    (h : Protected T commands ctrl lo hi) : Outside lo hi ctrl.val := by
  have := h.cursorApart
  unfold Outside
  omega

private theorem Protected.command {T : Root} {commands lo hi : ℕ} {ctrl : Word w}
    (h : Protected T commands ctrl lo hi) (z : ℕ) (low : commands≤z)
    (high : z<commands+7*(T.halves+2)) : Outside lo hi z := by
  have := h.commandApart
  unfold Outside
  omega

private theorem Protected.arguments {T : Root} {commands lo hi : ℕ} {ctrl : Word w}
    (h : Protected T commands ctrl lo hi) (z : ℕ) (low : T.arguments≤z)
    (high : z<T.arguments+7*(T.halves+2)) : Outside lo hi z := by
  have := h.argumentApart
  unfold Outside
  omega

private theorem protectedTables {T : Root} {raw : ℕ → ℕ} {commands lo hi : ℕ}
    {ctrl : Word w} {m mem : Memory w} (stored : Tables T raw commands m)
    (sep : Protected T commands ctrl lo hi) (frame : agreesOutside lo hi mem m) :
    Tables T raw commands mem := by
  constructor
  · intro i h j
    have hj := j.isLt
    rw [frame _ (sep.command _ (by omega) (by omega)),stored.command i h j]
  · intro i h j
    have hj := j.isLt
    rw [frame _ (sep.arguments _ (by omega) (by omega)),stored.arguments i h j]

private theorem addressVal (n j : ℕ) (fit : n+j<2^w) :
    ((n : Word w)+(j : Word w)).val=n+j := by rw [←Nat.cast_add,Fin.val_cast_of_lt fit]

private theorem decoder (T : Root) (raw : ℕ → ℕ) (commands i : ℕ) (ctrl : Word w)
    (m : Memory w) (hi : i<T.halves+2) (cursor : m ctrl.val=((commands+7*i : ℕ) : Word w))
    (table : Tables T raw commands m) (cmdFit : commands+7*(T.halves+2)≤2^w)
    (argFit : T.arguments+7*(T.halves+2)≤2^w) :
    pointer ctrl m=((T.arguments+7*i : ℕ) : Word w) ∧
    tag ctrl m=(HistoryTerminalTape.command T raw i 2 : Word w) ∧
    ∀ j : Fin 7, m (pointer ctrl m+(j.val : Word w)).val=
      (HistoryTerminalTape.arguments T raw i j : Word w) := by
  have z : HistoryTerminalTape.command T raw i 0 = T.arguments+7*i := by
    by_cases h : i=0 <;> by_cases k : i≤T.halves <;> simp [HistoryTerminalTape.command,h,k]
  have ptr : pointer ctrl m = ((T.arguments+7*i : ℕ) : Word w) := by
    rw [pointer,cursor,Fin.val_cast_of_lt (by omega),←z]
    simpa using table.command i hi 0
  refine ⟨ptr,?_,?_⟩
  · rw [tag,cursor,show (2:Word w)=((2:ℕ):Word w) by norm_num,addressVal _ _ (by omega)]
    exact table.command i hi 2
  · intro j
    have hj := j.isLt
    rw [ptr,addressVal _ _ (by omega)]
    exact table.arguments i hi j

private theorem shifted (start src : ℕ) (a : Word w) (low : start≤a.val) :
    (src : Word w)+(a-(start : Word w))=((src+(a.val-start) : ℕ) : Word w) := by
  rw [Nat.cast_add,Nat.cast_sub low,Fin.cast_val_eq_self]

private theorem tag_ne {a b : ℕ} (ha : a<2^w) (hb : b<2^w) (h : a≠b) :
    (a : Word w)≠(b : Word w) := by
  intro e
  have v := congrArg Fin.val e
  rw [Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb] at v
  exact h v

private theorem read_pin (T : Root) (raw : ℕ → ℕ) (commands i : ℕ) (initial m : Memory w)
    (ctrl : Word w) (hi : i<T.halves+1) (cursor : m ctrl.val=((commands+7*i : ℕ) : Word w))
    (table : Tables T raw commands m) (cmdFit : commands+7*(T.halves+2)≤2^w)
    (argFit : T.arguments+7*(T.halves+2)≤2^w) (wide : 11<2^w)
    (begin : i=0 → m=initial) (endFit : T.endpoints+T.ext≤2^w)
    (endApart : ∀ z,T.endpoints≤z → z<T.endpoints+T.ext → Outside T.map (T.map+T.ext) z)
    (sep : Protected T commands ctrl (pinJob T raw initial i).start (pinJob T raw initial i).finish) :
    let x := pinJob T raw initial i
    ∀ (a : Word w) (mem : Memory w), x.start≤a.val → a.val<x.finish →
      agreesOutside x.start x.finish mem m → (expression w).eval (fun _ => ctrl) mem (fun _ => a)=x.word a.val := by
  intro x a mem lo upper frame
  have d := decoder T raw commands i ctrl mem (by omega)
    ((frame _ sep.cursor).trans cursor) (protectedTables table sep frame) cmdFit argFit
  have ad : address ctrl mem a =
      (HistoryTerminalTape.arguments T raw i 2 : Word w)+(a-(HistoryTerminalTape.arguments T raw i 0 : Word w)) := by
    change mem (pointer ctrl mem+2).val+(a-mem (pointer ctrl mem+0).val)=_
    have z := d.2.2 0
    have t := d.2.2 2
    change mem (pointer ctrl mem+0).val=_ at z
    change mem (pointer ctrl mem+2).val=_ at t
    rw [z,t]
  rw [eval,d.2.1]
  by_cases zero : i=0
  · subst i
    have hx : x.start=T.map := by simp [x,pinJob]
    have hy : x.finish=T.map+T.ext := by simp [x,pinJob,Job.finish]
    rw [hx] at lo
    rw [hy] at upper
    have eq10 : (10:Word w)≠1 := tag_ne (a:=10) (b:=1) (by omega) (by omega) (by decide)
    have loc : address ctrl mem a=((T.endpoints+(a.val-T.map) : ℕ) : Word w) := by
      simpa [HistoryTerminalTape.arguments,shifted T.map T.endpoints a lo] using ad
    change _=initial (T.endpoints+(a.val-T.map))
    have op : HistoryTerminalTape.command T raw 0 2=10 := rfl
    rw [op,show ((10:ℕ):Word w)=10 by norm_num,ite_eq_right eq10,ite_eq_left rfl]
    rw [loc,Fin.val_cast_of_lt (by omega)]
    exact (frame _ (by rw [hx,hy]; apply endApart <;> omega)).trans (congrFun (begin rfl) _)
  · have within : i≤T.halves := by omega
    have hx : x.start=interval T raw (i-1) := by simp [x,pinJob,zero]
    rw [hx] at lo
    have n1 : (11:Word w)≠1 := tag_ne (a:=11) (b:=1) wide (by omega) (by decide)
    have n10 : (11:Word w)≠10 := tag_ne (a:=11) (b:=10) wide (by omega) (by decide)
    have ad' : address ctrl mem a = ((HistoryTerminalTape.source T raw (i-1) +
        (a.val-interval T raw (i-1)) : ℕ) : Word w) := by
      simpa [HistoryTerminalTape.arguments,zero,within,shifted _ _ a lo] using ad
    simpa [HistoryTerminalTape.command,zero,within,n1,n10,x,pinJob] using ad'

private theorem read_join (T : Root) (raw : ℕ → ℕ) (commands : ℕ) (ctrl : Word w) (m : Memory w)
    (cursor : m ctrl.val=((commands+7*(T.halves+1) : ℕ) : Word w))
    (table : Tables T raw commands m) (cmdFit : commands+7*(T.halves+2)≤2^w)
    (argFit : T.arguments+7*(T.halves+2)≤2^w)
    (sep : Protected T commands ctrl T.meta (T.meta+4*T.rows))
    (inputs : HistoryJoinScan.Separate (joinArgument T : Word w) T.meta (T.meta+4*T.rows) m) :
    readJobs (expression w) (fun _ => ctrl) ctrl [joinedJob T m] m := by
  refine ⟨?_,trivial⟩
  intro a mem lo hi frame
  have d := decoder T raw commands (T.halves+1) ctrl mem (by omega)
    ((frame _ sep.cursor).trans cursor) (protectedTables table sep frame) cmdFit argFit
  have jt : tag ctrl mem=1 := by simpa [HistoryTerminalTape.command] using d.2.1
  have ptr : pointer ctrl mem = (joinArgument T : Word w) := d.1
  rw [eval,jt,ite_eq_left rfl,ptr]
  change _=HistoryJoinScan.readWord (HistoryJoinScan.fetch _ m) m (a.val : Word w)
  rw [Fin.cast_val_eq_self]
  apply HistoryJoinScan.readWord_frame
  · intro j; exact frame _ (inputs.control j)
  · exact frame _ (inputs.source a lo hi)
  · dsimp only
    intro low high
    exact frame _ (inputs.pins a lo hi low high)

private theorem pin_prefix (T : Root) (raw : ℕ → ℕ) (commands : ℕ) (initial : Memory w)
    (ctrl : Word w) (cmdFit : commands+7*(T.halves+2)≤2^w)
    (argFit : T.arguments+7*(T.halves+2)≤2^w) (wide : 11<2^w)
    (outsideC : Outside commands (commands+7*(T.halves+2)) ctrl.val)
    (outsideA : Outside T.arguments (T.arguments+7*(T.halves+2)) ctrl.val)
    (endFit : T.endpoints+T.ext≤2^w)
    (endApart : ∀ z,T.endpoints≤z → z<T.endpoints+T.ext → Outside T.map (T.map+T.ext) z)
    (apart : ∀ i, i<T.halves+1 → Protected T commands ctrl (pinJob T raw initial i).start (pinJob T raw initial i).finish)
    (i n : ℕ) (hi : i+n≤T.halves+1) (m : Memory w) (begin : i=0 → m=initial)
    (cursor : m ctrl.val=((commands+7*i : ℕ):Word w)) (table : Tables T raw commands m) :
    let xs := pinJobs T raw initial i n
    readJobs (expression w) (fun _ => ctrl) ctrl xs m ∧
      Tables T raw commands (after ctrl xs m) ∧
      after ctrl xs m ctrl.val=((commands+7*(i+n) : ℕ):Word w) := by
  induction n generalizing i m with
  | zero => simpa [pinJobs,List.range',readJobs,HistoryReadyTape.after] using And.intro table cursor
  | succ n ih =>
    let x := pinJob T raw initial i
    let filled := fillSegment x.start x.count x.word m
    let next := bumpMemory ctrl filled
    have can : i<T.halves+1 := by omega
    have sep := apart i can
    have untouched : agreesOutside x.start x.finish filled m := by
      intro z hz
      simp only [filled,fillSegment]
      exact ite_eq_right (by change ¬(x.start≤z ∧ z<x.finish); omega)
    have written : Tables T raw commands filled := protectedTables table sep untouched
    have still : Tables T raw commands next := by
      have same (z : ℕ) (h : z≠ctrl.val) : next z=filled z := by
        simp [next,bumpMemory,writeMemory,h]
      constructor
      · intro j hj q
        have hq := q.isLt
        rw [same _ (by unfold Outside at outsideC; omega)]
        exact written.command j hj q
      · intro j hj q
        have hq := q.isLt
        rw [same _ (by unfold Outside at outsideA; omega)]
        exact written.arguments j hj q
    have nextC : next ctrl.val=((commands+7*(i+1):ℕ):Word w) := by
      simp only [next,bumpMemory,writeMemory,↓reduceIte,untouched _ sep.cursor,cursor]
      push_cast
      ring
    obtain ⟨tailReads,tailTable,last⟩ := ih (i+1) (by omega) next (by omega) nextC still
    have head := read_pin T raw commands i initial m ctrl can cursor table cmdFit argFit wide
      begin endFit endApart sep
    have unroll : pinJobs T raw initial i (n+1)=x::pinJobs T raw initial (i+1) n := by
      simp [pinJobs,List.range'_succ,x]
    simp only [unroll,readJobs,HistoryReadyTape.after]
    exact ⟨⟨head,tailReads⟩,tailTable,by simpa only [Nat.add_assoc,Nat.add_comm 1 n] using last⟩

private theorem readJobs_append {k : ℕ} (e : Term w k 1) (pub : Fin k → Word w) (ctrl : Word w)
    (xs ys : List (Job w)) (m : Memory w) :
    readJobs e pub ctrl (xs++ys) m ↔ readJobs e pub ctrl xs m ∧ readJobs e pub ctrl ys (after ctrl xs m) := by
  induction xs generalizing m with
  | nil => simp [readJobs,HistoryReadyTape.after]
  | cons x xs ih => simp only [List.cons_append,readJobs,HistoryReadyTape.after,ih,and_assoc]

/-- The three opcodes execute on the generated command and argument banks, including the pin map
produced by all preceding endpoint and wire writes when the join starts. -/
theorem reads (T : Root) (raw : ℕ → ℕ) (commands : ℕ) (ctrl : Word w) (initial : Memory w)
    (cursor : initial ctrl.val=(commands : Word w)) (table : Tables T raw commands initial)
    (cmdFit : commands+7*(T.halves+2)≤2^w) (argFit : T.arguments+7*(T.halves+2)≤2^w)
    (wide : 11<2^w) (outsideC : Outside commands (commands+7*(T.halves+2)) ctrl.val)
    (outsideA : Outside T.arguments (T.arguments+7*(T.halves+2)) ctrl.val)
    (endFit : T.endpoints+T.ext≤2^w)
    (endApart : ∀ z,T.endpoints≤z → z<T.endpoints+T.ext → Outside T.map (T.map+T.ext) z)
    (pinsApart : ∀ i, i<T.halves+1 → Protected T commands ctrl (pinJob T raw initial i).start
      (pinJob T raw initial i).finish)
    (joinApart : Protected T commands ctrl T.meta (T.meta+4*T.rows))
    (joinSources : HistoryJoinScan.Separate (joinArgument T : Word w) T.meta (T.meta+4*T.rows)
      (after ctrl (pinJobs T raw initial 0 (T.halves+1)) initial)) :
    readJobs (expression w) (fun _ => ctrl) ctrl (jobs T raw ctrl initial) initial := by
  obtain ⟨hp,ht,hc⟩ := pin_prefix T raw commands initial ctrl cmdFit argFit wide outsideC outsideA
    endFit endApart pinsApart 0 (T.halves+1) (by omega) initial (fun _ => rfl) (by simpa using cursor) table
  apply (readJobs_append ..).mpr
  exact ⟨hp,read_join T raw commands ctrl _ (by simpa using hc) ht cmdFit argFit joinApart joinSources⟩

@[simp] theorem jobs_length (T : Root) (raw : ℕ → ℕ) (ctrl : Word w) (m : Memory w) :
    (jobs T raw ctrl m).length=T.halves+2 := by simp [jobs,pinJobs,Nat.add_assoc]

private theorem job_at (T : Root) (raw : ℕ → ℕ) (ctrl : Word w) (m : Memory w)
    (i : Fin (jobs T raw ctrl m).length) :
    (jobs T raw ctrl m).get i = if i.val<T.halves+1 then pinJob T raw m i.val
      else joinedJob T (after ctrl (pinJobs T raw m 0 (T.halves+1)) m) := by
  let xs := pinJobs T raw m 0 (T.halves+1)
  let lastJob := joinedJob T (after ctrl xs m)
  have len : xs.length=T.halves+1 := by simp [xs,pinJobs]
  have lookup (n : ℕ) (hn : n<T.halves+2) : (jobs T raw ctrl m)[n]? =
      some (if n<T.halves+1 then pinJob T raw m n else lastJob) := by
    change (xs++[lastJob])[n]? = _
    by_cases h : n<T.halves+1
    · rw [ite_eq_left h,List.getElem?_append_left (show n<xs.length by omega)]
      simp [xs,pinJobs,List.getElem?_map,List.getElem?_range' h]
    · rw [ite_eq_right h,List.getElem?_append_right (show xs.length≤n by omega),
        show n-xs.length=0 by omega]
      rfl
  have element := lookup i.val (i.isLt.trans_le (jobs_length T raw ctrl m).le)
  rw [List.getElem?_eq_getElem i.isLt] at element
  exact Option.some.inj element

theorem loaded (T : Root) (raw : ℕ → ℕ) (commands : ℕ) (ctrl : Word w) (m : Memory w)
    (table : Tables T raw commands m) : Loaded commands (jobs T raw ctrl m) m := by
  intro i
  have hi : i.val<T.halves+2 := i.isLt.trans_le (jobs_length T raw ctrl m).le
  have first : m (commands+7*i.val+1) =
      (HistoryTerminalTape.command T raw i.val ⟨1,by decide⟩ : Word w) :=
    table.command i.val hi ⟨1,by decide⟩
  have last : m (commands+7*i.val+6) =
      (HistoryTerminalTape.command T raw i.val ⟨6,by decide⟩ : Word w) :=
    table.command i.val hi ⟨6,by decide⟩
  rw [first,last,job_at]
  by_cases z : i.val=0 <;> by_cases p : i.val≤T.halves <;>
    simp [HistoryTerminalTape.command,z,p,pinJob,joinedJob,Job.finish,
      show (i.val<T.halves+1) ↔ i.val≤T.halves by omega]

/-- The number of words produced by all endpoint, wire, and record commands. -/
def words (T : Root) (raw : ℕ → ℕ) : ℕ :=
  ((List.range' 0 (T.halves+1)).map (fun i =>
    if i=0 then T.ext else (half T raw (i-1)).width)).sum+4*T.rows

def cycles (w : ℕ) (T : Root) (raw : ℕ → ℕ) : ℕ :=
  6+19*(T.halves+2)+words T raw*(2*(expression w).binds+4)

private theorem cost_jobs (b : ℕ) (xs : List (Job w)) :
    cost b xs=6+19*xs.length+(xs.map Job.count).sum*(2*b+4) := by
  induction xs with
  | nil => simp [cost]
  | cons x xs ih => simp only [cost,List.length_cons,List.map_cons,List.sum_cons,ih]; ring

theorem jobs_cost (T : Root) (raw : ℕ → ℕ) (ctrl : Word w) (m : Memory w) :
    cost (expression w).binds (jobs T raw ctrl m)=cycles w T raw := by
  have counts (i : ℕ) : (pinJob T raw m i).count =
      if i=0 then T.ext else (half T raw (i-1)).width := by
    by_cases h : i=0 <;> simp [pinJob,h]
  rw [cost_jobs,jobs_length]
  simp [cycles,words,jobs,pinJobs,joinedJob,List.map_map,Function.comp_def,counts]

/-- A terminal root executes the installed bank on its initial memory and returns the full map and
record stream. Each actual half contributes only its width to the per-word term. -/
theorem execute_spec (T : Root) (raw : ℕ → ℕ) (commands : ℕ) (ctrl : Word w) (initial : Memory w)
    (cursor : initial ctrl.val=(commands : Word w))
    (stop : initial (ctrl+1).val=((commands+7*(T.halves+2) : ℕ):Word w))
    (table : Tables T raw commands initial)
    (earlier : ctrl.val+2≤commands) (cmdFit : commands+7*(T.halves+2)<2^w)
    (argFit : T.arguments+7*(T.halves+2)≤2^w) (wide : 11<2^w)
    (outsideA : Outside T.arguments (T.arguments+7*(T.halves+2)) ctrl.val)
    (endFit : T.endpoints+T.ext≤2^w)
    (endApart : ∀ z,T.endpoints≤z → z<T.endpoints+T.ext → Outside T.map (T.map+T.ext) z)
    (pinsApart : ∀ i, i<T.halves+1 → Protected T commands ctrl (pinJob T raw initial i).start
      (pinJob T raw initial i).finish)
    (pinsFit : ∀ i, i<T.halves+1 → (pinJob T raw initial i).finish<2^w)
    (joinApart : Protected T commands ctrl T.meta (T.meta+4*T.rows)) (joinFit : T.meta+4*T.rows<2^w)
    (joinSources : HistoryJoinScan.Separate (joinArgument T : Word w) T.meta (T.meta+4*T.rows)
      (after ctrl (pinJobs T raw initial 0 (T.halves+1)) initial)) :
    (execute (expression w) (Fin.last 0) (fun _ => ctrl)).Spec (fun m => m=initial)
      (fun m o => o=after ctrl (jobs T raw ctrl initial) m) (cycles w T raw) := by
  let xs := jobs T raw ctrl initial
  have len : xs.length=T.halves+2 := jobs_length ..
  have protectedAll (x : Job w) (hx : x∈xs) : Protected T commands ctrl x.start x.finish ∧ x.finish<2^w := by
    obtain ⟨i,h⟩ := List.mem_iff_get.mp hx
    subst x
    rw [show xs.get i = _ from job_at T raw ctrl initial i]
    by_cases h : i.val<T.halves+1
    · rw [ite_eq_left h]; exact ⟨pinsApart _ h,pinsFit _ h⟩
    · rw [ite_eq_right h]; exact ⟨joinApart,joinFit⟩
  rw [←jobs_cost T raw ctrl initial]
  apply HistoryReadyTape.execute_spec (expression w) (Fin.last 0) (fun _ => ctrl)
    (fun m => m=initial) xs commands earlier (by simpa only [len] using cmdFit)
  · exact fun x hx => (protectedAll x hx).1.cursorApart
  · intro x hx
    simpa only [len] using (protectedAll x hx).1.commandApart
  · exact fun x hx => (protectedAll x hx).2
  · intro m hm
    subst m
    refine ⟨cursor,by simpa only [len] using stop,loaded T raw commands ctrl initial table,?_⟩
    exact reads T raw commands ctrl initial cursor table cmdFit.le argFit wide
      (Or.inl (by omega)) outsideA endFit endApart pinsApart joinApart joinSources

end ThreeFlat.RAM.TickTerminalPrimitive

end OAI
