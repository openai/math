import OAI.ThreeFlat.RAM.HistoryTerminalTape
import OAI.ThreeFlat.RAM.HistoryNodeValue
import OAI.ThreeFlat.RAM.HistoryReadyTape
import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.CountedProcedureCost
import OAI.ThreeFlat.RAM.TickTerminalPrimitive

namespace OAI
/-! # Concatenating actual selected roots into the padded interpreter's metadata bank -/

noncomputable section
namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure HistoryTerminalTape
open scoped Fin.CommRing BigOperators

/-- The result bank contains 8 words per chronological node. The selected list holds zero-based
terminal ordinals. The five mutable control words are root index, selected count, cumulative
row count, cumulative hidden count, and remaining roots. -/
structure Arena where
  control : ℕ
  selected : ℕ
  rootHeader : ℕ
  results : ℕ
  wireStart : ℕ
  wirePrefix : ℕ
  physicalPins : ℕ
  metadata : ℕ
  seed : ℕ
  map : ℕ
  commands : ℕ
  arguments : ℕ

def rootId (A : Arena) (m : ℕ→ℕ) :=
  m A.rootHeader + m (A.selected+m A.control)

def terminal (A : Arena) (m : ℕ→ℕ) : Root :=
  let i := rootId A m
  let z := HistoryStageRoot.atResult m (A.results+8*i)
  let h := m (m (A.rootHeader+1)+8*i+6)
  ⟨A.arguments,A.map,z.ext,z.extCount,m h,m (h+1),A.wireStart,A.wirePrefix,z.stream,z.pins,
   A.metadata+4*m (A.control+2),z.rows,A.physicalPins,m (A.control+3)⟩

/-- Prefix counts in S12 remain fixed while the local terminal operand table is consumed. -/
def seedWords (A : Arena) (m : ℕ→ℕ) : Fin 26→ℕ :=
  let t := terminal A m
  let span := 7*(t.halves+2)
  let z := HistoryStageRoot.atResult m (A.results+8*rootId A m)
  Fin.append (Fin.append (![A.seed+1,A.commands,span,A.arguments,span,A.commands,A.commands+span,z.bits] : Fin 8→ℕ) t.words)
    ![m A.control+1,m (A.control+1),m (A.control+2)+z.rows,m (A.control+3)+z.bits]

private abbrev E := Formula 1
private def rd (a : E) (i : ℕ) : E := .load (add a (.lit i))
private def pick (start : ℕ) : List E → E → E
  | [],_ => .lit 0
  | v::vs,i => eqz i (.lit start) v (pick (start+1) vs i)

private def seedList (A : Arena) : List E :=
  let ctrl := Formula.lit A.control
  let idx := add (rd (.lit A.rootHeader) 0) (.load (add (.lit A.selected) (rd ctrl 0)))
  let offset := mul (.lit 8) idx
  let z := add (.lit A.results) offset
  let halfHeader := rd (add (rd (.lit A.rootHeader) 1) offset) 6
  let span := mul (.lit 7) (add (rd halfHeader 0) (.lit 2))
  [.lit (A.seed+1),.lit A.commands,span,.lit A.arguments,span,.lit A.commands,
   add (.lit A.commands) span,rd z 3,.lit A.arguments,.lit A.map,rd z 4,rd z 5,
   rd halfHeader 0,rd halfHeader 1,.lit A.wireStart,.lit A.wirePrefix,rd z 0,rd z 1,
   add (.lit A.metadata) (mul (.lit 4) (rd ctrl 2)),rd z 2,.lit A.physicalPins,rd ctrl 3,
   add (rd ctrl 0) (.lit 1),rd ctrl 1,add (rd ctrl 2) (rd z 2),add (rd ctrl 3) (rd z 3)]

def boot (A : Arena) : E := pick 0 (seedList A) (.cut (.reg 0) (.lit A.seed))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem boot_word (A : Arena) (w : ℕ) (m : ℕ→ℕ) (z : Param→ℕ) (i : Fin 26) :
    (boot A).natural w z m (fun _=>A.seed+i.val)=seedWords A m i := by
  fin_cases i <;> simp [boot,seedList,seedWords,terminal,rootId,HistoryStageRoot.atResult,Root.words,
    pick,rd,eqz,add,mul,Formula.natural,natOp,natTest,Fin.append]
  all_goals first | rfl

/-- The 14-word local header starts at seed+8. For each actual half-port the existing
terminal generator emits a wire run; endpoint copies precede these runs and the weighted
row copy follows them. -/
def generator (W : ℕ) (A : Arena) (cmd : Bool) : Term W 0 1 :=
  let lower := if cmd then A.commands else A.arguments
  let row := Term.binary .sub (.result 0) (.literal (lower:Word W))
  (HeaderScan.closed (HistoryTerminalTape.formula cmd)).instantiate (fun i =>
    if i=0 then .literal ((A.seed+8:ℕ):Word W) else if i=5 then row else .literal 0)

def genInput (A : Arena) (i : ℕ) : Fin 13→ℕ :=
  fun j => if j=0 then A.seed+8 else if j=5 then i else 0

def natMemory {W : ℕ} (m : Memory W) (i : ℕ) := (m i).val

theorem generator_word {W : ℕ} (A : Arena) (cmd : Bool) (m : Memory W) (T : Root)
    (i : ℕ) (j : Fin 7) (a : Word W)
    (address : a.val=(if cmd then A.commands else A.arguments)+7*i+j.val)
    (mounted : ∀ c : Fin 14, natMemory m (A.seed+8+c.val)=T.words c)
    (safe : (HistoryTerminalTape.formula cmd).Fits W (fun _=>0) (natMemory m) (genInput A (7*i+j.val))) :
    (generator W A cmd).eval Fin.elim0 m (fun _=>a) =
      ((if cmd then command T (natMemory m) i j else arguments T (natMemory m) i j : ℕ) : Word W) := by
  let base := if cmd then A.commands else A.arguments
  have rel : a-(base:Word W)=((7*i+j.val:ℕ):Word W) := by
    have bound : base≤a.val := by dsimp [base]; omega
    rw [← Fin.cast_val_eq_self a,← Nat.cast_sub bound]
    apply congrArg (fun z : ℕ => (z : Word W))
    dsimp [base]
    omega
  let vs := genInput A (7*i+j.val)
  have env : (fun z : Fin 13 =>
      (if z=0 then Term.literal ((A.seed+8:ℕ):Word W) else if z=5 then
        Term.binary .sub (Term.result 0) (Term.literal (base:Word W)) else Term.literal 0 : Term W 0 1).eval
        Fin.elim0 m (fun _=>a)) = (fun z => (vs z : Word W)) := by
    funext z
    by_cases h : z=0
    · simp [h,vs,genInput]
    by_cases k : z=5
    · simp [k,vs,genInput,Term.eval_binary,Term.eval,Term.eval_literal,BinaryOp.eval,rel]
    · simp [h,k,vs,genInput]
  have val := Formula.value_eq_natural (HistoryTerminalTape.formula cmd) (fun _=>0) (natMemory m) vs safe
  have output := HistoryTerminalTape.formula_value W (fun _=>0) (natMemory m) vs T i j cmd
    (by simp [vs,genInput]) (by simpa [vs,genInput] using mounted)
  rw [output] at val
  simp only [natMemory,Fin.cast_val_eq_self,Nat.cast_zero] at val
  rw [generator,Term.eval_instantiate,HeaderScan.eval_closed]
  change (HistoryTerminalTape.formula cmd).value (fun _ => 0) m _=_
  rw [env]
  exact val

theorem boot_at {W : ℕ} (A : Arena) (m : Memory W) (a : Word W) (j : Fin 26)
    (whereAt : a.val=A.seed+j.val)
    (safe : (boot A).Fits W (fun _=>0) (natMemory m) (fun _=>a.val)) :
    (HeaderScan.closed (boot A) : Term W 0 1).eval Fin.elim0 m (fun _=>a) =
      (seedWords A (natMemory m) j : Word W) := by
  have out := Formula.value_eq_natural (boot A) (fun _=>0) (natMemory m) (fun _=>a.val) safe
  have addr : (boot A).natural W (fun _=>0) (natMemory m) (fun _=>a.val)=seedWords A (natMemory m) j := by
    rw [whereAt]
    exact boot_word A W (natMemory m) (fun _=>0) j
  rw [addr] at out
  simpa only [HeaderScan.eval_closed,natMemory,Fin.cast_val_eq_self,Nat.cast_zero] using out

/-- Exactly the compact words consulted while creating this root's 26-word startup block. -/
def bootReads (A : Arena) (m : ℕ→ℕ) (a : ℕ) : Prop :=
  let node := rootId A m
  let incident := m (m (A.rootHeader+1)+8*node+6)
  (A.control≤a ∧ a<A.control+4) ∨ (A.rootHeader≤a ∧ a<A.rootHeader+2) ∨
    a=A.selected+m A.control ∨ (A.results+8*node≤a ∧ a<A.results+8*node+6) ∨
    a=m (A.rootHeader+1)+8*node+6 ∨ (incident≤a ∧ a < incident+2)

theorem seedWords_congr (A : Arena) (m m' : ℕ→ℕ)
    (same : ∀ a,bootReads A m a → m' a=m a) : seedWords A m'=seedWords A m := by
  let i := rootId A m
  let out := A.results+8*i
  let src := m (A.rootHeader+1)+8*i+6
  let head := m src
  have ctrl (j : ℕ) (hj : j<4) : m' (A.control+j)=m (A.control+j) := same _ (Or.inl ⟨by omega,by omega⟩)
  have hdr (j : ℕ) (hj : j<2) : m' (A.rootHeader+j)=m (A.rootHeader+j) :=
    same _ (Or.inr (Or.inl ⟨by omega,by omega⟩))
  have sel := same _ (Or.inr (Or.inr (Or.inl rfl)))
  have ctrl0 : m' A.control=m A.control := by simpa using ctrl 0 (by decide)
  have head0 : m' A.rootHeader=m A.rootHeader := by simpa using hdr 0 (by decide)
  have idEq : rootId A m'=i := by simp only [rootId,i,ctrl0,head0,sel]
  have cols (j : ℕ) (hj : j<6) : m' (out+j)=m (out+j) :=
    same _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp [out,i]; omega,by dsimp [out,i]; omega⟩))))
  have out0 : m' out=m out := by simpa using cols 0 (by decide)
  have z : HistoryStageRoot.atResult m' out=HistoryStageRoot.atResult m out := by
    simp only [HistoryStageRoot.atResult,out0,cols 1 (by decide),cols 2 (by decide),cols 3 (by decide),
      cols 4 (by decide),cols 5 (by decide)]
  have ptr : m' src=m src := same _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have half (j : ℕ) (hj : j<2) : m' (head+j)=m (head+j) :=
    same _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by dsimp [head,src,i]; omega,by dsimp [head,src,i]; omega⟩)))))
  have half0 : m' head=m head := by simpa using half 0 (by decide)
  have termEq : terminal A m'=terminal A m := by
    simp only [terminal,idEq,show rootId A m=i from rfl,hdr 1 (by decide),
      show A.results+8*i=out from rfl,z,show m (A.rootHeader+1)+8*i+6=src from rfl,ptr,
      show m src=head from rfl,half0,half 1 (by decide),ctrl 2 (by decide),ctrl 3 (by decide)]
  simp only [seedWords,termEq,idEq,show rootId A m=i from rfl,show A.results+8*i=out from rfl,z,
    ctrl0,ctrl 1 (by decide),ctrl 2 (by decide),ctrl 3 (by decide)]

def seedAt {W : ℕ} (A : Arena) (m : Memory W) (a : ℕ) : Word W :=
  (seedWords A (natMemory m) ⟨(a-A.seed)%26,Nat.mod_lt _ (by decide)⟩ : Word W)

/-- Generates the actual compact startup block, with frame obligations referring only to
the 17 input words in the selected root directory, result array, and cursors. -/
theorem start_spec {W : ℕ} (A : Arena) (m : Memory W)
    (fit : A.seed+26<2^W)
    (away : ∀ a, bootReads A (natMemory m) a → a<A.seed ∨ A.seed+26≤a)
    (bounds : ∀ a : Word W, A.seed≤a.val → a.val<A.seed+26 → ∀ m',
      DescriptorScan.agreesOutside A.seed (A.seed+26) m' m →
      (boot A).Fits W (fun _=>0) (natMemory m') (fun _=>a.val)) :
    (PhysicalInputPhases.writing (HeaderScan.closed (boot A)) Fin.elim0 A.seed 26).Spec
      (fun x=>x=m) (fun _ out=>out=fillSegment A.seed 26 (seedAt A m) m)
      (4+26*(2*(HeaderScan.closed (w:=W) (boot A)).binds+4)) := by
  intro _ _ _ machine
  refine Procedure.Spec.atMemory (A:=PhysicalInputPhases.writing (HeaderScan.closed (boot A)) Fin.elim0 A.seed 26)
    (PhysicalInputPhases.writing_spec (HeaderScan.closed (w:=W) (boot A)) Fin.elim0 A.seed 26 fit
      (fun x=>x=m) (seedAt A m) ?_) m rfl machine
  intro initial same a m' lo hi frame
  subst initial
  let i : Fin 26 := ⟨a.val-A.seed,by omega⟩
  have loc : a.val=A.seed+i.val := by dsimp [i]; omega
  rw [boot_at A m' a i loc (bounds a lo hi m' frame)]
  have equal := seedWords_congr A (natMemory m) (natMemory m') (fun j hj=>congrArg Fin.val (frame j (away j hj)))
  rw [equal]
  have index : (⟨(a.val-A.seed)%26,Nat.mod_lt _ (by decide)⟩ : Fin 26)=i :=
    Fin.ext (Nat.mod_eq_of_lt (show a.val-A.seed<26 from i.isLt))
  simp only [seedAt,index]

def tableBase (A : Arena) (cmd : Bool) := if cmd then A.commands else A.arguments

def tableAt {W : ℕ} (A : Arena) (T : Root) (raw : ℕ→ℕ) (cmd : Bool) (a : ℕ) : Word W :=
  let x := a-tableBase A cmd
  let j : Fin 7 := ⟨x%7,Nat.mod_lt _ (by decide)⟩
  ((if cmd then command T raw (x/7) j else arguments T raw (x/7) j : ℕ) : Word W)

theorem table_at {W : ℕ} (A : Arena) (T : Root) (raw : ℕ→ℕ) (cmd : Bool) (i : ℕ) (j : Fin 7) :
    (tableAt A T raw cmd (tableBase A cmd+7*i+j.val) : Word W)=
      ((if cmd then command T raw i j else arguments T raw i j : ℕ):Word W) := by
  have sub : tableBase A cmd+7*i+j.val-tableBase A cmd = 7*i+j.val := by omega
  have div : (7*i+j.val)/7=i := by
    rw [Nat.add_comm,Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  have rem : (7*i+j.val)%7=j.val := by rw [Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt]
  simp only [tableAt,sub,div,rem]

def rangeReads (T : Root) (raw : ℕ→ℕ) (z : ℕ) : Prop :=
  (T.halfData≤z ∧ z<T.halfData+4*T.halves) ∨
  ∃ i<T.halves,z=T.wirePrefix+(half T raw i).edge

private theorem tables_congr (T : Root) (m m' : ℕ→ℕ) (i : ℕ) (_valid : i<T.halves+2)
    (same : ∀ z, rangeReads T m z → m' z=m z) :
    command T m' i=command T m i ∧ arguments T m' i=arguments T m i := by
  have halfEq (x : ℕ) (hx : x<T.halves) : half T m' x=half T m x := by
    have col (j : ℕ) (hj : j<4) : m' (T.halfData+4*x+j)=m (T.halfData+4*x+j) :=
      same _ (Or.inl ⟨by omega,by omega⟩)
    have first : m' (T.halfData+4*x)=m (T.halfData+4*x) := by simpa using col 0 (by decide)
    simp only [HistoryTerminalTape.half,first,col 1 (by decide),col 2 (by decide),col 3 (by decide)]
  by_cases zero : i=0
  · simp [command,arguments,zero]
  by_cases middle : i≤T.halves
  · have inBounds : i-1<T.halves := by omega
    have wire := same _ (Or.inr ⟨i-1,inBounds,rfl⟩)
    simp [command,arguments,zero,middle,HistoryTerminalTape.source,interval,halfEq _ inBounds,wire]
  · simp [command,arguments,zero,middle]

/-- Executes the table generator against the concrete startup and incidence rows. Both
the command and operand case use the same checked descriptor, with bounds coming from
the actual half count. -/
theorem table_spec {W : ℕ} (A : Arena) (T : Root) (raw : ℕ→ℕ) (cmd : Bool) (m : Memory W)
    (span : tableBase A cmd+7*(T.halves+2)<2^W)
    (header : m (m (A.seed:Word W).val+((if cmd then 0 else 2:ℕ):Word W)).val=(tableBase A cmd:Word W) ∧
      m (m (A.seed:Word W).val+((if cmd then 1 else 3:ℕ):Word W)).val=((7*(T.halves+2):ℕ):Word W))
    (seedData : ∀ j : Fin 14,natMemory m (A.seed+8+j.val)=T.words j)
    (fields : ∀ z,rangeReads T raw z → natMemory m z=raw z)
    (seedAway : ∀ j : Fin 14,A.seed+8+j.val<tableBase A cmd ∨ tableBase A cmd+7*(T.halves+2)≤A.seed+8+j.val)
    (srcAway : ∀ z,rangeReads T raw z → z<tableBase A cmd ∨ tableBase A cmd+7*(T.halves+2)≤z)
    (bounds : ∀ i<T.halves+2, ∀ j : Fin 7, ∀ m',
      DescriptorScan.agreesOutside (tableBase A cmd) (tableBase A cmd+7*(T.halves+2)) m' m →
      (HistoryTerminalTape.formula cmd).Fits W (fun _=>0) (natMemory m') (genInput A (7*i+j.val))) :
    (HeaderScan.procedure (A.seed:Word W) (if cmd then 0 else 2) (if cmd then 1 else 3) (generator W A cmd)).Spec
      (fun x=>x=m) (fun _ out=>out=fillSegment (tableBase A cmd) (7*(T.halves+2)) (tableAt A T raw cmd) m)
      (13+7*(T.halves+2)*(2*(generator W A cmd).binds+4)) := by
  intro _ _ _ machine
  refine Procedure.Spec.atMemory
    (A:=HeaderScan.procedure (A.seed:Word W) (if cmd then 0 else 2) (if cmd then 1 else 3) (generator W A cmd))
    (HeaderScan.spec (A.seed:Word W) (if cmd then 0 else 2) (if cmd then 1 else 3)
      (generator W A cmd) (fun x=>x=m) (fun _=>tableBase A cmd) (fun _=>7*(T.halves+2))
      (fun _=>tableAt A T raw cmd) _ (fun _ _=>⟨span,le_rfl⟩) (by rintro state eq; subst state; exact header)
      ?_) m rfl machine
  intro state same a μ lo hi frame
  subst state
  let δ := a.val-tableBase A cmd
  let i := δ/7
  let j : Fin 7 := ⟨δ%7,Nat.mod_lt _ (by decide)⟩
  have chunks := Nat.mod_add_div δ 7
  have eq : a.val=tableBase A cmd+7*i+j.val := by dsimp [i,j,δ] at *; omega
  have ib : i<T.halves+2 := by have := j.isLt; omega
  have held (x : ℕ) (h : rangeReads T raw x) : natMemory μ x=raw x :=
    (congrArg Fin.val (frame x (srcAway x h))).trans (fields x h)
  have input := generator_word A cmd μ T i j a eq (fun x =>
    (congrArg Fin.val (frame _ (seedAway x))).trans (seedData x)) (bounds i ib j μ frame)
  have both := tables_congr T raw (natMemory μ) i ib held
  rw [eq,table_at]
  simpa only [both.1,both.2] using input

def seedImage {W : ℕ} (A : Arena) (m : Memory W) :=
  fillSegment A.seed 26 (seedAt A m) m

def commandImage {W : ℕ} (A : Arena) (m : Memory W) :=
  let raw := natMemory m
  let T := terminal A raw
  fillSegment A.commands (7*(T.halves+2)) (tableAt A T raw true) (seedImage A m)

def readyImage {W : ℕ} (A : Arena) (m : Memory W) :=
  let raw := natMemory m
  let T := terminal A raw
  fillSegment A.arguments (7*(T.halves+2)) (tableAt A T raw false) (commandImage A m)

private theorem image_eq {W : ℕ} (A : Arena) (m : Memory W) (j : Fin 26) :
    seedImage A m (A.seed+j.val)=(seedWords A (natMemory m) j:Word W) := by
  have hj := j.isLt
  rw [seedImage,fillSegment,ite_eq_left (by omega)]
  simp [seedAt,Nat.mod_eq_of_lt hj]

private theorem seed_kept {W : ℕ} (A : Arena) (m : Memory W) (j : Fin 26)
    (sep : A.seed+26≤A.commands) (sep' : A.seed+26≤A.arguments) :
    commandImage A m (A.seed+j.val)=seedImage A m (A.seed+j.val) ∧
    readyImage A m (A.seed+j.val)=seedImage A m (A.seed+j.val) := by
  have hj := j.isLt
  have pre : A.seed+j.val<A.commands := by omega
  have pre' : A.seed+j.val<A.arguments := by omega
  simp [commandImage,readyImage,fillSegment,not_le.mpr pre,not_le.mpr pre']

theorem loaded_tables {W : ℕ} (A : Arena) (m : Memory W)
    (apart : A.commands+7*((terminal A (natMemory m)).halves+2)≤A.arguments) :
    TickTerminalPrimitive.Tables (terminal A (natMemory m)) (natMemory m) A.commands (readyImage A m) := by
  let raw := natMemory m
  let T := terminal A raw
  change A.commands+7*(T.halves+2)≤A.arguments at apart
  constructor
  · intro i hi j
    have hj := j.isLt
    change i<T.halves+2 at hi
    have here : A.commands≤A.commands+7*i+j.val ∧ A.commands+7*i+j.val<A.commands+7*(T.halves+2) := by omega
    have before : ¬ A.arguments≤A.commands+7*i+j.val := by omega
    change fillSegment A.arguments (7*(T.halves+2)) _ (fillSegment A.commands (7*(T.halves+2)) _ _)
      (A.commands+7*i+j.val)=_
    rw [fillSegment,ite_eq_right (by omega),fillSegment,ite_eq_left here]
    exact table_at A T raw true i j
  · intro i hi j
    have hj := j.isLt
    change i<T.halves+2 at hi
    change fillSegment A.arguments (7*(T.halves+2)) _ _ (A.arguments+7*i+j.val)=_
    rw [fillSegment,ite_eq_left (by omega)]
    exact table_at A T raw false i j

def oneCost (W : ℕ) (A : Arena) (T : Root) (raw : ℕ→ℕ) :=
  let span := 7*(T.halves+2)
  let seed := 4+26*(2*(HeaderScan.closed (w:=W) (boot A)).binds+4)
  let commands := 13+span*(2*(generator W A true).binds+4)
  let arguments := 13+span*(2*(generator W A false).binds+4)
  seed+commands+arguments+TickTerminalPrimitive.cycles W T raw+(6+5*4)

def output {W : ℕ} (A : Arena) (m : Memory W) :=
  let raw := natMemory m
  let cur : Word W := ((A.seed+5:ℕ):Word W)
  let r := readyImage A m
  let done := HistoryReadyTape.after cur (TickTerminalPrimitive.jobs (terminal A raw) raw cur r) r
  PhysicalInputCopy.copied (A.seed+22) 4 A.control done

private theorem next {W : ℕ} {a b : Procedure W} {m n o : Memory W} {α β : ℕ}
    (left : a.Spec (·=m) (fun _ v=>v=n) α) (right : b.Spec (·=n) (fun _ v=>v=o) β) :
    (a.seq b).Spec (·=m) (fun _ v=>v=o) (α+β) := by
  intro _ _ _ machine
  exact Procedure.Spec.mono (A:=a.seq b) (Procedure.Spec.seq (A:=a) (B:=b) left right (fun _ _ h=>h))
    (fun _ h=>h) (fun _ _ h=>h.choose_spec.2) le_rfl machine

def one (W : ℕ) (A : Arena) : Procedure W :=
  let seed := PhysicalInputPhases.writing (HeaderScan.closed (boot A)) Fin.elim0 A.seed 26
  let commands := HeaderScan.procedure (A.seed : Word W) 0 1 (generator W A true)
  let operands := HeaderScan.procedure (A.seed : Word W) 2 3 (generator W A false)
  let execute := HistoryReadyTape.execute (TickTerminalPrimitive.expression W) (Fin.last 0) (fun _ => ((A.seed+5:ℕ):Word W))
  let save := PhysicalInputPhases.copying W (A.seed+22) 4 A.control
  (((seed.seq commands).seq operands).seq execute).seq save

/-- The successor phase reads a pair of header columns from the actual 26-word block. -/
private theorem header_pair {W : ℕ} (A : Arena) (m current : Memory W) (cmd : Bool)
    (fit : A.seed+26<2^W)
    (same : ∀ j : Fin 26,current (A.seed+j.val)=(seedWords A (natMemory m) j:Word W)) :
    current (current (A.seed:Word W).val+((if cmd then 0 else 2:ℕ):Word W)).val=(tableBase A cmd:Word W) ∧
    current (current (A.seed:Word W).val+((if cmd then 1 else 3:ℕ):Word W)).val=
      ((7*((terminal A (natMemory m)).halves+2):ℕ):Word W) := by
  have zero := same 0
  change current (A.seed+0)=((A.seed+1:ℕ):Word W) at zero
  rw [Nat.add_zero] at zero
  have readOff (j : Fin 26) (offset : ℕ) (eq : j.val=1+offset) :
      current (current (A.seed:Word W).val+(offset:Word W)).val=
        (seedWords A (natMemory m) j:Word W) := by
    have hj := j.isLt
    have fits : (A.seed+1)+offset<2^W := by omega
    rw [Fin.val_cast_of_lt (by omega : A.seed<2^W),zero,←Nat.cast_add,Fin.val_cast_of_lt fits]
    rw [show (A.seed+1)+offset=A.seed+j.val by omega]
    exact same j
  cases cmd
  · exact ⟨readOff 3 2 rfl,readOff 4 3 rfl⟩
  · exact ⟨readOff 1 0 rfl,readOff 2 1 rfl⟩

private theorem header_rows {W : ℕ} (A : Arena) (m current : Memory W)
    (same : ∀ j : Fin 26,current (A.seed+j.val)=(seedWords A (natMemory m) j:Word W))
    (small : ∀ j : Fin 14,(terminal A (natMemory m)).words j<2^W) (j : Fin 14) :
    natMemory current (A.seed+8+j.val)=(terminal A (natMemory m)).words j := by
  let idx : Fin 26 := (Fin.natAdd 8 j).castAdd 4
  have h := congrArg Fin.val (same idx)
  simp only [idx,Fin.val_castAdd,Fin.val_natAdd,seedWords,Fin.append_left,Fin.append_right,
    Fin.val_cast_of_lt (small j)] at h
  simpa only [natMemory,Nat.add_assoc] using h

def tableInput {W : ℕ} (A : Arena) (m : Memory W) (cmd : Bool) :=
  if cmd then seedImage A m else commandImage A m

def sourceSafe (T : Root) (raw : ℕ→ℕ) (lo upper : ℕ) :=
  ∀ a,rangeReads T raw a → a<lo ∨ upper≤a

private theorem input_reads {W : ℕ} (A : Arena) (m : Memory W) (cmd : Bool)
    (sep₀ : sourceSafe (terminal A (natMemory m)) (natMemory m) A.seed (A.seed+26))
    (sep₁ : sourceSafe (terminal A (natMemory m)) (natMemory m) A.commands
      (A.commands+7*((terminal A (natMemory m)).halves+2)))
    (z : ℕ) (hz : rangeReads (terminal A (natMemory m)) (natMemory m) z) :
    natMemory (tableInput A m cmd) z=natMemory m z := by
  have h₀ := sep₀ z hz
  have h₁ := sep₁ z hz
  have pre : ¬(A.seed≤z ∧ z<A.seed+26) := by omega
  have mid : ¬(A.commands≤z ∧ z<A.commands+7*((terminal A (natMemory m)).halves+2)) := by omega
  cases cmd <;> simp [natMemory,tableInput,commandImage,seedImage,fillSegment,pre,mid]

private theorem input_seed {W : ℕ} (A : Arena) (m : Memory W) (cmd : Bool) (early : A.seed+26≤A.commands)
    (j : Fin 26) :
    tableInput A m cmd (A.seed+j.val)=(seedWords A (natMemory m) j:Word W) := by
  have hj := j.isLt
  have earlier : ¬ A.commands≤A.seed+j.val := by omega
  cases cmd <;> simp only [tableInput,Bool.false_eq_true,ite_false,ite_true,commandImage,fillSegment,earlier,
    false_and,ite_false] <;> exact image_eq A m j

/-- Address fit and separation assumptions concern the immutable compact directory and the
two physical tables. They are shared by all word writes for this root. -/
structure TableBounds {W : ℕ} (A : Arena) (m : Memory W) : Prop where
  first : A.seed+26≤A.commands
  disjoint : A.commands+7*((terminal A (natMemory m)).halves+2)≤A.arguments
  endArgs : A.arguments+7*((terminal A (natMemory m)).halves+2)<2^W
  words : ∀ j : Fin 14,(terminal A (natMemory m)).words j<2^W
  immutable : sourceSafe (terminal A (natMemory m)) (natMemory m) A.seed (A.seed+26)
  commands : sourceSafe (terminal A (natMemory m)) (natMemory m) A.commands
    (A.commands+7*((terminal A (natMemory m)).halves+2))
  arguments : sourceSafe (terminal A (natMemory m)) (natMemory m) A.arguments
    (A.arguments+7*((terminal A (natMemory m)).halves+2))
  rowFits : ∀ cmd (i : ℕ), i<(terminal A (natMemory m)).halves+2 → ∀ j : Fin 7, ∀ current,
    DescriptorScan.agreesOutside (tableBase A cmd)
      (tableBase A cmd+7*((terminal A (natMemory m)).halves+2)) current (tableInput A m cmd) →
    (HistoryTerminalTape.formula cmd).Fits W (fun _=>0) (natMemory current) (genInput A (7*i+j.val))

private theorem generate_table {W : ℕ} (A : Arena) (m : Memory W) (cmd : Bool) (lim : TableBounds A m) :
    let T := terminal A (natMemory m)
    let span := 7*(T.halves+2)
    (HeaderScan.procedure (A.seed:Word W) (if cmd then 0 else 2) (if cmd then 1 else 3) (generator W A cmd)).Spec
      (·=tableInput A m cmd) (fun _ o=>o=if cmd then commandImage A m else readyImage A m)
      (13+span*(2*(generator W A cmd).binds+4)) := by
  intro T span _ _ _ machine
  have lo := lim.first
  have mid := lim.disjoint
  have up := lim.endArgs
  have early : A.seed+26≤tableBase A cmd := by cases cmd <;> simp [tableBase] <;> omega
  have fit : tableBase A cmd+span<2^W := by
    cases cmd <;> simp only [tableBase,Bool.false_eq_true,ite_false,ite_true,span,T] <;> omega
  have initialWords := input_seed A m cmd lo
  have r := table_spec A T (natMemory m) cmd (tableInput A m cmd) fit
    (header_pair A m _ cmd (by omega) initialWords) (header_rows A m _ initialWords lim.words)
    (input_reads A m cmd lim.immutable lim.commands) (fun j=>Or.inl (by have := j.isLt; omega))
    (by cases cmd; exact lim.arguments; exact lim.commands) (lim.rowFits cmd) machine
  cases cmd <;> exact r

/-- Each root's trivalent and scalar streams are immutable while rows are copied. The
ranges depend only on its compact input directory and on the already computed row counter. -/
structure RootBounds {W : ℕ} (A : Arena) (m : Memory W) : Prop extends TableBounds A m where
  controlFit : A.control+4<2^W
  saveApart : A.control≤A.seed+22 ∨ A.seed+26≤A.control
  bootApart : ∀ z,bootReads A (natMemory m) z → z<A.seed ∨ A.seed+26≤z
  bootFits : ∀ z : Word W,A.seed≤z.val → z.val<A.seed+26 → ∀ current,
    DescriptorScan.agreesOutside A.seed (A.seed+26) current m →
    (boot A).Fits W (fun _=>0) (natMemory current) (fun _=>z.val)
  endpointFit : let T := terminal A (natMemory m); T.endpoints+T.ext≤2^W
  endpointApart : let T := terminal A (natMemory m)
    ∀ z,T.endpoints≤z → z<T.endpoints+T.ext → TickTerminalPrimitive.Outside T.map (T.map+T.ext) z
  pinOutputs : let raw := natMemory m; let T := terminal A raw; let r := readyImage A m
    ∀ i,i<T.halves+1 → let x := TickTerminalPrimitive.pinJob T raw r i
      TickTerminalPrimitive.Protected T A.commands ((A.seed+5:ℕ):Word W) x.start x.finish ∧ x.finish<2^W
  rowOutput : let T := terminal A (natMemory m)
    TickTerminalPrimitive.Protected T A.commands ((A.seed+5:ℕ):Word W) T.meta (T.meta+4*T.rows) ∧
      T.meta+4*T.rows<2^W
  joinApart : let raw := natMemory m; let T := terminal A raw; let r := readyImage A m
    let c := ((A.seed+5:ℕ):Word W)
    HistoryJoinScan.Separate ((TickTerminalPrimitive.joinArgument T:ℕ):Word W) T.meta (T.meta+4*T.rows)
      (HistoryReadyTape.after c (TickTerminalPrimitive.pinJobs T raw r 0 (T.halves+1)) r)

/-- Executes the selected root's real five-phase procedure through its consuming continuation.
The effect and cost use the precise selected stream, with a bounded job for each incident half. -/
theorem one_spec {W : ℕ} (A : Arena) (m : Memory W) (h : RootBounds A m) :
    (one W A).Spec (·=m) (fun _ o=>o=output A m) (oneCost W A (terminal A (natMemory m)) (natMemory m)) := by
  let raw := natMemory m
  let T := terminal A raw
  let r := readyImage A m
  let ctrl : Word W := ((A.seed+5:ℕ):Word W)
  have lo := h.first
  have mid := h.disjoint
  have up := h.endArgs
  change A.commands+7*(T.halves+2)≤A.arguments at mid
  change A.arguments+7*(T.halves+2)<2^W at up
  have seedFit : A.seed+26<2^W := by omega
  have ctrlVal : ctrl.val=A.seed+5 := Fin.val_cast_of_lt (by omega)
  have seed (j : Fin 26) : r (A.seed+j.val)=(seedWords A raw j:Word W) :=
    (seed_kept A m j lo (by omega)).2.trans (image_eq A m j)
  have cur : r ctrl.val=(A.commands:Word W) := by rw [ctrlVal]; exact seed 5
  have endOf : r (ctrl+1).val=((A.commands+7*(T.halves+2):ℕ):Word W) := by
    have adr : (ctrl+1).val=A.seed+6 := by
      change (((A.seed+5:ℕ):Word W)+((1:ℕ):Word W)).val=A.seed+6
      rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    rw [adr]
    exact seed 6
  let done := HistoryReadyTape.after ctrl (TickTerminalPrimitive.jobs T raw ctrl r) r
  have run : (HistoryReadyTape.execute (TickTerminalPrimitive.expression W) (Fin.last 0) (fun _ => ctrl)).Spec
      (fun x => x=r) (fun _ o => o=done) (TickTerminalPrimitive.cycles W T raw) := by
    intro _ _ _ machine
    exact Procedure.Spec.atMemory
      (A:=HistoryReadyTape.execute (TickTerminalPrimitive.expression W) (Fin.last 0) (fun _ => ctrl))
      (TickTerminalPrimitive.execute_spec T raw A.commands ctrl r cur endOf (loaded_tables A m mid)
      (by rw [ctrlVal]; omega) (by omega) up.le (by omega) (by left; rw [ctrlVal]; change A.seed+5<A.arguments; omega)
      h.endpointFit h.endpointApart (fun i hi=>(h.pinOutputs i hi).1) (fun i hi=>(h.pinOutputs i hi).2)
      h.rowOutput.1 h.rowOutput.2 h.joinApart) r rfl machine
  intro _ _ _ machine
  exact next (next (next (next (start_spec A m seedFit h.bootApart h.bootFits)
    (generate_table A m true h.toTableBounds)) (generate_table A m false h.toTableBounds)) run)
    (Procedure.Spec.atMemory (A:=PhysicalInputPhases.copying W (A.seed+22) 4 A.control)
      (PhysicalInputPhases.copying_spec (w:=W) (A.seed+22) 4 A.control (by omega) h.controlFit h.saveApart)
      done trivial) machine

/-- Each slot sweeps its list exactly once. The countdown preamble installs the true
filtered list length in control+4. All row and half counts remain memory values. -/
def many (W : ℕ) (A : Arena) : Procedure W := (one W A).counted ((A.control+4:ℕ):Word W)

open HistoryReadyTape

private theorem after_away {W : ℕ} (c : Word W) (r : Memory W) (xs : List (Job W)) (a : ℕ)
    (cursor : a≠c.val) (jobs : ∀ x∈xs,a<x.start ∨ x.finish≤a) : after c xs r a=r a := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    have apart := jobs x (List.mem_cons_self ..)
    have bounds : ¬(x.start≤a ∧ a<x.start+x.count) := by change a<x.start ∨ x.start+x.count≤a at apart; omega
    rw [HistoryReadyTape.after,ih _ (fun y hy=>jobs y (List.mem_cons_of_mem _ hy))]
    simp only [HistoryJoinController.bumpMemory,writeMemory,cursor,ite_false,fillSegment,bounds,ite_false]

def retained {W : ℕ} (A : Arena) (m : Memory W) (a : ℕ) :=
  let T := terminal A (natMemory m)
  let c := ((A.seed+5:ℕ):Word W)
  a≠c.val ∧ ∀ x ∈ TickTerminalPrimitive.jobs T (natMemory m) c (readyImage A m),a<x.start ∨ x.finish≤a

theorem counts_out {W : ℕ} (A : Arena) (m : Memory W) (h : RootBounds A m)
    (saved : ∀ j : Fin 4,retained A m (A.seed+22+j.val)) (j : Fin 4) :
    output A m (A.control+j.val)=(seedWords A (natMemory m) (Fin.natAdd 22 j):Word W) := by
  let r := readyImage A m
  let T := terminal A (natMemory m)
  let c := ((A.seed+5:ℕ):Word W)
  let xs := TickTerminalPrimitive.jobs T (natMemory m) c r
  change PhysicalInputCopy.copied _ 4 _ (after c xs r) _=_
  rw [PhysicalInputCopy.copied_at _ _ _ _ _ j.isLt,after_away c r xs _ (saved j).1 (saved j).2]
  have first := h.first
  have next := h.disjoint
  have row := seed_kept A m (Fin.natAdd 22 j) first (by omega)
  rw [show A.seed+22+j.val=A.seed+(Fin.natAdd 22 j).val by simp [Nat.add_assoc]]
  exact row.2.trans (image_eq A m (Fin.natAdd 22 j))

theorem output_frame {W : ℕ} (A : Arena) (m : Memory W) (z : ℕ)
    (outside : retained A m z) (small : z<A.control ∨ A.control+4≤z)
    (seed : z<A.seed ∨ A.seed+26≤z)
    (cmd : z<A.commands ∨ A.commands+7*((terminal A (natMemory m)).halves+2)≤z)
    (arg : z<A.arguments ∨ A.arguments+7*((terminal A (natMemory m)).halves+2)≤z) :
    output A m z=m z := by
  rw [output,PhysicalInputCopy.copied_outside _ _ _ _ _ small,after_away _ _ _ _ outside.1 outside.2]
  simp only [readyImage,commandImage,seedImage,fillSegment,ite_eq_right (show ¬(A.seed≤z ∧ z<A.seed+26) by omega),
    ite_eq_right (show ¬(A.commands≤z ∧ z<A.commands+7*((terminal A (natMemory m)).halves+2)) by omega),
    ite_eq_right (show ¬(A.arguments≤z ∧ z<A.arguments+7*((terminal A (natMemory m)).halves+2)) by omega)]

def countdown {W : ℕ} (A : Arena) : Word W := ((A.control+4:ℕ):Word W)

def decrease {W : ℕ} (A : Arena) (m : Memory W) :=
  let c := countdown (W:=W) A
  writeMemory m c (m c.val-1)

/-- The deterministic pure recurrence uses exactly the same control decrement and physical
row writes as the native counted loop. An empty slot starts and stops at its initial image. -/
def images {W : ℕ} (A : Arena) (m : Memory W) : ℕ→Memory W
  | 0=>m
  | i+1=>output A (decrease A (images A m i))

def iterationCost {W : ℕ} (A : Arena) (m : Memory W) (i : ℕ) :=
  let raw := natMemory (decrease A (images A m i))
  oneCost W A (terminal A raw) raw

theorem many_spec {W : ℕ} (A : Arena) (m : Memory W) (n : ℕ)
    (initial : (m (countdown (W:=W) A).val).val=n)
    (lim : ∀ i<n,RootBounds A (decrease A (images A m i)))
    (counter : ∀ i<n, let before := decrease A (images A m i)
      output A before (countdown (W:=W) A).val=before (countdown (W:=W) A).val) :
    (many W A).Spec (·=m) (fun _ o=>o=images A m n)
    (4+7*n+∑ j ∈ Finset.range n,iterationCost A m (n-(j+1))) := by
  let c := countdown (W:=W) A
  let inv (z : ℕ) (state : Memory W) := z≤n ∧ state=images A m (n-z)
  have run : ((one W A).counted c).Spec (fun μ => inv n μ ∧ (μ c.val).val=n)
      (fun _ out=>inv 0 out) (4+7*n+∑ j ∈ Finset.range n,iterationCost A m (n-(j+1))) :=
    Procedure.counted_cost (one W A) c n (fun z=>iterationCost A m (n-(z+1))) inv (by
      intro z state invZ count
      obtain ⟨bound,eq⟩ := invZ
      let i := n-(z+1)
      have ib : i<n := by dsimp [i]; omega
      let μ' := decrease A (images A m i)
      change state=images A m i at eq
      subst state
      intro _ _ _ machine
      refine Procedure.Spec.mono (A:=one W A) (one_spec A μ' (lim i ib)) (fun _ q=>q) ?_ le_rfl machine
      rintro _ _ rfl
      refine ⟨?_,by change z≤n ∧ output A μ'=images A m (n-z); rw [show n-z=i+1 by dsimp [i]; omega]; exact ⟨by omega,rfl⟩⟩
      rw [counter i ib]
      change (writeMemory _ c (_-1) c.val).val=_
      simp only [writeMemory,ite_true]
      have positive : 0<((images A m i) c.val).val := by omega
      rw [←Fin.cast_val_eq_self ((images A m i) c.val),←Nat.cast_one (R:=Word W),
        ←Nat.cast_sub (show 1≤((images A m i) c.val).val by omega),
        Fin.val_cast_of_lt (by have := ((images A m i) c.val).isLt; omega)]
      omega)
  intro _ _ _ machine
  exact Procedure.Spec.mono (A:=(one W A).counted c) run
    (by rintro x rfl; exact ⟨⟨le_rfl,by simp [images]⟩,initial⟩)
    (by rintro _ o ⟨_,q⟩; simpa using q) le_rfl machine

end ThreeFlat.RAM.TickTerminalRoot

end
end OAI
