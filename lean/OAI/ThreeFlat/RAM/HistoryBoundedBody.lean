import OAI.ThreeFlat.RAM.HistoryPartyBatchExec

namespace OAI
/-! # Native joins on a bounded list of completed local roots -/

namespace ThreeFlat.RAM.HistoryBoundedBody

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open HistoryBoundedJoin
open scoped Fin.CommRing BigOperators

/-- The hub consists of its six public fields followed by the destination
of the cached four-word result. Its child rows and per-child operands have
already been produced from the selected site. The argument and command
areas are reused as soon as this bounded join is complete. -/
structure Layout where
  hub : ℕ
  seed : ℕ
  commands : ℕ

private abbrev E := Formula 1
private def rd (a : E) (j : ℕ) : E := .load (add a (.lit j))
private def pick (a : E) : ℕ → List E → E
  | _,[] => .lit 0
  | i,x::xs => eqz a (.lit i) x (pick a (i+1) xs)

def boot (A : Layout) : E :=
  let k := rd (.lit A.hub) 3
  let args := rd (.lit A.hub) 5
  let output := rd (.lit A.hub) 6
  let cs := mul (.lit 14) k
  pick (.cut (.reg 0) (.lit A.seed)) 0
    [.lit (A.seed+1),.lit A.commands,cs,args,mul (.lit 7) k,output,.lit 4,.lit A.commands,add (.lit A.commands) cs]

def bootWords (A : Layout) (m : ℕ→ℕ) : Fin 9 → ℕ :=
  let k := m (A.hub+3)
  ![A.seed+1,A.commands,14*k,m (A.hub+5),7*k,m (A.hub+6),4,A.commands,A.commands+14*k]

theorem boot_value (A : Layout) (W : ℕ) (d : Param→ℕ) (m : ℕ→ℕ) (j : Fin 9) :
    (boot A).natural W d m (fun _ => A.seed+j.val)=bootWords A m j := by
  fin_cases j <;> simp [boot,bootWords,rd,pick,eqz,add,mul,Formula.natural,natOp,natTest]

private def fieldSum (A : Layout) (j : ℕ) : ℕ→E
  | 0 => .lit 0
  | t+1 =>
    let h := Formula.lit A.hub
    let row := rd h 4
    let child : E := .load (add row (.lit (4*t)))
    add (fieldSum A j t) (lt (.lit t) (rd h 3) (rd child j) (.lit 0))

def result (A : Layout) (cap : ℕ) : E :=
  let h := Formula.lit A.hub
  pick (.cut (.reg 0) (rd h 6)) 0 [rd h 0,rd h 1,fieldSum A 2 cap,add (rd h 2) (fieldSum A 3 cap)]


theorem result_work (A B : Layout) (cap : ℕ) : (result A cap).work=(result B cap).work := by
  have hs (j : ℕ) (n : ℕ) : (fieldSum A j n).work=(fieldSum B j n).work := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (fieldSum A j n).work+_+1=(fieldSum B j n).work+_+1
      rw [ih]
      rfl
  simp only [result,pick,rd,eqz,add,Formula.work,hs]

private theorem sum_at (A : Layout) (j cap W : ℕ) (d : Param→ℕ) (m : ℕ→ℕ) (vs : Fin 1→ℕ) :
    (fieldSum A j cap).natural W d m vs=∑ i∈Finset.range cap,if i< m (A.hub+3) then
        m (m (m (A.hub+4)+4*i)+j) else 0 := by
  induction cap with
  | zero => simp [fieldSum,Formula.natural]
  | succ t ih =>
    by_cases live : t < m (A.hub+3) <;>
      simp [fieldSum,Finset.sum_range_succ,ih,rd,lt,add,Formula.natural,natOp,natTest,live]

def resultWords (A : Layout) (cap : ℕ) (m : ℕ→ℕ) : Fin 4 → ℕ :=
  let S (j : ℕ) := ∑ i∈Finset.range cap,if i< m (A.hub+3) then m (m (m (A.hub+4)+4*i)+j) else 0
  ![m A.hub,m (A.hub+1),S 2,m (A.hub+2)+S 3]

theorem result_value (A : Layout) (cap W : ℕ) (d : Param→ℕ) (m : ℕ→ℕ) (j : Fin 4) :
    (result A cap).natural W d m (fun _ => m (A.hub+6)+j.val)=resultWords A cap m j := by
  fin_cases j <;> simp [result,resultWords,rd,pick,eqz,add,Formula.natural,natOp,natTest,sum_at]

def generator (W : ℕ) (A : Layout) (cap : ℕ) (commands : Bool) : Term W 0 1 :=
  let base := if commands then Term.literal (A.commands : Word W) else
    (Term.literal ((A.hub+5 : ℕ) : Word W)).load
  let rel := Term.binary .sub (.result 0) base
  (HeaderScan.closed (HistoryBoundedJoin.formula cap commands)).instantiate
    (fun i => if i=0 then .literal (A.hub : Word W) else if i=5 then rel else .literal 0)

/-- Ordinally ordered [pin-map,copy] instruction pairs, with a cache
containing the dimensions and the absolute output pointer of this join. -/
noncomputable def procedure (W : ℕ) (A : Layout) (cap : ℕ) : Procedure W :=
  let seed := PhysicalInputPhases.writing (HeaderScan.closed (boot A)) Fin.elim0 A.seed 9
  let commands := HeaderScan.procedure (A.seed : Word W) 0 1 (generator W A cap true)
  let args := HeaderScan.procedure (A.seed : Word W) 2 3 (generator W A cap false)
  let run := HistoryReadyTape.execute (HistorySelectedOps.rows (.literal (0 : Word W) : Term W 0 4) [])
    (Fin.last 0) (fun _ => ((A.seed+7 : ℕ):Word W))
  let save := HeaderScan.procedure (A.seed : Word W) 4 5 (HeaderScan.closed (result A cap))
  ((seed.seq commands).seq args).seq (run.seq save)


theorem boot_fits (A : Layout) (W : ℕ) (d : Param → ℕ) (m : ℕ → ℕ) (j : Fin 9)
    (seedRoom : A.seed+9 < 2^W) (hubRoom : A.hub+7 < 2^W) :
    (boot A).Fits W d m (fun _ => A.seed+j.val) := by
  have indexRoom := j.isLt
  have offset : A.seed+j.val-A.seed=j.val := Nat.add_sub_cancel_left _ _
  simp only [boot,pick,rd,eqz,add,mul,Formula.Fits,Formula.natural,opFits,natOp,natTest,offset]
  split_ifs <;> (repeat' apply And.intro) <;> first | trivial | omega

private theorem fieldSum_fits (A : Layout) (W : ℕ) (d : Param → ℕ) (m : ℕ → ℕ)
    (vs : Fin 1 → ℕ) (field cap : ℕ) (hf : field≤3) (hubRoom : A.hub+7 < 2^W)
    (capRoom : cap≤2^W) (argcRoom : m (A.hub+3) < 2^W)
    (linkRoom : m (A.hub+4)+4*m (A.hub+3) ≤ 2^W)
    (rootRoom : ∀ i : Fin (m (A.hub+3)), m (m (A.hub+4)+4*i.val)+3 < 2^W) :
    (fieldSum A field cap).Fits W d m vs := by
  have header (k : ℕ) (hk : k≤6) : (rd (.lit A.hub) k).Fits W d m vs :=
    ⟨⟨trivial,trivial,trivial⟩,show A.hub+k<2^W by omega⟩
  induction cap with
  | zero => trivial
  | succ t ih =>
    have index : t < 2^W := by omega
    refine ⟨ih (by omega),⟨trivial,header 3 (by decide),index,argcRoom,?_⟩,trivial⟩
    by_cases live : t < m (A.hub+3)
    · have link : m (A.hub+4)+4*t < 2^W := by omega
      have root : m (m (A.hub+4)+4*t)+field < 2^W := by
        have := rootRoom ⟨t,live⟩
        change m (m (A.hub+4)+4*t)+3 < 2^W at this
        omega
      simp only [Formula.natural,natOp,natTest,rd,add,decide_eq_true_eq,ite_eq_left live]
      exact ⟨⟨⟨⟨header 4 (by decide),trivial,trivial⟩,link⟩,trivial,trivial⟩,root⟩
    · simp only [Formula.natural,natOp,natTest,rd,add,decide_eq_true_eq,ite_eq_right live,Formula.Fits]

/-- The result reads its four hub fields and the row and bit totals of each live child.
The absolute sum addresses and the selected output address fit in the current word. -/
theorem result_fits (A : Layout) (cap W out : ℕ) (d : Param → ℕ) (m : ℕ → ℕ) (j : Fin 4)
    (whereOut : m (A.hub+6)=out) (hubRoom : A.hub+7 < 2^W) (outputRoom : out+4 < 2^W)
    (capRoom : cap≤2^W) (argcRoom : m (A.hub+3) < 2^W)
    (linkRoom : m (A.hub+4)+4*m (A.hub+3) ≤ 2^W)
    (rootRoom : ∀ i : Fin (m (A.hub+3)), m (m (A.hub+4)+4*i.val)+3 < 2^W) :
    (result A cap).Fits W d m (fun _ => out+j.val) := by
  have sum (field : ℕ) (hf : field≤3) :=
    fieldSum_fits A W d m (fun _ => out+j.val) field cap hf hubRoom capRoom argcRoom linkRoom rootRoom
  have rows := sum 2 (by decide)
  have bits := sum 3 (by decide)
  have indexRoom := j.isLt
  have offset : out+j.val-out=j.val := Nat.add_sub_cancel_left _ _
  simp only [result,pick,rd,eqz,add,Formula.Fits,Formula.natural,opFits,natOp,natTest,
    whereOut,offset,rows,bits]
  split_ifs <;> (repeat' apply And.intro) <;> first | trivial | exact rows | exact bits | omega

open HistoryPartyBatchExec
variable {W : ℕ}

def stageRegs (A : Layout) (j : ℕ) (u : Fin 13) := if u=0 then A.hub else if u=5 then j else 0

def rowWidth (commands : Bool) := if commands then 14 else 7

def dataWord (commands : Bool) (T : Hub) (m : ℕ→ℕ) (i pos : ℕ) : ℕ :=
  let col : Fin 7 := ⟨pos%7,Nat.mod_lt _ (by decide)⟩
  if commands then command T m i (decide (7≤pos)) col else arguments T m i col

def tableWord (commands : Bool) (T : Hub) (m : ℕ→ℕ) (base addr : ℕ) : Word W :=
  let x := addr-base
  (dataWord commands T m (x/rowWidth commands) (x%rowWidth commands):Word W)

theorem generator_word (A : Layout) (T : Hub) (cap : ℕ) (commands : Bool) (input : Memory W)
    (i pos : ℕ) (rp : pos<rowWidth commands) (bound : i≤cap)
    (header : ∀ j : Fin 6,numeric input (A.hub+j.val)=T.words j)
    (ptr : A.hub+5<2^W)
    (fits : (HistoryBoundedJoin.formula cap commands).Fits W (fun _=>0) (numeric input)
      (stageRegs A (rowWidth commands*i+pos))) :
    (generator W A cap commands).eval Fin.elim0 input
      (fun _ => (((if commands then A.commands else T.arguments)+(rowWidth commands*i+pos):ℕ):Word W))=
      (dataWord commands T (numeric input) i pos:Word W) := by
  let k := rowWidth commands*i+pos
  have hdr := header (5:Fin 6)
  change (input (A.hub+5)).val=T.arguments at hdr
  have hdrWord : input (A.hub+5)=(T.arguments:Word W) := by rw [←hdr,Fin.cast_val_eq_self]
  have src : (((A.hub+5:ℕ):Word W)).val=A.hub+5 := Fin.val_cast_of_lt ptr
  have slot : (↑A.hub+(5:Word W)).val=A.hub+5 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using src
  let reg := stageRegs A k
  have conv : ((generator W A cap commands).eval Fin.elim0 input (fun _=>(((if commands then A.commands else T.arguments)+k:ℕ):Word W)))=
    (HeaderScan.closed (HistoryBoundedJoin.formula cap commands)).eval Fin.elim0 input (fun j=>(reg j:Word W)) := by
    rw [generator,Term.eval_instantiate]
    apply congrArg _
    funext j
    by_cases addr : j=0 <;> by_cases ix : j=5 <;> cases commands <;>
      simp [reg,stageRegs,addr,ix,Term.eval,Nat.cast_add,BinaryOp.eval,slot,hdrWord]
  apply conv.trans
  have calcWord := closed_eval (HistoryBoundedJoin.formula cap commands) (numeric input) reg fits
  rw [word_numeric input] at calcWord
  apply calcWord.trans
  let j : Fin 7 := ⟨pos%7,Nat.mod_lt _ (by decide)⟩
  let copy := decide (7≤pos)
  have key : reg 5=if commands then 14*i+7*copy.toNat+j.val else 7*i+j.val := by
    cases commands with
    | false =>
      change pos < 7 at rp
      change 7*i+pos=7*i+pos%7
      rw [Nat.mod_eq_of_lt rp]
    | true =>
      change pos < 14 at rp
      change 14*i+pos=14*i+7*(decide (7≤pos)).toNat+pos%7
      by_cases inCopy : 7≤pos <;> simp [inCopy] <;> omega
  exact congrArg (fun x : ℕ => (x:Word W)) (make_word W cap T A.hub _ _ reg i j commands copy bound
    (by simp [reg,stageRegs]) header key)

/-- Every read in the preparation loop is either a fixed hub field, a local
link, or one of the four fields at the linked older node. -/
structure Frame (A : Layout) (T : Hub) (input : Memory W) (lo len : ℕ) : Prop where
  hub : ∀ j : Fin 7,A.hub+j.val<lo ∨ lo+len≤A.hub+j.val
  links : ∀ (i : Fin T.argc) (j : Fin 4),let x := T.children+4*i.val+j.val
    x<lo ∨ lo+len≤x
  nodes : ∀ (i : Fin T.argc) (j : Fin 4),let x := (child T (numeric input) i.val).node+j.val
    x<lo ∨ lo+len≤x

private theorem link_eq (A : Layout) (T : Hub) (μ m : Memory W) {lo len : ℕ}
    (f : Frame A T m lo len) (same : DescriptorScan.agreesOutside lo (lo+len) μ m) (i : Fin T.argc) :
    child T (numeric μ) i.val=child T (numeric m) i.val := by
  let x := T.children+4*i.val
  have get (k : Fin 4) : numeric μ (x+k.val)=numeric m (x+k.val) := congrArg Fin.val (same _ (f.links i k))
  have h0 : numeric μ x=numeric m x := by simpa using get 0
  have h1 : numeric μ (x+1)=numeric m (x+1) := get 1
  have h2 : numeric μ (x+2)=numeric m (x+2) := get 2
  have h3 : numeric μ (x+3)=numeric m (x+3) := get 3
  change Child.mk (numeric μ x) (numeric μ (x+1)) (numeric μ (x+2)) (numeric μ (x+3))=_
  rw [h0,h1,h2,h3]; rfl

private theorem node_eq (A : Layout) (T : Hub) (μ m : Memory W) {lo len : ℕ}
    (f : Frame A T m lo len) (same : DescriptorScan.agreesOutside lo (lo+len) μ m) (i : Fin T.argc) :
    read (child T (numeric μ) i.val).node (numeric μ)=read (child T (numeric m) i.val).node (numeric m) := by
  rw [link_eq A T μ m f same i]
  let x := (child T (numeric m) i.val).node
  have get (k : Fin 4) : numeric μ (x+k.val)=numeric m (x+k.val) := congrArg Fin.val (same _ (f.nodes i k))
  have h0 : numeric μ x=numeric m x := by simpa using get 0
  have h1 : numeric μ (x+1)=numeric m (x+1) := get 1
  have h2 : numeric μ (x+2)=numeric m (x+2) := get 2
  have h3 : numeric μ (x+3)=numeric m (x+3) := get 3
  change Info.mk (numeric μ x) (numeric μ (x+1)) (numeric μ (x+2)) (numeric μ (x+3))=_
  rw [h0,h1,h2,h3]; rfl

private theorem data_eq (A : Layout) (T : Hub) (μ m : Memory W) {lo len : ℕ}
    (f : Frame A T m lo len) (same : DescriptorScan.agreesOutside lo (lo+len) μ m)
    (i : Fin T.argc) (b : Bool) (pos : ℕ) :
    dataWord b T (numeric μ) i.val pos=dataWord b T (numeric m) i.val pos := by
  have sum (g : Info→ℕ) : total T (numeric μ) i.val g=total T (numeric m) i.val g := by
    unfold total
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg g (node_eq A T μ m f same ⟨k,(Finset.mem_range.mp hk).trans i.isLt⟩)
  have nod := node_eq A T μ m f same i
  have lnk := link_eq A T μ m f same i
  rw [lnk] at nod
  simp only [dataWord,command,arguments,moved,offset,nod,lnk,sum]

/-- Both native bounded-degree scans actually generate the map/copy
control records and their seven relocation operands for every old child. -/
theorem table_exec (A : Layout) (T : Hub) (cap : ℕ) (commands : Bool) (input : Memory W)
    (header : ∀ j : Fin 6,numeric input (A.hub+j.val)=T.words j)
    (bounded : T.argc≤cap) (safe : A.hub+5<2^W)
    (base entry : ℕ) (dst : base=if commands then A.commands else T.arguments)
    (h0 : HeaderScan.headerWord input (A.seed:Word W) entry=(base:Word W))
    (h1 : HeaderScan.headerWord input (A.seed:Word W) (entry+1)=((rowWidth commands*T.argc:ℕ):Word W))
    (limit : base+rowWidth commands*T.argc<2^W)
    (frame : Frame A T input base (rowWidth commands*T.argc)) (small : 14<2^W)
    (capRoom : cap≤2^W) (linkRoom : T.children+4*T.argc≤2^W)
    (rootRoom : ∀ i : Fin T.argc,(child T (numeric input) i.val).node+3<2^W)
    (hubRoom : A.hub+6<2^W) :
    (HeaderScan.procedure (A.seed:Word W) entry (entry+1) (generator W A cap commands)).Exec input
      (fillSegment base (rowWidth commands*T.argc) (tableWord commands T (numeric input) base) input)
      (13+rowWidth commands*T.argc*(2*(generator W A cap commands).binds+4)) := by
  apply scan_dynamic _ _ _ _ _ _ _ _ limit h0 h1
  intro a μ lo hi same
  have bank (k : Fin 6) : numeric μ (A.hub+k.val)=T.words k :=
    (congrArg Fin.val (same _ (frame.hub k.castSucc))).trans (header k)
  have wpos : 0<rowWidth commands := by cases commands <;> decide
  let x := a.val-base
  have ends : x<rowWidth commands*T.argc := by dsimp [x];omega
  have dim : x/rowWidth commands<T.argc := (Nat.div_lt_iff_lt_mul wpos).2 (by rwa [Nat.mul_comm])
  let i : Fin T.argc := ⟨x/rowWidth commands,dim⟩
  let j : Fin (rowWidth commands) := ⟨x%rowWidth commands,Nat.mod_lt _ wpos⟩
  have split : rowWidth commands*i.val+j.val=x := Nat.div_add_mod x _
  have id : base+x=a.val := Nat.add_sub_of_le lo
  have live (k : Fin T.argc) : (child T (numeric μ) k.val).node+3<2^W := by
    rw [link_eq A T μ input frame same k]
    exact rootRoom k
  have fit := HistoryBoundedJoin.formula_fits W cap T A.hub (fun _=>0) (numeric μ)
    (stageRegs A (rowWidth commands*i.val+j.val)) commands i j (by simp [stageRegs]) bank
    (by simp [stageRegs,rowWidth]) hubRoom small (by simp [stageRegs];rw [split];omega) capRoom linkRoom live
  have out := generator_word A T cap commands μ i.val j.val j.isLt (by have := i.isLt;omega) bank safe fit
  rw [←dst,split,id,Fin.cast_val_eq_self,data_eq A T μ input frame same i commands j.val] at out
  simpa only [tableWord,←id,Nat.add_sub_cancel_left] using out

theorem boot_exec (A : Layout) (input : Memory W) (room : A.seed+9<2^W)
    (hubRoom : A.hub+7<2^W) (apart : A.hub+7≤A.seed ∨ A.seed+9≤A.hub) :
    (PhysicalInputPhases.writing (HeaderScan.closed (boot A)) Fin.elim0 A.seed 9).Exec input
      (fillSegment A.seed 9 (fun a => if h : a-A.seed<9 then (bootWords A (numeric input) ⟨a-A.seed,h⟩:Word W) else 0) input)
      (4+9*(2*(HeaderScan.closed (w:=W) (boot A)).binds+4)) := by
  intro P R K machine pc reg pub exit installed params cfg src entry original
  subst src
  refine PhysicalInputPhases.writing_spec (HeaderScan.closed (boot A)) Fin.elim0 A.seed 9 room
    (fun m => m=input) (fun a => if h : a-A.seed<9 then
      (bootWords A (numeric input) ⟨a-A.seed,h⟩ : Word W) else 0) ?_
    machine pc reg pub exit installed params cfg input entry rfl
  intro orig initial a μ lo hi same
  subst orig
  let j : Fin 9 := ⟨a.val-A.seed,by omega⟩
  have key : A.seed+j.val=a.val := Nat.add_sub_of_le lo
  have keep (k : Fin 7) : numeric μ (A.hub+k.val)=numeric input (A.hub+k.val) :=
    congrArg Fin.val (same _ (by have := k.isLt;omega))
  have eq : bootWords A (numeric μ) j=bootWords A (numeric input) j := by
    have argc : numeric μ (A.hub+3)=numeric input (A.hub+3) := keep 3
    have argv : numeric μ (A.hub+5)=numeric input (A.hub+5) := keep 5
    have output : numeric μ (A.hub+6)=numeric input (A.hub+6) := keep 6
    simp only [bootWords,argc,argv,output]
  have val := closed_eval (boot A) (numeric μ) (fun _=>A.seed+j.val)
    (boot_fits A W (fun _=>0) (numeric μ) j room hubRoom)
  rw [word_numeric μ,boot_value,eq,key,Fin.cast_val_eq_self] at val
  rw [dite_eq_left (show a.val-A.seed<9 from j.isLt)]
  exact val

def readHub (A : Layout) (m : ℕ→ℕ) : Hub := ⟨m A.hub,m (A.hub+1),m (A.hub+2),
  m (A.hub+3),m (A.hub+4),m (A.hub+5)⟩

private theorem results_eq (A : Layout) (cap : ℕ) (μ m : Memory W) {lo len : ℕ}
    (f : Frame A (readHub A (numeric m)) m lo len) (same : DescriptorScan.agreesOutside lo (lo+len) μ m) :
    resultWords A cap (numeric μ)=resultWords A cap (numeric m) := by
  have hub (k : ℕ) (bound : k<7) :
      numeric μ (A.hub+k)=numeric m (A.hub+k) :=
    congrArg Fin.val (same _ (f.hub ⟨k,bound⟩))
  have hz : numeric μ A.hub=numeric m A.hub := hub 0 (by decide)
  have sum (j : ℕ) (field : j<4) :
      (∑ k∈Finset.range cap,if k<numeric μ (A.hub+3) then
        numeric μ (numeric μ (numeric μ (A.hub+4)+4*k)+j) else 0) =
      ∑ k∈Finset.range cap,if k<numeric m (A.hub+3) then
        numeric m (numeric m (numeric m (A.hub+4)+4*k)+j) else 0 := by
    rw [hub 3 (by decide),hub 4 (by decide)]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k<numeric m (A.hub+3)
    · simp only [ite_eq_left hk]
      let i : Fin (readHub A (numeric m)).argc := ⟨k,hk⟩
      let addr := numeric m (A.hub+4)+4*k
      have keep : addr<lo ∨ lo+len≤addr := f.links i 0
      have ptr : numeric μ addr=numeric m addr := congrArg Fin.val (same _ keep)
      dsimp only [addr] at ptr
      rw [ptr]
      exact congrArg Fin.val (same _ (f.nodes i ⟨j,field⟩))
    · simp only [ite_eq_right hk]
  simp only [resultWords,hz,hub 1 (by decide),hub 2 (by decide),sum 2 (by decide),sum 3 (by decide)]

def resultAt (A : Layout) (cap : ℕ) (raw : ℕ→ℕ) (out addr : ℕ) : Word W :=
  if h : addr-out<4 then (resultWords A cap raw ⟨addr-out,h⟩:Word W) else 0

theorem result_exec (A : Layout) (cap out : ℕ) (input : Memory W)
    (whereOut : numeric input (A.hub+6)=out)
    (h0 : HeaderScan.headerWord input (A.seed:Word W) 4=(out:Word W))
    (h1 : HeaderScan.headerWord input (A.seed:Word W) 5=4)
    (room : out+4<2^W) (hubRoom : A.hub+7<2^W) (capRoom : cap≤2^W)
    (linkRoom : numeric input (A.hub+4)+4*numeric input (A.hub+3)≤2^W)
    (rootRoom : ∀ k : Fin (numeric input (A.hub+3)),numeric input (numeric input (A.hub+4)+4*k.val)+3<2^W)
    (frame : Frame A (readHub A (numeric input)) input out 4) :
    (HeaderScan.procedure (A.seed:Word W) 4 5 (HeaderScan.closed (result A cap))).Exec input
      (fillSegment out 4 (resultAt A cap (numeric input) out) input)
      (13+4*(2*(HeaderScan.closed (w:=W) (result A cap)).binds+4)) := by
  apply scan_dynamic _ _ _ _ _ _ _ _ room h0 h1
  intro a μ lo hi same
  let j : Fin 4 := ⟨a.val-out,by omega⟩
  have idx : out+j.val=a.val := Nat.add_sub_of_le lo
  have hub (k : ℕ) (bound : k<7) : numeric μ (A.hub+k)=numeric input (A.hub+k) :=
    congrArg Fin.val (same _ (frame.hub ⟨k,bound⟩))
  have dst := (hub 6 (by decide)).trans whereOut
  have root (k : Fin (numeric μ (A.hub+3))) : numeric μ (numeric μ (A.hub+4)+4*k.val)+3<2^W := by
    let i : Fin (numeric input (A.hub+3)) := ⟨k.val,lt_of_lt_of_eq k.isLt (hub 3 (by decide))⟩
    let addr := numeric input (A.hub+4)+4*k.val
    have keep : addr<out ∨ out+4≤addr := frame.links i 0
    have p : numeric μ addr=numeric input addr := congrArg Fin.val (same _ keep)
    dsimp only [addr] at p
    rw [hub 4 (by decide),p]
    exact rootRoom i
  have fit := result_fits A cap W out (fun _=>0) (numeric μ) j dst hubRoom room capRoom
    ((μ (A.hub+3)).isLt) (by rw [hub 4 (by decide),hub 3 (by decide)];exact linkRoom) root
  have raw := closed_eval (result A cap) (numeric μ) (fun _=>out+j.val) fit
  have eq := result_value A cap W (fun _=>0) (numeric μ) j
  rw [dst,results_eq A cap μ input frame same] at eq
  rw [word_numeric μ,eq,idx,Fin.cast_val_eq_self] at raw
  rw [resultAt,dite_eq_left (show a.val-out<4 from j.isLt)]
  exact raw


namespace Tape
open DescriptorScan HistoryReadyTape HistoryJoinScan BitNetwork.Ordered BitLayout
variable {F : Type*} {n p h : ℕ} {arity : Fin n→ℕ}

def source (wire : ∀ i,Fin (arity i)→BitSource h p) (i : Fin n) (v : ℕ) :=
  if live : v<arity i then sourceAddress (wire i ⟨v,live⟩) else 0

def target (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (i : Fin n) (key : ℕ) : ℕ :=
  if live : key/4<(N i).cells then
    HistoryCompiledRows.metadata id (glue N wire) (finSigmaFinEquiv ⟨i,⟨key/4,live⟩⟩) ⟨key%4,Nat.mod_lt _ (by decide)⟩
  else 0

def jobs (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : Header ℕ) (i : Fin n) : List (Job W) :=
  [⟨q.pins,arity i,fun a => (source wire i (a-q.pins):Word W)⟩,
   ⟨q.dest,4*(N i).cells,fun a => (target N wire id i (a-q.dest):Word W)⟩]

def expr (W : ℕ) := HistorySelectedOps.rows (.literal (0:Word W) : Term W 0 4) []

/-- The three actual numeric controls that make a pin map in this procedure
are split-affine (8), copied physical addresses (10), and consecutive (11).
Both earlier child words and computed party addresses are resident arrays. -/
structure MapRow where
  op : ℕ
  arg : ℕ
  split : ℕ
  first : ℕ
  second : ℕ

def MapRow.reads (r : MapRow) (ctrl : Word W) (m : Memory W) (q : Header ℕ) :=
  let data : Fin 1→Word W := fun _ => ctrl
  let a := HistorySelectedOps.operandPointer (K:=0) data m
  HistorySelectedOps.tag (K:=0) data m=r.op ∧ a=(r.arg:Word W) ∧
    m a.val=(q.pins:Word W) ∧ m (a+2).val=(r.split:Word W) ∧
    (r.op=8→m (a+3).val=(r.first:Word W)) ∧ (r.op=8→m (a+4).val=(r.second:Word W))

def MapRow.value (r : MapRow) (m : Memory W) (x : ℕ) : Word W :=
  if r.op=8 then (HistoryPortMap.piecewise x r.split r.first r.second:Word W)
  else if r.op=10 then m (r.split+x) else ((r.split+x:ℕ):Word W)

theorem map_read (r : MapRow) (ctrl : Word W) (q : Header ℕ) (m : Memory W)
    (a : Word W) (x : ℕ) (key : a=((q.pins+x:ℕ):Word W)) (state : r.reads ctrl m q)
    (kind : r.op=8 ∨ r.op=10 ∨ r.op=11) (wide : 12≤2^W) (live : x<2^W)
    (bound : r.split<2^W) (copy : r.op = 10 → r.split + x < 2^W) :
    (expr W).eval (fun _ => ctrl) m (fun _=>a)=r.value m x := by
  obtain ⟨op,_,dest,split,a1,a2⟩ := state
  exact HistorySelectedOps.map_word (.literal 0 : Term W 0 4) [] (fun _=>ctrl) m (fun _=>a)
    r.op q.pins r.split r.first r.second x wide op kind dest split a1 a2 key live bound copy

/-- The real operand fetch and the retained child words at this position
in the chronological output. Its guessed pin-map interval is filled by
the preceding job, so it is derived in the proof. -/
theorem read_two (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : Header ℕ) (r : MapRow) (i : Fin n)
    (m : Memory W) (ctrl : Word W) (wide : 12≤2^W) (kind : r.op=8 ∨ r.op=10 ∨ r.op=11)
    (split : r.split<2^W) (mapRoom : q.pins+arity i≤2^W)
    (copyRoom : r.op = 10 → r.split + arity i ≤ 2^W)
    (apart : q.pins+arity i≤q.dest ∨ q.dest+4*(N i).cells≤q.pins)
    (cursor : ctrl.val<q.pins ∨ q.pins+arity i≤ctrl.val)
    (shape : q.oldPins=arity i ∧ q.newPins=p ∧ q.offset=h+∑ z : Fin i.val,(N (Fin.castLE i.isLt.le z)).internal)
    (srcRoom : q.source+4*(N i).cells≤2^W) (oldRoom : 2+q.oldPins<2^W)
    (mapReads : ∀ v : Memory W, agreesOutside q.pins (q.pins+arity i) v m →
      r.reads ctrl v q ∧ ∀ j : Fin (arity i), r.value v j.val=(sourceAddress (wire i j):Word W))
    (joinReads : ∀ v : Memory W, agreesOutside q.dest (q.dest+4*(N i).cells) v
      (HistoryJoinController.bumpMemory ctrl (fillSegment q.pins (arity i) (fun a=>(source wire i (a-q.pins):Word W)) m)) →
      HistorySelectedOps.tag (K:=0) (fun _=>ctrl) v=1 ∧
      fetch (HistorySelectedOps.operandPointer (K:=0) (fun _=>ctrl) v) v=q.words ∧
      HistoryCompiledRows.Records id (N i) q.source v)
    (small : ∀ row : Fin (N i).cells,∀ j : Fin 4,HistoryCompiledRows.metadata id (N i) row j<2^W) :
    readJobs (expr W) (fun _=>ctrl) ctrl (jobs N wire id q i) m := by
  constructor
  · intro a v lo hi same
    change q.pins ≤ a.val at lo
    change a.val<q.pins+arity i at hi
    let j : Fin (arity i) := ⟨a.val-q.pins,by omega⟩
    have addr : a=((q.pins+j.val:ℕ):Word W) := by
      rw [show q.pins+j.val=a.val by dsimp [j];omega,Fin.cast_val_eq_self]
    obtain ⟨state,values⟩ := mapReads v same
    have eq := map_read r ctrl q v a j.val addr state kind wide (by have := j.isLt;omega) split
      (by intro mode;have := copyRoom mode;have := j.isLt;omega)
    change _ = (source wire i j.val : Word W)
    exact eq.trans (by simpa [source,j.isLt] using values j)
  constructor
  · intro a v lo hi same
    change q.dest ≤ a.val at lo
    change a.val<q.dest+4*(N i).cells at hi
    let key := a.val-q.dest
    let row : Fin (N i).cells := ⟨key/4,by dsimp [key];omega⟩
    let col : Fin 4 := ⟨key%4,Nat.mod_lt _ (by decide)⟩
    have addr : a=((q.dest+(4*row.val+col.val):ℕ):Word W) := by
      rw [show 4*row.val+col.val=key from Nat.div_add_mod key 4,
        show q.dest+key=a.val by dsimp [key];omega,Fin.cast_val_eq_self]
    obtain ⟨tag,word,child⟩ := joinReads v same
    have pins (t : ℕ) (ok : t<q.oldPins) : v (q.pins+t)=(source wire i t:Word W) := by
      have inside : t<arity i := by rwa [shape.1] at ok
      have apartCtrl : q.pins+t≠ctrl.val := by omega
      have away : q.pins+t < q.dest ∨ q.dest+4*(N i).cells ≤ q.pins+t := by omega
      rw [same (q.pins+t) away]
      simp [HistoryJoinController.bumpMemory,writeMemory,apartCtrl,fillSegment,inside]
    have eq := HistorySelectedOps.copy_record (.literal 0 : Term W 0 4) [] (fun _=>ctrl) v (fun _=>a)
      N wire id q i row col (source wire i) wide tag word addr (by
        intro j;rw [HistoryCompiledRows.pin_address];simp [source,j.isLt])
      shape srcRoom (by rwa [shape.1]) oldRoom (small row col) child pins
    change _ = (target N wire id i key : Word W)
    have present : key / 4 < (N i).cells := row.isLt
    exact eq.trans (by simp only [target, dite_eq_left present]; rfl)
  · trivial

/-- The selected chronological tape consists of consecutive pairs for all
actual child ordinals, in the same order as the dependent row enumeration. -/
def tape (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : Fin n→Header ℕ) : List (Job W) :=
  (List.finRange n).flatMap fun i=>jobs N wire id (q i) i

theorem tape_length (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : Fin n→Header ℕ) :
    (tape (W:=W) N wire id q).length=2*n := by
  suffices ∀ xs : List (Fin n),(xs.flatMap (fun i=>jobs (W:=W) N wire id (q i) i)).length=2*xs.length by
    simpa [tape] using this (List.finRange n)
  intro xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    change 2 + 2 * xs.length = 2 * (xs.length + 1)
    omega

theorem tape_cost (k : ℕ) (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : Fin n→Header ℕ) :
    cost k (tape (W:=W) N wire id q)=6+38*n+
      ((List.finRange n).map (fun i=>arity i+4*(N i).cells)).sum*(2*k+4) := by
  suffices ∀ l : List (Fin n),cost k (l.flatMap fun i=>jobs (W:=W) N wire id (q i) i)=
      6+38*l.length+(l.map (fun i=>arity i+4*(N i).cells)).sum*(2*k+4) by
    simpa [tape] using this (List.finRange n)
  intro l
  induction l with
  | nil => simp [cost]
  | cons i l ih =>
    rw [List.flatMap_cons]
    change 19 + arity i * (2*k+4) + (19 + (4*(N i).cells) * (2*k+4) +
      cost k (l.flatMap (fun t => jobs (W:=W) N wire id (q t) t))) = _
    simp only [ih, List.length_cons, List.map_cons, List.sum_cons]
    ring

theorem offset_separate (N : ∀ i,BitNetwork F (arity i)) (q : Fin n→Header ℕ) (base : ℕ)
    (ord : ∀ i,(q i).dest=base+4*Diagonal.HistoryContraction.Tree.before (fun j=>(N j).cells) i)
    (i j : Fin n) (diff : i≠j) (r : Fin (N i).cells) (c : Fin 4) :
    (q i).dest+(4*r.val+c.val)<(q j).dest ∨
      (q j).dest+4*(N j).cells≤(q i).dest+(4*r.val+c.val) := by
  rw [ord,ord]
  rcases lt_or_gt_of_ne diff with lt|lt
  · have hs := Diagonal.HistoryContraction.Tree.before_end_le (fun j=>(N j).cells) lt
    have := r.isLt;have := c.isLt;omega
  · have hs := Diagonal.HistoryContraction.Tree.before_end_le (fun j=>(N j).cells) lt
    omega

theorem records (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : Fin n→Header ℕ) (base : ℕ) (ctrl : Word W) (m : Memory W)
    (ord : ∀ i,(q i).dest=base+4*Diagonal.HistoryContraction.Tree.before (fun j=>(N j).cells) i)
    (maps : ∀ i j,(q j).pins+arity j≤(q i).dest ∨ (q i).dest+4*(N i).cells≤(q j).pins)
    (fresh : ∀ i,ctrl.val<(q i).dest ∨ (q i).dest+4*(N i).cells≤ctrl.val) :
    HistoryCompiledRows.Records id (glue N wire) base (after ctrl (tape N wire id q) m) := by
  apply HistoryCompiledRows.records_of_intervals N wire id
  intro i r c
  rw [←ord]
  let a := (q i).dest+(4*r.val+c.val)
  have idx : (q i).dest≤a ∧ a<(q i).dest+4*(N i).cells := by
    have := r.isLt;have := c.isLt;dsimp [a];omega
  have ctl : a≠ctrl.val := by have := fresh i;omega
  have mem : i∈List.finRange n := List.mem_finRange i
  obtain ⟨before,tail,all,_⟩ := List.eq_append_cons_of_mem mem
  have no : i∉tail := by
    have nodup := List.nodup_finRange n
    rw [all,List.nodup_append] at nodup
    exact (List.nodup_cons.mp nodup.2.1).1
  let child := fun j => jobs (W:=W) N wire id (q j) j
  have far : ∀ z∈tail.flatMap child, a<z.start ∨ z.finish≤a := by
    intro z hz
    obtain ⟨j,hj,z'⟩ := List.mem_flatMap.mp hz
    have distinct : i≠j := by rintro rfl;exact no hj
    have dist := offset_separate N q base ord i j distinct r c
    have hm := maps i j
    simp only [child,jobs,List.mem_cons,List.not_mem_nil,or_false] at z'
    rcases z' with rfl|rfl
    · change a<(q j).pins ∨ (q j).pins+arity j≤a
      omega
    · exact dist
  change after ctrl ((List.finRange n).flatMap child) m a=_
  rw [all,List.flatMap_append,List.flatMap_cons,after_append,after_append,after_away _ _ _ _ ctl far]
  simp only [child,jobs,HistoryReadyTape.after,HistoryJoinController.bumpMemory,writeMemory,ite_eq_right ctl,fillSegment,
    ite_eq_left idx,target]
  have div : (4*r.val+c.val)/4=r.val := by rw [Nat.mul_add_div (by decide),Nat.div_eq_of_lt c.isLt,Nat.add_zero]
  have mod : (4*r.val+c.val)%4=c.val := by rw [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt c.isLt]
  simp [a,div,mod,r.isLt]


end Tape

/-- Concrete native memories after the bounded map/copy generator. Each
phase writes its own rectangular bank. The constructed pipeline consumes
only generated rows and the earlier children resident at the selected site. -/
structure Build (W : ℕ) where
  layout : Layout
  hub : Hub
  cap : ℕ
  input : Memory W

namespace Build
variable (B : Build W)

def seeded := fillSegment B.layout.seed 9
  (fun a => if h : a-B.layout.seed<9 then (bootWords B.layout (numeric B.input) ⟨a-B.layout.seed,h⟩:Word W) else 0) B.input

def commands := fillSegment B.layout.commands (14*B.hub.argc)
  (tableWord true B.hub (numeric B.seeded) B.layout.commands) B.seeded

def entered := fillSegment B.hub.arguments (7*B.hub.argc)
  (tableWord false B.hub (numeric B.commands) B.hub.arguments) B.commands

def control : Word W := ((B.layout.seed+7:ℕ):Word W)
def reached (ops : List (HistoryReadyTape.Job W)) := HistoryReadyTape.after B.control ops B.entered
def outputBase := numeric B.input (B.layout.hub+6)

def output (ops : List (HistoryReadyTape.Job W)) :=
  fillSegment B.outputBase 4 (resultAt B.layout B.cap (numeric (B.reached ops)) B.outputBase) (B.reached ops)

def ticks (ops : List (HistoryReadyTape.Job W)) :=
  ((4+9*(2*(HeaderScan.closed (w:=W) (boot B.layout)).binds+4))+
   (13+14*B.hub.argc*(2*(generator W B.layout B.cap true).binds+4))+
   (13+7*B.hub.argc*(2*(generator W B.layout B.cap false).binds+4)))+
   (HistoryReadyTape.cost (Tape.expr W).binds ops+13+4*(2*(HeaderScan.closed (w:=W) (result B.layout B.cap)).binds+4))

/-- Operand and word bounds consumed by the five concrete native loops.
No construction supplies a desired output state or arbitrary executing
program. All reads are from the three actual generated memory images. -/
structure Source (B : Build W) (ops : List (HistoryReadyTape.Job W)) : Prop where
  cap : B.hub.argc≤B.cap
  seedRoom : B.layout.seed+9<2^W
  hubRoom : B.layout.hub+7<2^W
  seedApart : B.layout.hub+7≤B.layout.seed ∨ B.layout.seed+9≤B.layout.hub
  order : B.layout.seed+9≤B.layout.commands ∧ B.layout.commands+14*B.hub.argc≤B.hub.arguments
  commandRoom : B.layout.commands+14*B.hub.argc<2^W
  argumentsRoom : B.hub.arguments+7*B.hub.argc<2^W
  origin : ∀ j : Fin 6, numeric B.input (B.layout.hub+j.val)=B.hub.words j
  stableHub : ∀ j : Fin 6,numeric B.seeded (B.layout.hub+j.val)=B.hub.words j ∧
    numeric B.commands (B.layout.hub+j.val)=B.hub.words j
  commandSources : Frame B.layout B.hub B.seeded B.layout.commands (14*B.hub.argc)
  argumentSources : Frame B.layout B.hub B.commands B.hub.arguments (7*B.hub.argc)
  small : 14<2^W
  capRoom : B.cap≤2^W
  linkRoom : B.hub.children+4*B.hub.argc≤2^W
  rootRoom : ∀ i : Fin B.hub.argc,(child B.hub (numeric B.seeded) i.val).node+3<2^W ∧
    (child B.hub (numeric B.commands) i.val).node+3<2^W
  count : ops.length=2*B.hub.argc
  frame : HistoryReadyTape.Away B.layout.seed 9 ops ∧
    HistoryReadyTape.Away B.layout.commands (14*B.hub.argc) ops
  limits : ∀ j∈ops,j.finish<2^W
  bounds : HistoryReadyTape.Loaded B.layout.commands ops B.entered
  resultRoom : B.outputBase+4<2^W
  resultSources : Frame B.layout (readHub B.layout (numeric (B.reached ops))) (B.reached ops) B.outputBase 4
  resultAddress : numeric (B.reached ops) (B.layout.hub+6)=B.outputBase
  resultLinks : let m := numeric (B.reached ops)
    m (B.layout.hub+4)+4*m (B.layout.hub+3)≤2^W
  resultRoots : let m := numeric (B.reached ops)
    ∀ k : Fin (m (B.layout.hub+3)),m (m (B.layout.hub+4)+4*k.val)+3<2^W


theorem seeded_word (j : Fin 9) : B.seeded (B.layout.seed+j.val)=
    (bootWords B.layout (numeric B.input) j:Word W) := by
  have := j.isLt
  simp [seeded,fillSegment,show B.layout.seed+j.val<B.layout.seed+9 by omega,j.isLt]

theorem entered_word (ops : List (HistoryReadyTape.Job W)) (s : Source B ops) (j : Fin 9) :
    B.entered (B.layout.seed+j.val)=B.seeded (B.layout.seed+j.val) := by
  obtain ⟨ds,da⟩ := s.order
  have := j.isLt
  simp [entered,commands,fillSegment,show ¬B.hub.arguments≤B.layout.seed+j.val by omega,
    show ¬B.layout.commands≤B.layout.seed+j.val by omega]

theorem procedure_exec (ops : List (HistoryReadyTape.Job W)) (s : Source B ops)
    (reads : HistoryReadyTape.readJobs (Tape.expr W) (fun _=>B.control) B.control ops B.entered) :
    (procedure W B.layout B.cap).Exec B.input (B.output ops) (B.ticks ops) := by
  let addr := (B.layout.seed : Word W)
  have first : (PhysicalInputPhases.writing (HeaderScan.closed (boot B.layout)) Fin.elim0 B.layout.seed 9).Exec
      B.input B.seeded (4+9*(2*(HeaderScan.closed (w:=W) (boot B.layout)).binds+4)) :=
    boot_exec B.layout B.input s.seedRoom s.hubRoom s.seedApart
  have cnt := s.origin (3:Fin 6)
  have arg := s.origin (5:Fin 6)
  change numeric B.input (B.layout.hub+3)=B.hub.argc at cnt
  change numeric B.input (B.layout.hub+5)=B.hub.arguments at arg
  have boot (j : Fin 8) (mem : Memory W) (hz : mem B.layout.seed=B.seeded B.layout.seed)
      (hj : mem (B.layout.seed+1+j.val)=B.seeded (B.layout.seed+1+j.val)) :
      HeaderScan.headerWord mem (B.layout.seed:Word W) j.val=
        (bootWords B.layout (numeric B.input) ⟨1+j.val,by omega⟩:Word W) := by
    have z := B.seeded_word (0:Fin 9)
    change B.seeded (B.layout.seed+0)=((B.layout.seed+1:ℕ):Word W) at z
    simp only [Nat.add_zero] at z
    rw [HeaderScan.headerWord,Fin.val_cast_of_lt (by have := s.seedRoom;omega),hz,z,←Nat.cast_add,
      Fin.val_cast_of_lt (by have := j.isLt;have := s.seedRoom;omega),hj]
    simpa [Nat.add_assoc] using B.seeded_word ⟨1+j.val,by omega⟩
  have seed (j : Fin 8) := boot j B.seeded rfl rfl
  have cmd (j : Fin 8) : HeaderScan.headerWord B.commands (B.layout.seed:Word W) j.val=
      (bootWords B.layout (numeric B.input) ⟨1+j.val,by omega⟩:Word W) := by
    apply boot
    all_goals have := j.isLt;have h := s.order.1; simp [commands,fillSegment,
      show ¬B.layout.commands≤B.layout.seed by omega,
      show ¬B.layout.commands≤B.layout.seed+1+j.val by omega]
  have c : (HeaderScan.procedure addr 0 1 (generator W B.layout B.cap true)).Exec B.seeded B.commands
      (13+14*B.hub.argc*(2*(generator W B.layout B.cap true).binds+4)) := table_exec B.layout B.hub B.cap true B.seeded (fun j=>(s.stableHub j).1)
    s.cap (by have := s.hubRoom;omega) B.layout.commands 0 rfl
    (by simpa [bootWords,cnt] using seed 0) (by simpa [bootWords,cnt,rowWidth] using seed 1)
    s.commandRoom s.commandSources s.small s.capRoom s.linkRoom (fun i=>(s.rootRoom i).1)
    (by have := s.hubRoom;omega)
  have a : (HeaderScan.procedure addr 2 3 (generator W B.layout B.cap false)).Exec B.commands B.entered
      (13+7*B.hub.argc*(2*(generator W B.layout B.cap false).binds+4)) := table_exec B.layout B.hub B.cap false B.commands (fun j=>(s.stableHub j).2)
    s.cap (by have := s.hubRoom;omega) B.hub.arguments 2 rfl
    (by simpa [bootWords,arg] using cmd 2) (by simpa [bootWords,cnt,rowWidth] using cmd 3)
    s.argumentsRoom s.argumentSources s.small s.capRoom s.linkRoom (fun i=>(s.rootRoom i).2)
    (by have := s.hubRoom;omega)
  have ctrlVal : B.control.val=B.layout.seed+7 := Fin.val_cast_of_lt (by have := s.seedRoom;omega)
  have stop : (B.control+1).val=B.layout.seed+8 := by
    change (((B.layout.seed+7:ℕ):Word W)+1).val=_
    rw [←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt (by have := s.seedRoom;omega)]
  have tape : (HistoryReadyTape.execute (Tape.expr W) (Fin.last 0) (fun _=>B.control)).Exec
      B.entered (B.reached ops) (HistoryReadyTape.cost (Tape.expr W).binds ops) := by
    have current : B.entered (B.layout.seed+7) = (B.layout.commands : Word W) :=
      (B.entered_word ops s (7 : Fin 9)).trans (B.seeded_word 7)
    have limit : B.entered (B.layout.seed+8) = ((B.layout.commands+14*B.hub.argc:ℕ) : Word W) := by
      have h := (B.entered_word ops s (8 : Fin 9)).trans (B.seeded_word 8)
      change B.entered (B.layout.seed+8) =
        ((B.layout.commands+14*numeric B.input (B.layout.hub+3):ℕ) : Word W) at h
      simpa only [cnt] using h
    have lengthAt : 7*ops.length=14*B.hub.argc := by rw [s.count]; omega
    intro P R K M pc reg pub exit installed params cfg m start init
    subst m
    exact HistoryReadyTape.execute_spec (Tape.expr W) (Fin.last 0) (fun _=>B.control)
      (fun m=>m=B.entered) ops B.layout.commands
      (by rw [ctrlVal]; have := s.order.1; omega)
      (by rw [lengthAt]; exact s.commandRoom)
      (by intro j hj;have h := s.frame.1 j hj;change _ ≤ B.control.val ∨ B.control.val+2 ≤ _;rw [ctrlVal];omega)
      (by rw [lengthAt]; exact s.frame.2)
      s.limits (by
        rintro _ rfl
        exact ⟨by rw [ctrlVal]; exact current,
          by rw [stop,lengthAt]; exact limit,s.bounds,reads⟩)
      M pc reg pub exit installed params cfg B.entered start rfl
  have keep (j : Fin 9) (no : B.layout.seed+j.val≠B.control.val) :
      B.reached ops (B.layout.seed+j.val)=B.seeded (B.layout.seed+j.val) := by
    rw [reached,HistoryReadyTape.after_away _ _ _ _ no (by
      intro x hx; have hj := j.isLt;have h := s.frame.1 x hx;omega),B.entered_word ops s j]
  have fin (j : Fin 8) (nj : j.val≠6) : HeaderScan.headerWord (B.reached ops) (B.layout.seed:Word W) j.val =
      (bootWords B.layout (numeric B.input) ⟨1+j.val,by omega⟩:Word W) := by
    apply boot
    · simpa using keep 0 (by rw [ctrlVal];omega)
    · simpa [Nat.add_assoc] using keep ⟨1+j.val,by omega⟩ (by rw [ctrlVal];dsimp;omega)
  have save : (HeaderScan.procedure addr 4 5 (HeaderScan.closed (result B.layout B.cap))).Exec
      (B.reached ops) (B.output ops) (13+4*(2*(HeaderScan.closed (w:=W) (result B.layout B.cap)).binds+4)) :=
    result_exec B.layout B.cap B.outputBase (B.reached ops) s.resultAddress
    (by simpa [bootWords,outputBase] using fin 4 (by decide))
    (by simpa [bootWords] using fin 5 (by decide))
    s.resultRoom s.hubRoom s.capRoom s.resultLinks s.resultRoots s.resultSources
  rw [ticks, Nat.add_assoc (HistoryReadyTape.cost (Tape.expr W).binds ops) 13]
  intro P R K M pc reg pub exit installed params cfg m start input
  exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then first c) a)
    (Procedure.Exec.then tape save) M pc reg pub exit installed params cfg m start input


open BitNetwork.Ordered HistoryJoinScan HistoryReadyTape BitLayout

variable {F : Type*} {n h p : ℕ} {arity : Fin n→ℕ}
variable (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : Fin n→Header ℕ) (row : Fin n→Tape.MapRow)

def «prefix» (xs : List (Fin n)) := after B.control
  (xs.flatMap (fun i=>Tape.jobs N wire id (q i) i)) B.entered

theorem command_word (i : Fin B.hub.argc) (side : Bool) (j : Fin 7)
    (apart : B.layout.commands+14*B.hub.argc≤B.hub.arguments ∨
      B.hub.arguments+7*B.hub.argc≤B.layout.commands) :
    B.entered (B.layout.commands+(14*i.val+7*side.toNat+j.val))=
      (command B.hub (numeric B.seeded) i.val side j:Word W) := by
  let a := B.layout.commands+(14*i.val+7*side.toNat+j.val)
  have ir := i.isLt
  have jr := j.isLt
  have pos : B.layout.commands≤a ∧ a<B.layout.commands+14*B.hub.argc := by
    cases side <;> dsimp [a] <;> omega
  have outside : ¬ (B.hub.arguments≤a ∧ a<B.hub.arguments+7*B.hub.argc) := by omega
  change B.entered a=_
  simp only [entered,commands,fillSegment,ite_eq_right outside,ite_eq_left pos]
  cases side <;> simp [tableWord,dataWord,rowWidth,a,
    show (14*i.val+j.val)/14=i.val by omega,show (14*i.val+j.val)%14=j.val by omega,
    show (14*i.val+7+j.val)/14=i.val by omega,show (14*i.val+7+j.val)%14=7+j.val by omega,
    show (7+j.val)%7=j.val by omega,Nat.mod_eq_of_lt j.isLt,show ¬7≤j.val by omega]

theorem argument_word (i : Fin B.hub.argc) (j : Fin 7) :
    B.entered (B.hub.arguments+(7*i.val+j.val)) =
      (arguments B.hub (numeric B.commands) i.val j:Word W) := by
  have hi := i.isLt
  have hj := j.isLt
  simp [entered,fillSegment,tableWord,dataWord,rowWidth,
    show B.hub.arguments+(7*i.val+j.val)<B.hub.arguments+7*B.hub.argc by omega,
    show (7*i.val+j.val)/7=i.val by omega,show (7*i.val+j.val)%7=j.val by omega,
    Nat.mod_eq_of_lt j.isLt]

theorem result_word (ops : List (Job W)) (j : Fin 4) :
    B.output ops (B.outputBase+j.val) =
      (resultWords B.layout B.cap (numeric (B.reached ops)) j:Word W) := by
  have hj := j.isLt
  simp [output,fillSegment,resultAt,j.isLt]

/-- The native final four-word publication of any bounded physical join.
The inputs are the actual retained command hub and its typed child root words. -/
theorem result_info (ops : List (Job W)) (cap : n≤B.cap) (stream pins shared : ℕ)
    (header : let raw:=numeric (B.reached ops)
      raw B.layout.hub=stream ∧ raw (B.layout.hub+1)=pins ∧ raw (B.layout.hub+2)=shared ∧ raw (B.layout.hub+3)=n)
    (childWords : ∀ i : Fin n,let raw:=numeric (B.reached ops)
      let root:=raw (raw (B.layout.hub+4)+4*i.val)
      raw (root+2)=(N i).cells ∧ raw (root+3)=(N i).internal) (j : Fin 4) :
    B.output ops (B.outputBase+j.val)=
      ((HistoryBoundedJoin.Info.mk stream pins (∑ i,(N i).cells) (shared+∑ i,(N i).internal)).words j:Word W) := by
  let raw:=numeric (B.reached ops)
  let root (i : ℕ):=raw (raw (B.layout.hub+4)+4*i)
  have amount (t : ℕ) (f : Fin n→ℕ) (rows : ∀ i : Fin n,raw (root i.val+t)=f i) :
      (∑ k∈Finset.range B.cap,if k<raw (B.layout.hub+3) then raw (root k+t) else 0)=∑ i,f i := by
    have arityAt : raw (B.layout.hub+3)=n := header.2.2.2
    rw [arityAt]
    have subset : Finset.range n⊆Finset.range B.cap := Finset.range_mono cap
    let g := fun k=> if k<n then raw (root k+t) else 0
    have eqn := Finset.sum_subset (f:=g) subset (by
      intro i hi h
      have out : ¬i<n := by simpa using h
      simp [g,out])
    calc
      _=∑ k∈Finset.range n,g k := eqn.symm
      _=∑ i,f i := by
        rw [←Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i _
        simpa [g,i.isLt] using rows i
  have r := amount 2 (fun i=>(N i).cells) (fun i=>(childWords i).1)
  have h := amount 3 (fun i=>(N i).internal) (fun i=>(childWords i).2)
  rw [B.result_word]
  apply congrArg Nat.cast
  change resultWords B.layout B.cap raw j=_
  fin_cases j <;> first | exact header.1 | exact header.2.1 | exact r | exact congrArg₂ Nat.add header.2.2.1 h

private theorem pair_at {α : Type*} (g : α→List (Job W)) (size : ∀ a,(g a).length=2)
    (l : List α) (i : Fin l.length) (u : Fin 2) :
    (l.flatMap g)[2*i.val+u.val]?=(g (l.get i))[u.val]? := by
  induction l with
  | nil => exact i.elim0
  | cons a l ih =>
    refine Fin.cases ?_ (fun j=>?_) i
    · simp [List.flatMap_cons,List.getElem?_append_left (show u.val<(g a).length by rw [size];exact u.isLt)]
    · have ix : 2*j.succ.val+u.val=(g a).length+(2*j.val+u.val) := by rw [size];simp;omega
      simpa only [List.flatMap_cons,ix,List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left,List.get_cons_succ'] using ih j

theorem loaded (size : n=B.hub.argc)
    (apart : B.layout.commands+14*B.hub.argc≤B.hub.arguments ∨
      B.hub.arguments+7*B.hub.argc≤B.layout.commands)
    (mapStart : ∀ i : Fin n,command B.hub (numeric B.seeded) i.val false 1=(q i).pins)
    (mapEnd : ∀ i : Fin n,command B.hub (numeric B.seeded) i.val false 6=(q i).pins+arity i)
    (joinStart : ∀ i : Fin n,command B.hub (numeric B.seeded) i.val true 1=(q i).dest)
    (joinEnd : ∀ i : Fin n,command B.hub (numeric B.seeded) i.val true 6=(q i).dest+4*(N i).cells) :
    Loaded B.layout.commands (Tape.tape N wire id q) B.entered := by
  intro a
  have sz : a.val < 2*n :=
    lt_of_lt_of_eq a.isLt (Tape.tape_length (W:=W) N wire id q)
  let i : Fin n := ⟨a.val/2,by omega⟩
  let u : Fin 2 := ⟨a.val%2,by omega⟩
  have address : 2*i.val+u.val=a.val := Nat.div_add_mod a.val 2
  let g := fun j => Tape.jobs (W:=W) N wire id (q j) j
  let ti : Fin (List.finRange n).length := ⟨i.val,by simp⟩
  have self : (List.finRange n).get ti=i := by simp [ti,List.get_eq_getElem]
  have e := pair_at g (fun _=>rfl) (List.finRange n) ti u
  change ((List.finRange n).flatMap g)[2*i.val+u.val]?=_ at e
  have ui : u.val<(g i).length := u.isLt
  rw [self,address] at e
  change (Tape.tape (W:=W) N wire id q)[a.val]? = (g i)[u.val]? at e
  rw [List.getElem?_eq_getElem a.isLt,List.getElem?_eq_getElem ui] at e
  have selected : (Tape.tape (W:=W) N wire id q).get a=(g i).get ⟨u.val,ui⟩ := Option.some.inj e
  rw [selected]
  have dispatch (col : Fin 7) : B.entered (B.layout.commands+7*a.val+col.val)=
      (command B.hub (numeric B.seeded) i.val (decide (1≤u.val)) col:Word W) := by
    have binary (j : Fin 2) : 7*(decide (1≤j.val)).toNat=7*j.val := by
      fin_cases j <;> rfl
    have addr : B.layout.commands+7*a.val+col.val =
        B.layout.commands+(14*i.val+7*(decide (1≤u.val)).toNat+col.val) := by
      rw [binary u]
      omega
    rw [addr]
    simpa only [Fin.val_cast] using B.command_word (i.cast size) (decide (1≤u.val)) col apart
  obtain eq|eq : u.val=0 ∨ u.val=1 := by have := u.isLt;omega
  · simpa [g,Tape.jobs,eq,mapStart,mapEnd,Job.finish] using And.intro (dispatch 1) (dispatch 6)
  · simpa [g,Tape.jobs,eq,joinStart,joinEnd,Job.finish] using And.intro (dispatch 1) (dispatch 6)

/-- A word remains readable throughout a join when its address is apart
from the cursor word, the pin maps and the output row intervals. -/
def protectedAt (a : ℕ) := a≠B.control.val ∧ ∀ i : Fin n,
  (a<(q i).pins ∨ (q i).pins+arity i≤a) ∧
  (a<(q i).dest ∨ (q i).dest+4*(N i).cells≤a)

private theorem apart_job (x : ℕ) (frozen : B.protectedAt N q x)
    (i : Fin n) (job : Job W) (mem : job∈Tape.jobs N wire id (q i) i) :
    x<job.start ∨ job.finish≤x := by
  rcases (by simpa only [Tape.jobs,List.mem_cons,List.not_mem_nil,or_false] using mem :
    job=⟨(q i).pins,arity i,_⟩ ∨ job=⟨(q i).dest,4*(N i).cells,_⟩) with rfl|rfl
  · exact (frozen.2 i).1
  · exact (frozen.2 i).2

theorem prefix_keeps (xs : List (Fin n)) {x : ℕ} (frozen : B.protectedAt N q x) :
    B.prefix N wire id q xs x=B.entered x := by
  apply after_away _ _ _ _ frozen.1
  intro z hz
  obtain ⟨i,_,h⟩ := List.mem_flatMap.mp hz
  exact B.apart_job N wire id q x frozen i z h

theorem prefix_position (xs : List (Fin n)) (i : Fin n) (ys : List (Fin n))
    (order : List.finRange n=xs++i::ys) (initial : B.entered B.control.val=(B.layout.commands:Word W))
    (apart : ∀ i : Fin n,(B.control.val<(q i).pins ∨ (q i).pins+arity i≤B.control.val) ∧
      (B.control.val<(q i).dest ∨ (q i).dest+4*(N i).cells≤B.control.val)) :
    B.prefix N wire id q xs B.control.val=((B.layout.commands+14*i.val:ℕ):Word W) := by
  have l : ∀ ts : List (Fin n),
      (ts.flatMap fun j=>Tape.jobs (W:=W) N wire id (q j) j).length=2*ts.length := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih => rw [List.flatMap_cons,List.length_append,ih];change 2+2*ts.length=2*(ts.length+1);omega
  have rank := HistoryPartyTapeRun.before_index order
  unfold «prefix»
  rw [HistoryPartyTapeRun.cursor_after,initial,l,rank,←Nat.cast_add]
  · congr 1;ring
  · intro z hz
    obtain ⟨j,_,in'⟩ := List.mem_flatMap.mp hz
    rcases (by simpa only [Tape.jobs,List.mem_cons,List.not_mem_nil,or_false] using in' :
      z=⟨(q j).pins,arity j,_⟩ ∨ z=⟨(q j).dest,4*(N j).cells,_⟩) with rfl|rfl
    · exact (apart j).1
    · exact (apart j).2

theorem map_keeps (xs : List (Fin n)) (i : Fin n) (m : Memory W)
    (frame : DescriptorScan.agreesOutside (q i).pins ((q i).pins+arity i) m (B.prefix N wire id q xs))
    {x : ℕ} (frozen : B.protectedAt N q x) : m x=B.entered x :=
  (frame x (frozen.2 i).1).trans (B.prefix_keeps N wire id q xs frozen)

theorem copied_keeps (xs : List (Fin n)) (i : Fin n) (m : Memory W)
    (frame : DescriptorScan.agreesOutside (q i).dest ((q i).dest+4*(N i).cells) m
      (HistoryJoinController.bumpMemory B.control (fillSegment (q i).pins (arity i)
        (fun a=>(Tape.source wire i (a-(q i).pins):Word W)) (B.prefix N wire id q xs))))
    {x : ℕ} (frozen : B.protectedAt N q x) : m x=B.entered x := by
  have miss : ¬ ((q i).pins≤x ∧ x<(q i).pins+arity i) := by have := (frozen.2 i).1;omega
  rw [frame x (frozen.2 i).2]
  simp only [HistoryJoinController.bumpMemory,writeMemory,ite_eq_right frozen.1,fillSegment,ite_eq_right miss,
    B.prefix_keeps N wire id q xs frozen]

theorem command_at (size : n=B.hub.argc) (i : Fin n) (join : Bool) (mem : Memory W)
    (cursor : mem B.control.val=((B.layout.commands+(14*i.val+7*join.toNat):ℕ):Word W))
    (stable : ∀ j : Fin 7,mem (B.layout.commands+(14*i.val+7*join.toNat+j.val))=
      B.entered (B.layout.commands+(14*i.val+7*join.toNat+j.val)))
    (space : B.layout.commands+14*n≤2^W)
    (apart : B.layout.commands+14*B.hub.argc≤B.hub.arguments ∨ B.hub.arguments+7*B.hub.argc≤B.layout.commands)
    (tagRoom : command B.hub (numeric B.seeded) i.val join 2<2^W) :
    HistorySelectedOps.operandPointer (K:=0) (fun _=>B.control) mem=(command B.hub (numeric B.seeded) i.val join 0:Word W) ∧
    HistorySelectedOps.tag (K:=0) (fun _=>B.control) mem=command B.hub (numeric B.seeded) i.val join 2 := by
  let start := B.layout.commands+(14*i.val+7*join.toNat)
  have room (j : Fin 7) : start+j.val<2^W := by have hi := i.isLt;have hj := j.isLt;cases join <;> dsimp [start] <;> omega
  have read (j : Fin 7) : mem (start+j.val)=(command B.hub (numeric B.seeded) i.val join j:Word W) := by
    simpa [start,Nat.add_assoc] using (stable j).trans (B.command_word (i.cast size) join j apart)
  have z := read (0:Fin 7)
  have t : mem (start+2) = (command B.hub (numeric B.seeded) i.val join 2 : Word W) := read (2:Fin 7)
  change mem (mem B.control.val).val=_ ∧ (mem (mem B.control.val+2).val).val=_
  rw [cursor]
  change mem (start:Word W).val=_ ∧ (mem ((start:Word W)+2).val).val=_
  rw [Fin.val_cast_of_lt (by simpa using room 0),show (start:Word W)+2=((start+2:ℕ):Word W) by push_cast;rfl,
    Fin.val_cast_of_lt (by simpa using room 2)]
  exact ⟨by simpa using z,by rw [t,Fin.val_cast_of_lt tagRoom]⟩

/-- The pin-map opcode, its actual operands, and the retained tensor words at a
child. The prefix is the computed memory after all preceding child operations. -/
structure Resident (B : Build W) (N : ∀ i,BitNetwork F (arity i))
    (wire : ∀ i,Fin (arity i)→BitSource h p) (id : ((Fin 3→Bool)→F)→ℕ)
    (q : Fin n→Header ℕ) (row : Fin n→Tape.MapRow) (base : ℕ) : Prop where
  wide : 12≤2^W
  kind : ∀ i,(row i).op=8 ∨ (row i).op=10 ∨ (row i).op=11
  split : ∀ i,(row i).split<2^W
  room : ∀ i,(q i).pins+arity i≤2^W
  incoming : ∀ i,(row i).op=10→(row i).split+arity i≤2^W
  maps : ∀ i j,(q j).pins+arity j≤(q i).dest ∨ (q i).dest+4*(N i).cells≤(q j).pins
  cursorPins : ∀ i,B.control.val<(q i).pins ∨ (q i).pins+arity i≤B.control.val
  cursorRows : ∀ i,B.control.val<(q i).dest ∨ (q i).dest+4*(N i).cells≤B.control.val
  src : ∀ i,(q i).source+4*(N i).cells≤2^W
  width : ∀ i,2+(q i).oldPins<2^W
  shape : ∀ i,(q i).oldPins=arity i ∧ (q i).newPins=p ∧
    (q i).offset=h+∑ z : Fin i.val,(N (Fin.castLE i.isLt.le z)).internal
  order : ∀ i,(q i).dest=base+4*Diagonal.HistoryContraction.Tree.before (fun j=>(N j).cells) i
  map : ∀ xs i ys,List.finRange n=xs++i::ys → ∀ v : Memory W,
    DescriptorScan.agreesOutside (q i).pins ((q i).pins+arity i) v (B.prefix N wire id q xs) →
    (row i).reads B.control v (q i) ∧ ∀ j : Fin (arity i),(row i).value v j.val=(sourceAddress (wire i j):Word W)
  child : ∀ xs i ys,List.finRange n=xs++i::ys → ∀ v : Memory W,
    DescriptorScan.agreesOutside (q i).dest ((q i).dest+4*(N i).cells) v
      (HistoryJoinController.bumpMemory B.control (fillSegment (q i).pins (arity i)
        (fun a=>(Tape.source wire i (a-(q i).pins):Word W)) (B.prefix N wire id q xs))) →
    HistorySelectedOps.tag (K:=0) (fun _=>B.control) v=1 ∧
      fetch (HistorySelectedOps.operandPointer (K:=0) (fun _=>B.control) v) v=(q i).words ∧
      HistoryCompiledRows.Records id (N i) (q i).source v
  small : ∀ i r c,HistoryCompiledRows.metadata id (N i) r c<2^W
  outputAway : B.outputBase+4≤base ∨ base+4*(glue N wire).cells≤B.outputBase

/-- The words read by the bounded map and copy loops, in the actual memory
just after writing the command and argument banks. These static observations
also cover the roots and the per-party source arrays of an enclosing join. -/
structure Banks (B : Build W) (N : ∀ i,BitNetwork F (arity i))
    (wire : ∀ i,Fin (arity i)→BitSource h p) (id : ((Fin 3→Bool)→F)→ℕ)
    (q : Fin n→Header ℕ) (row : Fin n→Tape.MapRow) : Prop where
  size : n=B.hub.argc
  cursor : B.entered B.control.val=(B.layout.commands:Word W)
  controlRoom : B.layout.commands+14*n≤2^W
  order : B.layout.commands+14*B.hub.argc≤B.hub.arguments ∨ B.hub.arguments+7*B.hub.argc≤B.layout.commands
  commandSafe : ∀ i : Fin n,∀ side : Bool,∀ j : Fin 7,
    B.protectedAt N q (B.layout.commands+(14*i.val+7*side.toNat+j.val))
  opcode : ∀ i : Fin n,command B.hub (numeric B.seeded) i.val false 2=(row i).op
  operand : ∀ i : Fin n,command B.hub (numeric B.seeded) i.val false 0=(row i).arg
  mapRoom : ∀ i,(row i).arg+4<2^W
  mapSafe : ∀ i,∀ j : Fin 5,j.val<3 ∨ (row i).op=8 → B.protectedAt N q ((row i).arg+j.val)
  mapWord : ∀ i,∀ j : Fin 5,j.val<3 ∨ (row i).op=8 → B.entered ((row i).arg+j.val)=
    (![ (q i).pins,arity i,(row i).split,(row i).first,(row i).second] j:ℕ)
  resolve : ∀ i,∀ j : Fin (arity i),(row i).value B.entered j.val=(sourceAddress (wire i j):Word W)
  copySafe : ∀ i,(row i).op=10→∀ j : Fin (arity i),B.protectedAt N q ((row i).split+j.val)
  argRoom : B.hub.arguments+7*n≤2^W
  argSafe : ∀ i : Fin n,∀ j : Fin 6,B.protectedAt N q (B.hub.arguments+(7*i.val+j.val))
  argWord : ∀ i : Fin n,∀ j : Fin 6,arguments B.hub (numeric B.commands) i.val (j.castSucc)=
    (![(q i).source,(q i).dest,(q i).pins,(q i).oldPins,(q i).newPins,(q i).offset] j)
  childSafe : ∀ i,∀ r : Fin (N i).cells,∀ j : Fin 4,B.protectedAt N q ((q i).source+(4*r.val+j.val))
  childRows : ∀ i,HistoryCompiledRows.Records id (N i) (q i).source B.entered

private theorem at_word {mem : Memory W} (b j : ℕ) (fit : b+j<2^W) :
    mem ((b:Word W)+(j:Word W)).val=mem (b+j) := by rw [←Nat.cast_add,Fin.val_cast_of_lt fit]

theorem Banks.map_at (M : Banks B N wire id q row) (i : Fin n) (mem : Memory W)
    (opRoom : (row i).op<2^W) (cursor : mem B.control.val=((B.layout.commands+14*i.val:ℕ):Word W))
    (frame : ∀ a,B.protectedAt N q a → mem a=B.entered a) :
    (row i).reads B.control mem (q i) ∧ ∀ j : Fin (arity i),(row i).value mem j.val=(sourceAddress (wire i j):Word W) := by
  have cmd := B.command_at M.size i false mem (by simpa using cursor)
    (fun j=>frame _ (M.commandSafe i false j)) M.controlRoom M.order ((M.opcode i) ▸ opRoom)
  rw [M.opcode,M.operand] at cmd
  have entry (j : Fin 5) (used : j.val<3 ∨ (row i).op=8) :
      mem (((row i).arg:Word W)+(j.val:Word W)).val =
        (![(q i).pins,arity i,(row i).split,(row i).first,(row i).second] j:ℕ) := by
    rw [at_word (mem := mem) (row i).arg j.val (by have := M.mapRoom i;have := j.isLt;omega),
      frame _ (M.mapSafe i j used), M.mapWord i j used]
  constructor
  · refine ⟨cmd.2,cmd.1,?_,?_,fun h8=>?_,fun h8=>?_⟩
    all_goals rw [cmd.1]
    · simpa using entry 0 (Or.inl (by decide))
    · exact entry 2 (Or.inl (by decide))
    · exact entry 3 (Or.inr h8)
    · exact entry 4 (Or.inr h8)
  · intro j
    rw [←M.resolve i j]
    by_cases h8 : (row i).op=8
    · simp [Tape.MapRow.value,h8]
    by_cases h10 : (row i).op=10
    · simp [Tape.MapRow.value,h10,frame _ (M.copySafe i h10 j)]
    · simp [Tape.MapRow.value,h8,h10]

theorem Banks.join_at (M : Banks B N wire id q row) (i : Fin n) (mem : Memory W) (wide : 12≤2^W)
    (cursor : mem B.control.val=((B.layout.commands+(14*i.val+7):ℕ):Word W))
    (frame : ∀ a,B.protectedAt N q a → mem a=B.entered a) :
    HistorySelectedOps.tag (K:=0) (fun _=>B.control) mem=1 ∧
      fetch (HistorySelectedOps.operandPointer (K:=0) (fun _=>B.control) mem) mem=(q i).words ∧
      HistoryCompiledRows.Records id (N i) (q i).source mem := by
  have cmd := B.command_at M.size i true mem (by simpa using cursor)
    (fun j=>frame _ (M.commandSafe i true j)) M.controlRoom M.order
    (by change 1<2^W;omega)
  change _=((B.hub.arguments+7*i.val:ℕ):Word W) ∧ _=1 at cmd
  refine ⟨cmd.2,?_,?_⟩
  · rw [cmd.1]
    have fields (j : Fin 6) : mem (((B.hub.arguments+7*i.val:ℕ):Word W)+(j.val:Word W)).val =
        (![(q i).source,(q i).dest,(q i).pins,(q i).oldPins,(q i).newPins,(q i).offset] j:ℕ) := by
      rw [at_word (mem := mem) (B.hub.arguments+7*i.val) j.val
            (by have := M.argRoom;have := i.isLt;have := j.isLt;omega),Nat.add_assoc,
        frame _ (M.argSafe i j)]
      exact (B.argument_word (i.cast M.size) j.castSucc).trans (congrArg Nat.cast (M.argWord i j))
    unfold fetch Header.words
    congr 1
    · exact fields 0
    · exact fields 1
    · exact fields 2
    · exact fields 3
    · exact fields 4
    · exact fields 5
  · intro r j
    exact (frame _ (M.childSafe i r j)).trans (M.childRows i r j)

theorem resident_of_banks (M : Banks B N wire id q row) (base : ℕ) (wide : 12≤2^W)
    (kind : ∀ i,(row i).op=8 ∨ (row i).op=10 ∨ (row i).op=11)
    (split : ∀ i,(row i).split<2^W) (room : ∀ i,(q i).pins+arity i≤2^W)
    (incoming : ∀ i,(row i).op=10→(row i).split+arity i≤2^W)
    (maps : ∀ i j,(q j).pins+arity j≤(q i).dest ∨ (q i).dest+4*(N i).cells≤(q j).pins)
    (cursorPins : ∀ i,B.control.val<(q i).pins ∨ (q i).pins+arity i≤B.control.val)
    (cursorRows : ∀ i,B.control.val<(q i).dest ∨ (q i).dest+4*(N i).cells≤B.control.val)
    (src : ∀ i,(q i).source+4*(N i).cells≤2^W) (width : ∀ i,2+(q i).oldPins<2^W)
    (shape : ∀ i,(q i).oldPins=arity i ∧ (q i).newPins=p ∧ (q i).offset=h+∑ z : Fin i.val,(N (Fin.castLE i.isLt.le z)).internal)
    (order : ∀ i,(q i).dest=base+4*Diagonal.HistoryContraction.Tree.before (fun j=>(N j).cells) i)
    (small : ∀ i r c,HistoryCompiledRows.metadata id (N i) r c<2^W)
    (outputAway : B.outputBase+4≤base ∨ base+4*(glue N wire).cells≤B.outputBase) :
    Resident B N wire id q row base := by
  refine ⟨wide,kind,split,room,incoming,maps,cursorPins,cursorRows,src,width,shape,order,?_,?_,small,outputAway⟩
  · intro xs i ys all mem frame
    have cursor := B.prefix_position N wire id q xs i ys all M.cursor (fun j=>⟨cursorPins j,cursorRows j⟩)
    apply Banks.map_at B N wire id q row M i mem
    · rcases kind i with v|v|v <;> omega
    · rw [frame _ (cursorPins i),cursor]
    · exact fun a ok=>B.map_keeps N wire id q xs i mem frame ok
  · intro xs i ys all mem frame
    have cursor := B.prefix_position N wire id q xs i ys all M.cursor (fun j=>⟨cursorPins j,cursorRows j⟩)
    apply Banks.join_at B N wire id q row M i mem wide
    · rw [frame _ (cursorRows i)]
      have outside : ¬((q i).pins≤B.control.val ∧ B.control.val<(q i).pins+arity i) := by
        have := cursorPins i
        omega
      simp [HistoryJoinController.bumpMemory,writeMemory,fillSegment,outside,cursor,Nat.cast_add,add_assoc]
    · exact fun a ok=>B.copied_keeps N wire id q xs i mem frame ok

/-- All four words of every assembled gate occur in the actual final output
memory of the native bounded join. -/
theorem complete (base : ℕ) (source : Source B (Tape.tape N wire id q))
    (live : Resident B N wire id q row base) :
    let ops := Tape.tape N wire id q
    (procedure W B.layout B.cap).Exec B.input (B.output ops) (B.ticks ops) ∧
      HistoryCompiledRows.Records id (glue N wire) base (B.output ops) := by
  let ops := Tape.tape (W:=W) N wire id q
  have reads : readJobs (Tape.expr W) (fun _=>B.control) B.control ops B.entered := by
    apply read_children
    intro xs i ys all
    exact Tape.read_two N wire id (q i) (row i) i _ B.control live.wide (live.kind i) (live.split i)
      (live.room i) (live.incoming i) (live.maps i i) (live.cursorPins i) (live.shape i)
      (live.src i) (live.width i) (live.map xs i ys all) (live.child xs i ys all) (live.small i)
  refine ⟨B.procedure_exec ops source reads,?_⟩
  have stored := Tape.records N wire id q base B.control B.entered live.order live.maps live.cursorRows
  intro r c
  have hr := r.isLt
  have hc := c.isLt
  have apart := live.outputAway
  have bound : ¬ (B.outputBase≤base+(4*r.val+c.val) ∧ base+(4*r.val+c.val)<B.outputBase+4) := by omega
  simpa only [output,fillSegment,ite_eq_right bound,reached,ops] using stored r c



end Build


end ThreeFlat.RAM.HistoryBoundedBody

end OAI
