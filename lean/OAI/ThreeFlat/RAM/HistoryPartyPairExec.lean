import OAI.ThreeFlat.RAM.HistoryPartyPair
import OAI.ThreeFlat.Diagonal.HistoryPartyTrees

namespace OAI
/-! # Execution of the two batch and pair-join stages of a physical party -/

namespace ThreeFlat.RAM.HistoryPartyPairExec

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure DescriptorScan
open HistoryPartyBatch HistoryPartyBatchExec HistoryBoundedJoin HistoryJoinScan BitLayout
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree
open scoped Fin.CommRing BigOperators

noncomputable section

variable {w a b : ℕ} {F : Type*} [CommRing F]

def header (A : Layout) (n a b : ℕ) : Hub :=
  ⟨HistoryPartyPair.atPair A n 0,a+b,0,2,HistoryPartyPair.hub A+7,A.arguments⟩

def link (A : Layout) (n a : ℕ) : Fin 2 → Child :=
  ![⟨dest A true n 1,A.maps,8,HistoryPartyPair.hub A+15⟩,
    ⟨dest A false n 1,A.maps+a,8,HistoryPartyPair.hub A+20⟩]

def rows (A : Layout) (a b : ℕ) : Fin 2 → HistoryBoundedBody.Tape.MapRow :=
  ![⟨8,HistoryPartyPair.hub A+15,a,2,0⟩,⟨8,HistoryPartyPair.hub A+20,b,2+a,0⟩]

def mapOperands (A : Layout) (a b : ℕ) : Fin 2 → Fin 5 → ℕ :=
  ![![A.maps,a,a,2,0],![A.maps+a,b,b,2+a,0]]

omit [CommRing F] in
theorem map_value (A : Layout) (L : Tree F a) (R : Tree F b) (m : Memory w)
    (i : Fin 2) (j : Fin (pairArity L R i)) :
    ((rows A a b i).value m j.val)=(sourceAddress (pairWire L R i j):Word w) := by
  fin_cases i
  · change (HistoryPortMap.piecewise j.val a 2 0:Word w)=((2+j.val:ℕ):Word w)
    exact congrArg (fun x : ℕ => (x : Word w)) (ite_eq_left j.isLt)
  · change (HistoryPortMap.piecewise j.val b (2+a) 0:Word w)=((2+(a+j.val):ℕ):Word w)
    have inside : j.val < b := j.isLt
    rw [HistoryPortMap.piecewise,ite_eq_left inside,Nat.add_assoc]

/-- The published stream follows the batch's leaf staging rows in bank zero. -/
def copyHeader (A : Layout) (n : ℕ) (L : Tree F a) (R : Tree F b) (i : Fin 2) : Header ℕ :=
  ⟨dest A (decide (i=0)) n 0+4*(pairNetwork L R i).cells,HistoryPartyPair.atPair A n 0+4*before (fun j=>(pairNetwork L R j).cells) i,
    (link A n a i).map,pairArity L R i,a+b,before (fun j=>(pairNetwork L R j).internal) i⟩

def hubWord (A : Layout) (m : Memory w) (x : ℕ) : Word w :=
  if h : x-HistoryPartyPair.hub A<25 then
    (HistoryPartyPair.word A (numeric m) ⟨x-HistoryPartyPair.hub A,h⟩:Word w) else 0

def prepared (A : Layout) (m : Memory w) :=
  fillSegment (HistoryPartyPair.hub A) 25 (hubWord A m) m

theorem hub_read (A : Layout) (m : Memory w) (j : Fin 25) :
    prepared A m (HistoryPartyPair.hub A+j.val)=(HistoryPartyPair.word A (numeric m) j:Word w) := by
  simp [prepared,fillSegment,hubWord,j.isLt]

theorem prepared_outside (A : Layout) (m : Memory w) (x : ℕ)
    (outside : x<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤x) :
    prepared A m x=m x := by
  simp [prepared,fillSegment,show ¬(HistoryPartyPair.hub A≤x ∧ x<HistoryPartyPair.hub A+25) by omega]

def bootCost (A : Layout) (w : ℕ) := 4+25*(2*(HeaderScan.closed (w:=w) (HistoryPartyPair.formula A)).binds+4)

structure BootRoom (A : Layout) (m : Memory w) (n : ℕ) : Prop where
  cursor : A.cursor<2^w
  index : numeric m A.cursor-1=n
  width : HistoryPartyPair.hub A+25<2^w
  checks : dest A true n 1+1<2^w
  payload : dest A false n 1+1<2^w
  cursorAway : A.cursor<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤A.cursor
  checksAway : dest A true n 1+1<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤dest A true n 1+1
  payloadAway : dest A false n 1+1<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤dest A false n 1+1

private theorem pick_fits (a : Formula 1) (m : ℕ→ℕ) (v : Fin 1→ℕ) (xs : List (Formula 1)) (o : ℕ)
    (operand : a.Fits w (fun _=>0) m v) (width : a.natural w (fun _=>0) m v<2^w)
    (room : o+xs.length<2^w) (valid : ∀ e∈xs,e.Fits w (fun _=>0) m v) :
    (HistoryPartyPair.pick a o xs).Fits w (fun _=>0) m v := by
  induction xs generalizing o with
  | nil => trivial
  | cons x xs ih =>
    have r : o<2^w := by simp at room;omega
    change _ ∧ True ∧ _ ∧ o<2^w ∧ _
    refine ⟨operand,trivial,width,r,?_⟩
    split
    · exact valid _ (by simp)
    · exact ih (o+1) (by simp at room;omega) (fun e h=>valid e (List.mem_cons_of_mem _ h))

set_option maxRecDepth 6000 in
theorem boot_exec (A : Layout) (m : Memory w) (n : ℕ) (r : BootRoom A m n) :
    (PhysicalInputPhases.writing (HeaderScan.closed (HistoryPartyPair.formula A)) Fin.elim0
      (HistoryPartyPair.hub A) 25).Exec m (prepared A m) (bootCost A w) := by
  intro P R K machine pc reg pub exit installed params cfg input entry original
  subst input
  refine PhysicalInputPhases.writing_spec (HeaderScan.closed (HistoryPartyPair.formula A)) Fin.elim0
    (HistoryPartyPair.hub A) 25 r.width (fun v => v=m) (hubWord A m) ?_
    machine pc reg pub exit installed params cfg m entry rfl
  intro orig initial x μ low high frame
  subst orig
  let j : Fin 25 := ⟨x.val-HistoryPartyPair.hub A,by omega⟩
  have hx : HistoryPartyPair.hub A+j.val=x.val := Nat.add_sub_of_le low
  have cur : numeric μ A.cursor=numeric m A.cursor := congrArg Fin.val (frame _ r.cursorAway)
  have cl : numeric μ (dest A true n 1+1)=numeric m (dest A true n 1+1) := congrArg Fin.val (frame _ r.checksAway)
  have pr : numeric μ (dest A false n 1+1)=numeric m (dest A false n 1+1) := congrArg Fin.val (frame _ r.payloadAway)
  have row : HistoryPartyPair.word A (numeric μ) j=HistoryPartyPair.word A (numeric m) j := by
    unfold HistoryPartyPair.word
    rw [cur,r.index,cl,pr]
  have cmp : numeric μ A.cursor<2^w := (μ A.cursor).isLt
  have h : (HistoryPartyPair.formula A).Fits w (fun _=>0) (numeric μ) (fun _=>HistoryPartyPair.hub A+j.val) := by
    have hcu := r.cursor
    have hr := r.width
    have hcl := r.checks
    have hpr := r.payload
    have cur' : numeric μ A.cursor-1=n := by rw [cur,r.index]
    have one : 1<2^w := by omega
    let sec (family : ℕ) := HistoryScratch.sector A.motifs A.parties ⟨A.motif+2,A.party+2,family,1⟩
    change A.arena+(n*A.V+sec 1)*A.V+0+1<2^w at hcl
    change A.arena+(n*A.V+sec 0)*A.V+0+1<2^w at hpr
    unfold HistoryPartyPair.formula
    apply pick_fits
    · simp [Formula.Fits,Formula.natural];have := j.isLt;omega
    · simp [Formula.natural];have := j.isLt;omega
    · simp;omega
    · simp [Formula.Fits,Formula.natural,add,mul,natOp,opFits,cur',cmp,one,hcu,
        sec] at hcl hpr ⊢; omega

  have e := closed_eval (HistoryPartyPair.formula A) (numeric μ) (fun _=>HistoryPartyPair.hub A+j.val) h
  rw [word_numeric μ,HistoryPartyPair.value,row,hx,Fin.cast_val_eq_self] at e
  exact e.trans (by rw [←hx]; simp [hubWord,j.isLt])

/-- The three dynamic reads used by the party-pair header. -/
structure Children (A : Layout) (m : Memory w) (n a b : ℕ) : Prop where
  cursor : numeric m A.cursor-1=n
  left : numeric m (dest A true n 1+1)=a
  right : numeric m (dest A false n 1+1)=b

def fields (A : Layout) (n a b : ℕ) : Fin 25 → ℕ :=
  let h := HistoryPartyPair.hub A
  ![HistoryPartyPair.atPair A n 0,a+b,0,2,h+7,A.arguments,HistoryPartyPair.atPair A n 1,
    dest A true n 1,A.maps,8,h+15,dest A false n 1,A.maps+a,8,h+20,
    A.maps,a,a,2,0,A.maps+a,b,b,2+a,0]

theorem raw_fields (A : Layout) (m : Memory w) (n a b : ℕ) (c : Children A m n a b) :
    HistoryPartyPair.word A (numeric m)=fields A n a b := by
  simp [HistoryPartyPair.word,fields,c.cursor,c.left,c.right]

theorem stored_fields (A : Layout) (m : Memory w) (n a b : ℕ) (c : Children A m n a b)
    (j : Fin 25) (room : fields A n a b j<2^w) :
    numeric (prepared A m) (HistoryPartyPair.hub A+j.val)=fields A n a b j := by
  rw [numeric,hub_read,raw_fields A m n a b c,Fin.val_cast_of_lt room]

theorem stored_hub (A : Layout) (m : Memory w) (n a b : ℕ) (c : Children A m n a b)
    (room : ∀ j,fields A n a b j<2^w) (j : Fin 6) :
    numeric (prepared A m) (HistoryPartyPair.hub A+j.val)=(header A n a b).words j := by
  let k : Fin 25 := ⟨j.val,by have := j.isLt;omega⟩
  exact (stored_fields A m n a b c k (room k)).trans (by fin_cases j <;> rfl)

theorem stored_link (A : Layout) (m : Memory w) (n a b : ℕ) (c : Children A m n a b)
    (room : ∀ j,fields A n a b j<2^w) (i : Fin 2) (j : Fin 4) :
    numeric (prepared A m) ((header A n a b).children+4*i.val+j.val)=(link A n a i).words j := by
  let k : Fin 25 := ⟨7+4*i.val+j.val,by have := i.isLt;have := j.isLt;omega⟩
  have eq := stored_fields A m n a b c k (room k)
  have addr : (header A n a b).children+4*i.val+j.val=HistoryPartyPair.hub A+k.val := by
    dsimp [header,k];omega
  rw [addr,eq]
  fin_cases i <;> fin_cases j <;> rfl

theorem stored_operands (A : Layout) (m : Memory w) (n a b : ℕ) (c : Children A m n a b)
    (room : ∀ j,fields A n a b j<2^w) (i : Fin 2) (j : Fin 5) :
    numeric (prepared A m) ((rows A a b i).arg+j.val)=mapOperands A a b i j := by
  let k : Fin 25 := ⟨15+5*i.val+j.val,by have := i.isLt;have := j.isLt;omega⟩
  have eq := stored_fields A m n a b c k (room k)
  have addr : (rows A a b i).arg+j.val=HistoryPartyPair.hub A+k.val := by
    fin_cases i <;> simp [rows,k,Nat.add_assoc]
  rw [addr,eq]
  fin_cases i <;> fin_cases j <;> rfl

def build (A : Layout) (n a b : ℕ) (m : Memory w) : HistoryBoundedBody.Build w :=
  ⟨⟨HistoryPartyPair.hub A,A.seed,A.commands⟩,header A n a b,2,prepared A m⟩

variable (A : Layout) (n : ℕ) (L : Tree F a) (R : Tree F b) (id : ((Fin 3→Bool)→F)→ℕ)

def steps := HistoryBoundedBody.Tape.tape (W:=w) (pairNetwork L R) (pairWire L R) id (copyHeader A n L R)

omit [CommRing F] in
theorem shape (i : Fin 2) : (copyHeader A n L R i).oldPins=pairArity L R i ∧
    (copyHeader A n L R i).newPins=a+b ∧
    (copyHeader A n L R i).offset=0+∑ z : Fin i.val,(pairNetwork L R (Fin.castLE i.isLt.le z)).internal := by
  simp [copyHeader,before]

omit [CommRing F] in
theorem placed (i : Fin 2) : (copyHeader A n L R i).dest=
    HistoryPartyPair.atPair A n 0+4*before (fun j=>(pairNetwork L R j).cells) i := rfl

def childInfo (i : Fin 2) : Info :=
  ⟨(copyHeader A n L R i).source,pairArity L R i,(pairNetwork L R i).cells,(pairNetwork L R i).internal⟩

/-- Exactly the eight link words and eight earlier root words queried by the two-child generator. -/
structure InputRows (raw : ℕ→ℕ) : Prop where
  links : ∀ i : Fin 2, ∀ j : Fin 4,raw ((header A n a b).children+4*i.val+j.val)=(link A n a i).words j
  info : ∀ i : Fin 2, ∀ j : Fin 4,raw ((link A n a i).node+j.val)=(childInfo A n L R i).words j

omit [CommRing F] in
theorem loaded_child {raw : ℕ→ℕ} (r : InputRows A n L R raw) (i : Fin 2) :
    child (header A n a b) raw i.val=link A n a i := by
  have v := r.links i
  cases e : link A n a i with
  | mk loc maps op arg =>
    rw [e] at v
    let x := (header A n a b).children+4*i.val
    have h0 : raw x=loc := v 0
    have h1 : raw (x+1)=maps := v 1
    have h2 : raw (x+2)=op := v 2
    have h3 : raw (x+3)=arg := v 3
    change Child.mk (raw x) (raw (x+1)) (raw (x+2)) (raw (x+3))=_
    rw [h0,h1,h2,h3]

omit [CommRing F] in
theorem loaded_info {raw : ℕ→ℕ} (r : InputRows A n L R raw) (i : Fin 2) :
    read (child (header A n a b) raw i.val).node raw=childInfo A n L R i := by
  rw [loaded_child A n L R r]
  have v := r.info i
  cases e : childInfo A n L R i with
  | mk loc pins cells bits =>
    rw [e] at v
    have h0 : raw (link A n a i).node=loc := v 0
    have h1 : raw ((link A n a i).node+1)=pins := v 1
    have h2 : raw ((link A n a i).node+2)=cells := v 2
    have h3 : raw ((link A n a i).node+3)=bits := v 3
    simp only [HistoryBoundedJoin.read,h0,h1,h2,h3]

omit [CommRing F] in
theorem exact_commands {raw : ℕ→ℕ} (r : InputRows A n L R raw) (i : Fin 2) :
    let T := header A n a b
    let q := copyHeader A n L R i
    command T raw i.val false= ![(link A n a i).operand,q.pins,8,0,0,0,q.pins+pairArity L R i] ∧
    command T raw i.val true= ![A.arguments+7*i.val,q.dest,1,0,0,0,q.dest+4*(pairNetwork L R i).cells] ∧
    HistoryBoundedJoin.arguments T raw i.val=
      ![q.source,q.dest,q.pins,q.oldPins,q.newPins,q.offset,q.dest+4*(pairNetwork L R i).cells] := by
  have h := loaded_child A n L R r i
  have z : read (link A n a i).node raw=childInfo A n L R i := by
    simpa only [h] using loaded_info A n L R r i
  have ofst := moved_eq (pairNetwork L R) (pairWire L R) (header A n a b) raw i rfl (by
    intro j
    rw [loaded_info A n L R r j]
    rfl)
  simp only [command,HistoryBoundedJoin.arguments,ite_true,ite_false,ofst.1,ofst.2,h,z,Bool.false_eq_true]
  fin_cases i <;> simp [header,copyHeader,link,childInfo]

omit [CommRing F] in
theorem loaded (m : Memory w) (r : InputRows A n L R (numeric (build A n a b m).seeded))
    (sep : A.commands+28≤A.arguments ∨ A.arguments+14≤A.commands) :
    HistoryReadyTape.Loaded A.commands (steps (w:=w) A n L R id) (build A n a b m).entered := by
  apply (build A n a b m).loaded (pairNetwork L R) (pairWire L R) id (copyHeader A n L R) rfl sep
  · exact fun i => congrFun (exact_commands A n L R r i).1 (1 : Fin 7)
  · exact fun i => congrFun (exact_commands A n L R r i).1 (6 : Fin 7)
  · exact fun i => congrFun (exact_commands A n L R r i).2.1 (1 : Fin 7)
  · exact fun i => congrFun (exact_commands A n L R r i).2.1 (6 : Fin 7)

/-- The bounded gather's three initial scratch writes. -/
structure Outside (A : Layout) (x : ℕ) : Prop where
  seed : x<A.seed ∨ A.seed+9≤x
  commands : x<A.commands ∨ A.commands+28≤x
  arguments : x<A.arguments ∨ A.arguments+14≤x

theorem entered_keeps (m : Memory w) (x : ℕ) (o : Outside A x) :
    (build A n a b m).entered x=prepared A m x := by
  have s : ¬(A.seed≤x ∧ x<A.seed+9) := by have := o.seed;omega
  have c : ¬(A.commands≤x ∧ x<A.commands+28) := by have := o.commands;omega
  have z : ¬(A.arguments≤x ∧ x<A.arguments+14) := by have := o.arguments;omega
  simp [build,header,HistoryBoundedBody.Build.entered,HistoryBoundedBody.Build.commands,
    HistoryBoundedBody.Build.seeded,fillSegment,s,c,z]

theorem operand_bank (m : Memory w) (c : Children A m n a b) (cap : ∀ j,fields A n a b j<2^w)
    (apart : ∀ (i : Fin 2) (j : Fin 5), Outside A ((rows A a b i).arg+j.val)) (i : Fin 2) (j : Fin 5) :
    (build A n a b m).entered ((rows A a b i).arg+j.val)=(mapOperands A a b i j:Word w) := by
  rw [entered_keeps (a:=a) (b:=b) A n m _ (apart i j)]
  exact Fin.ext (by
    have h := stored_operands A m n a b c cap i j
    have lt : mapOperands A a b i j<2^w := by rw [←h]; exact (prepared A m _).isLt
    simpa [numeric,Fin.val_cast_of_lt lt] using h)

omit [CommRing F] in
theorem child_bank (m : Memory w)
    (cl : HistoryCompiledRows.Records id L.compile (dest A true n 0+4*L.rows) m)
    (pr : HistoryCompiledRows.Records id R.compile (dest A false n 0+4*R.rows) m)
    (outside : ∀ (i : Fin 2) (k : Fin (pairNetwork L R i).cells) (j : Fin 4),
      let x := (copyHeader A n L R i).source+(4*k.val+j.val)
      Outside A x ∧ (x<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤x)) (i : Fin 2) :
    HistoryCompiledRows.Records id (pairNetwork L R i) (copyHeader A n L R i).source (build A n a b m).entered := by
  intro k j
  obtain ⟨f,h⟩ := outside i k j
  rw [entered_keeps (a:=a) (b:=b) A n m _ f,prepared_outside _ _ _ h]
  fin_cases i
  · change m ((dest A true n 0+4*L.compile.cells)+(4*k.val+j.val)) =
      (HistoryCompiledRows.metadata id L.compile k j : Word w)
    simpa only [compiled_rows] using cl k j
  · change m ((dest A false n 0+4*R.compile.cells)+(4*k.val+j.val)) =
      (HistoryCompiledRows.metadata id R.compile k j : Word w)
    simpa only [compiled_rows] using pr k j

omit [CommRing F] in
/-- A subsequent payload batch retains the already generated checks records in the first arena. -/
theorem checks_retained (X : HistoryPartyBatchExec.Build w) (jobs : List (HistoryReadyTape.Job w))
    (base : ℕ) (original : HistoryCompiledRows.Records id L.compile base X.input)
    (room : X.layout.seed+37<2^w)
    (apart : ∀ i : Fin L.compile.cells,∀ j : Fin 4,let x:=base+(4*i.val+j.val)
      x≠X.ctrl.val ∧ (x<X.layout.seed ∨ X.layout.seed+37≤x) ∧
      (x<X.layout.batch ∨ X.layout.batch+26≤x) ∧ (x<X.layout.commands ∨ X.layout.commands+21*X.count≤x) ∧
      (x<X.layout.arguments ∨ X.layout.arguments+23*X.count≤x) ∧
      (∀ J∈jobs,x<J.start ∨ J.finish≤x) ∧ (x<X.target ∨ X.target+4≤x)) :
    HistoryCompiledRows.Records id L.compile base (X.published jobs) := by
  intro i j
  obtain ⟨ctrl,s,b,c,a,ops,t⟩ := apart i j
  exact (X.published_outside jobs _ room ctrl s b c a ops t).trans (original i j)

/-- The four read-only ranges for the final gather, including the two earlier gate streams. -/
structure Frozen (m : Memory w) : Prop where
  command : ∀ (i : Fin 2) (side : Bool) (j : Fin 7),(build A n a b m).protectedAt
    (pairNetwork L R) (copyHeader A n L R) (A.commands+(14*i.val+7*side.toNat+j.val))
  operand : ∀ (i : Fin 2) (j : Fin 5),(build A n a b m).protectedAt
    (pairNetwork L R) (copyHeader A n L R) ((rows A a b i).arg+j.val)
  arguments : ∀ (i : Fin 2) (j : Fin 6),(build A n a b m).protectedAt
    (pairNetwork L R) (copyHeader A n L R) (A.arguments+(7*i.val+j.val))
  children : ∀ (i : Fin 2) (k : Fin (pairNetwork L R i).cells) (j : Fin 4),
    (build A n a b m).protectedAt (pairNetwork L R) (copyHeader A n L R)
      ((copyHeader A n L R i).source+(4*k.val+j.val))

omit [CommRing F] in
theorem banks (m : Memory w) (c : Children A m n a b) (cap : ∀ j,fields A n a b j<2^w)
    (source : (build A n a b m).Source (steps A n L R id))
    (u : InputRows A n L R (numeric (build A n a b m).seeded))
    (v : InputRows A n L R (numeric (build A n a b m).commands)) (f : Frozen A n L R m)
    (headerRoom : HistoryPartyPair.hub A+25<2^w)
    (apart : ∀ (i : Fin 2) (j : Fin 5),Outside A ((rows A a b i).arg+j.val))
    (children : ∀ i,HistoryCompiledRows.Records id (pairNetwork L R i) (copyHeader A n L R i).source
      (build A n a b m).entered) :
    (build A n a b m).Banks (pairNetwork L R) (pairWire L R) id (copyHeader A n L R) (rows A a b) := by
  let B := build A n a b m
  have disk (i : Fin 2) := exact_commands A n L R u i
  have args (i : Fin 2) := (exact_commands A n L R v i).2.2
  have equal (i : Fin 2) : (rows A a b i).op=8 := by fin_cases i <;> rfl
  have seedRoom : A.seed+9 < 2^w := source.seedRoom
  have ptr : B.control.val=A.seed+7 := by
    change ((A.seed+7 : ℕ) : Word w).val = A.seed+7
    exact Fin.val_cast_of_lt (by omega)
  refine ⟨rfl,?_,source.commandRoom.le,.inl source.order.2,f.command,?_,?_,?_,fun i j _=>f.operand i j,
    ?_,map_value A L R B.entered,?_,source.argumentsRoom.le,f.arguments,?_,f.children,children⟩
  · change B.entered B.control.val=_
    rw [ptr]
    exact (B.entered_word _ source 7).trans (B.seeded_word 7)
  · intro i
    exact (congrFun (disk i).1 2).trans (equal i).symm
  · intro i
    refine (congrFun (disk i).1 0).trans ?_
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> dsimp [rows] <;> omega
  · intro i j _
    rw [operand_bank (a:=a) (b:=b) A n m c cap apart i j]
    fin_cases i <;> fin_cases j <;> rfl
  · intro i h
    have := equal i
    omega
  · intro i j
    refine (congrFun (args i) j.castSucc).trans ?_
    fin_cases j <;> rfl

/-- Width and interval bounds on the two generated copy jobs. -/
structure Space (m : Memory w) : Prop where
  pins : ∀ i,(copyHeader A n L R i).pins+pairArity L R i≤2^w
  maps : ∀ i j,(copyHeader A n L R j).pins+pairArity L R j≤(copyHeader A n L R i).dest ∨
    (copyHeader A n L R i).dest+4*(pairNetwork L R i).cells≤(copyHeader A n L R j).pins
  cursorPins : ∀ i,(build A n a b m).control.val<(copyHeader A n L R i).pins ∨
    (copyHeader A n L R i).pins+pairArity L R i≤(build A n a b m).control.val
  cursorRows : ∀ i,(build A n a b m).control.val<(copyHeader A n L R i).dest ∨
    (copyHeader A n L R i).dest+4*(pairNetwork L R i).cells≤(build A n a b m).control.val
  src : ∀ i,(copyHeader A n L R i).source+4*(pairNetwork L R i).cells≤2^w
  width : ∀ i,2+(copyHeader A n L R i).oldPins<2^w
  small : ∀ i k j,HistoryCompiledRows.metadata id (pairNetwork L R i) k j<2^w
  stream : 4*(L.rows+R.rows)≤A.V

omit [CommRing F] in
theorem resident (m : Memory w) (c : Children A m n a b) (cap : ∀ j,fields A n a b j<2^w)
    (S : Space A n L R id m)
    (H : (build A n a b m).Banks (pairNetwork L R) (pairWire L R) id (copyHeader A n L R) (rows A a b)) :
    (build A n a b m).Resident (pairNetwork L R) (pairWire L R) id (copyHeader A n L R) (rows A a b)
      (HistoryPartyPair.atPair A n 0) := by
  let B := build A n a b m
  have equal (i : Fin 2) : (rows A a b i).op=8 := by fin_cases i <;> rfl
  have wide : 12≤2^w := by
    have h : HistoryPartyPair.hub A+20<2^w := cap 14
    omega
  refine B.resident_of_banks (pairNetwork L R) (pairWire L R) id (copyHeader A n L R) (rows A a b)
    H (HistoryPartyPair.atPair A n 0) wide (fun i=>.inl (equal i)) ?_ S.pins ?_
    S.maps S.cursorPins S.cursorRows S.src S.width (shape A n L R) (placed A n L R) S.small ?_
  · intro i
    have eq : (rows A a b i).split=(copyHeader A n L R i).oldPins := by fin_cases i <;> rfl
    rw [eq]
    have := S.width i
    omega
  · intro i h
    have := equal i
    omega
  · right
    have same : B.outputBase=HistoryPartyPair.atPair A n 1 := stored_fields A m n a b c 6 (cap 6)
    rw [same]
    have off : HistoryPartyPair.atPair A n 1=HistoryPartyPair.atPair A n 0+A.V := by
      unfold HistoryPartyPair.atPair HistoryScratch.atWord HistoryScratch.sector
      ring
    rw [off,Nat.add_le_add_iff_left]
    change 4*(∑ i : Fin 2,(pairNetwork L R i).cells)≤A.V
    rw [Fin.sum_univ_two]
    change 4*(L.compile.cells+R.compile.cells)≤A.V
    simpa only [compiled_rows] using S.stream

/-- All addresses retained between the pair-header write and the final root write. -/
structure Retained (m : Memory w) (x : ℕ) : Prop where
  seed : x<A.seed ∨ A.seed+9≤x
  commands : x<A.commands ∨ A.commands+28≤x
  arguments : x<A.arguments ∨ A.arguments+14≤x
  cursor : x≠(build A n a b m).control.val
  jobs : ∀ J∈steps (w:=w) A n L R id,x<J.start ∨ J.finish≤x

omit [CommRing F] in
theorem keep (m : Memory w) (x : ℕ) (f : Retained A n L R id m x) :
    (build A n a b m).reached (steps A n L R id) x=prepared A m x := by
  let B := build A n a b m
  have h := HistoryReadyTape.after_away B.control (steps A n L R id) B.entered x f.cursor f.jobs
  have s : ¬(A.seed≤x ∧ x<A.seed+9) := by have := f.seed;omega
  have c : ¬(A.commands≤x ∧ x<A.commands+28) := by have := f.commands;omega
  have a : ¬(A.arguments≤x ∧ x<A.arguments+14) := by have := f.arguments;omega
  exact h.trans (by simp [B,build,header,HistoryBoundedBody.Build.entered,HistoryBoundedBody.Build.commands,
    HistoryBoundedBody.Build.seeded,fillSegment,s,c,a])

omit [CommRing F] in
theorem pair_info (m : Memory w) (c : Children A m n a b)
    (cap : ∀ j,fields A n a b j<2^w)
    (stay : ∀ j : Fin 25,Retained A n L R id m (HistoryPartyPair.hub A+j.val))
    (roots : ∀ (i : Fin 2) (j : Fin 4), Retained A n L R id m ((link A n a i).node+j.val))
    (off : ∀ (i : Fin 2) (j : Fin 4), let x := (link A n a i).node+j.val
      x<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤x)
    (left : ∀ j : Fin 4, numeric m (dest A true n 1+j.val)=(Info.words ⟨dest A true n 0+4*L.rows,a,L.rows,L.bits⟩ j))
    (right : ∀ j : Fin 4, numeric m (dest A false n 1+j.val)=(Info.words ⟨dest A false n 0+4*R.rows,b,R.rows,R.bits⟩ j))
    (j : Fin 4) :
    let B := build A n a b m
    B.output (steps A n L R id) (HistoryPartyPair.atPair A n 1+j.val) =
      (Info.words ⟨HistoryPartyPair.atPair A n 0,a+b,L.rows+R.rows,L.bits+R.bits⟩ j:Word w) := by
  let B := build A n a b m
  let ops := steps (w:=w) A n L R id
  let raw := numeric (B.reached ops)
  have hub (k : Fin 25) : raw (HistoryPartyPair.hub A+k.val)=fields A n a b k := by
    exact (congrArg Fin.val (keep A n L R id m _ (stay k))).trans (stored_fields A m n a b c k (cap k))
  have info (i : Fin 2) (k : Fin 4) :
      raw ((link A n a i).node+k.val)=numeric m ((link A n a i).node+k.val) :=
    congrArg Fin.val ((keep A n L R id m _ (roots i k)).trans (prepared_outside _ _ _ (off i k)))
  have l (k : Fin 4) := (info 0 k).trans (left k)
  have r (k : Fin 4) := (info 1 k).trans (right k)
  have out : B.outputBase=HistoryPartyPair.atPair A n 1 := stored_fields A m n a b c 6 (cap 6)
  change B.output ops _=_
  rw [←out,B.result_word]
  change ((HistoryBoundedBody.resultWords ⟨HistoryPartyPair.hub A,A.seed,A.commands⟩ 2 raw j : ℕ):Word w)=_
  have h0 : raw (HistoryPartyPair.hub A)=HistoryPartyPair.atPair A n 0 := hub 0
  have h1 : raw (HistoryPartyPair.hub A+1)=a+b := hub 1
  have h2 : raw (HistoryPartyPair.hub A+2)=0 := hub 2
  have h3 : raw (HistoryPartyPair.hub A+3)=2 := hub 3
  have h4 : raw (HistoryPartyPair.hub A+4)=HistoryPartyPair.hub A+7 := hub 4
  have hl : raw (HistoryPartyPair.hub A+7)=dest A true n 1 := hub 7
  have hr : raw (HistoryPartyPair.hub A+7+4)=dest A false n 1 := by
    rw [Nat.add_assoc]
    exact hub 11
  have lc : raw (dest A true n 1+2)=L.rows := l 2
  have rc : raw (dest A false n 1+2)=R.rows := r 2
  have lb : raw (dest A true n 1+3)=L.bits := l 3
  have rb : raw (dest A false n 1+3)=R.bits := r 3
  fin_cases j <;> simp [HistoryBoundedBody.resultWords,Info.words,Finset.sum_range_succ,h0,h1,h2,h3,h4,hl,hr,
    lc,rc,lb,rb]

/-- Fixed instruction costs of the two-child gather. -/
def setup (A : Layout) (w : ℕ) :=
  let q : HistoryBoundedBody.Layout := ⟨HistoryPartyPair.hub A,A.seed,A.commands⟩
  bootCost A w +
    ((4+9*(2*(HeaderScan.closed (w:=w) (HistoryBoundedBody.boot q)).binds+4))+
    (13+28*(2*(HistoryBoundedBody.generator w q 2 true).binds+4))+
    (13+14*(2*(HistoryBoundedBody.generator w q 2 false).binds+4)))+
    (82+13+4*(2*(HeaderScan.closed (w:=w) (HistoryBoundedBody.result q 2)).binds+4))

def overhead (A : Layout) (w : ℕ) := setup A w+(2*HistorySelectedOps.tariff []+4)

private theorem generator_binds (A B : HistoryBoundedBody.Layout) (w w' : ℕ) (cmd : Bool) :
    (HistoryBoundedBody.generator w A 2 cmd).binds =
      (HistoryBoundedBody.generator w' B 2 cmd).binds := by
  simp only [HistoryBoundedBody.generator, Term.binds_instantiate, HeaderScan.binds_closed]
  apply congrArg (fun sum => (HistoryBoundedJoin.formula 2 cmd).work + sum)
  apply Finset.sum_congr rfl
  intro i _
  by_cases z : i = 0 <;> by_cases f : i = 5 <;> cases cmd <;>
    simp only [z, f, ite_true, ite_false] <;> rfl

set_option maxRecDepth 6000 in
theorem overhead_eq (A A' : Layout) (w w' : ℕ) : overhead A w=overhead A' w' := by
  let q (L : Layout) : HistoryBoundedBody.Layout := ⟨HistoryPartyPair.hub L,L.seed,L.commands⟩
  have first : (HistoryPartyPair.formula A).work = (HistoryPartyPair.formula A').work := by
    simp only [HistoryPartyPair.formula, HistoryPartyPair.pick, eqz, add, mul, Formula.work]
  have seed : (HistoryBoundedBody.boot (q A)).work = (HistoryBoundedBody.boot (q A')).work := rfl
  have commands := generator_binds (q A) (q A') w w' true
  have arguments := generator_binds (q A) (q A') w w' false
  have result := HistoryBoundedBody.result_work (q A) (q A') 2
  dsimp only [q] at seed commands arguments result
  simp only [overhead, setup, bootCost, HeaderScan.binds_closed, first, seed,
    commands, arguments, result]

omit [CommRing F] in
theorem ticks_le (m : Memory w) :
    bootCost A w+(build A n a b m).ticks (steps A n L R id) ≤
    overhead A w*(1+a+b+4*(L.rows+R.rows)) := by
  let K := 2*(HistoryBoundedBody.Tape.expr w).binds+4
  have k : K≤2*HistorySelectedOps.tariff []+4 := by
    have h := HistorySelectedOps.rows_size_of w (.literal (0:Word w) : Term w 0 4)
      (by norm_num [Term.literal, Term.binds]) []
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 4
  have sum : ((List.finRange 2).map (fun i=>pairArity L R i+4*(pairNetwork L R i).cells)).sum=
      a+b+4*(L.rows+R.rows) := by
    rw [show List.finRange 2=[(0:Fin 2),1] by decide]
    change (a+4*L.compile.cells)+((b+4*R.compile.cells)+0)=_
    simp only [compiled_rows]
    omega
  let work := a+b+4*(L.rows+R.rows)
  have exactCost : bootCost A w+(build A n a b m).ticks (steps A n L R id) = setup A w+work*K := by
    unfold HistoryBoundedBody.Build.ticks steps
    rw [HistoryBoundedBody.Tape.tape_cost,sum]
    dsimp only [build,header,setup,work,K]
    omega
  have setup_le : setup A w ≤ overhead A w := Nat.le_add_right _ _
  have per_word : K ≤ overhead A w := k.trans (Nat.le_add_left _ _)
  calc
    _ = setup A w + work*K := exactCost
    _ ≤ overhead A w + work*overhead A w :=
      Nat.add_le_add setup_le (Nat.mul_le_mul_left work per_word)
    _ = _ := by
      rw [show 1+a+b+4*(L.rows+R.rows)=1+work by dsimp [work]; omega]
      ring

omit [CommRing F] in
/-- The exact party procedure first executes the two batch generators, then writes the
twenty-five real join fields, and finally copies both children with their generated pin maps. -/
theorem complete (input doneChecks donePayload : Memory w) (checksTicks payloadTicks : ℕ)
    (checks : (HistoryPartyBatch.procedure w A true).Exec input doneChecks checksTicks)
    (payload : (HistoryPartyBatch.procedure w A false).Exec doneChecks donePayload payloadTicks)
    (room : BootRoom A donePayload n)
    (source : (build A n a b donePayload).Source (steps A n L R id))
    (live : (build A n a b donePayload).Resident (pairNetwork L R) (pairWire L R) id (copyHeader A n L R)
      (rows A a b) (HistoryPartyPair.atPair A n 0)) :
    let B := build A n a b donePayload
    let ops := steps (w:=w) A n L R id
    (HistoryPartyPair.procedure w A).Exec input (B.output ops)
      (((checksTicks+payloadTicks)+bootCost A w)+B.ticks ops) ∧
    HistoryCompiledRows.Records id (pair L R).compile (HistoryPartyPair.atPair A n 0) (B.output ops) := by
  let B := build A n a b donePayload
  obtain ⟨execute,records⟩ := B.complete (pairNetwork L R) (pairWire L R) id (copyHeader A n L R)
    (rows A a b) (HistoryPartyPair.atPair A n 0) source live
  exact ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then checks payload)
    (boot_exec A donePayload n room)) execute, records⟩

omit [CommRing F] in
/-- The generated link fields address the two four-word roots retained from the batches. -/
theorem inputs_prepared (m : Memory w) (c : Children A m n a b)
    (cap : ∀ j, fields A n a b j < 2^w)
    (off : ∀ (i : Fin 2) (j : Fin 4), let x := (link A n a i).node+j.val
      x<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤x)
    (left : ∀ j : Fin 4, numeric m (dest A true n 1+j.val) =
      (Info.words ⟨dest A true n 0+4*L.rows,a,L.rows,L.bits⟩ j))
    (right : ∀ j : Fin 4, numeric m (dest A false n 1+j.val) =
      (Info.words ⟨dest A false n 0+4*R.rows,b,R.rows,R.bits⟩ j)) :
    InputRows A n L R (numeric (prepared A m)) := by
  refine ⟨stored_link A m n a b c cap, ?_⟩
  intro i j
  apply (congrArg Fin.val (prepared_outside A m _ (off i j))).trans
  fin_cases i
  · change numeric m (dest A true n 1+j.val) =
      Info.words ⟨dest A true n 0+4*L.compile.cells,a,L.compile.cells,L.compile.internal⟩ j
    simpa only [compiled_rows,compiled_bits] using left j
  · change numeric m (dest A false n 1+j.val) =
      Info.words ⟨dest A false n 0+4*R.compile.cells,b,R.compile.cells,R.compile.internal⟩ j
    simpa only [compiled_rows,compiled_bits] using right j

omit [CommRing F] in
private theorem inputs_fill (m : Memory w) (lo len : ℕ) (word : ℕ → Word w)
    (prior : InputRows A n L R (numeric m))
    (links : (header A n a b).children+8≤lo ∨ lo+len≤(header A n a b).children)
    (roots : ∀ i : Fin 2, (link A n a i).node+4≤lo ∨ lo+len≤(link A n a i).node) :
    InputRows A n L R (numeric (fillSegment lo len word m)) := by
  constructor
  · intro i j
    have outside : ¬(lo≤(header A n a b).children+4*i.val+j.val ∧
        (header A n a b).children+4*i.val+j.val<lo+len) := by
      have := i.isLt
      have := j.isLt
      omega
    simpa only [numeric,fillSegment,ite_eq_right outside] using prior.links i j
  · intro i j
    have outside : ¬(lo≤(link A n a i).node+j.val ∧ (link A n a i).node+j.val<lo+len) := by
      have := roots i
      have := j.isLt
      omega
    simpa only [numeric,fillSegment,ite_eq_right outside] using prior.info i j

omit [CommRing F] in
theorem inputs_seeded (m : Memory w) (prior : InputRows A n L R (numeric (prepared A m)))
    (links : (header A n a b).children+8≤A.seed ∨ A.seed+9≤(header A n a b).children)
    (roots : ∀ i : Fin 2, (link A n a i).node+4≤A.seed ∨ A.seed+9≤(link A n a i).node) :
    InputRows A n L R (numeric (build A n a b m).seeded) :=
  inputs_fill A n L R (prepared A m) A.seed 9 _ prior links roots

omit [CommRing F] in
theorem inputs_commands (m : Memory w) (prior : InputRows A n L R (numeric (build A n a b m).seeded))
    (links : (header A n a b).children+8≤A.commands ∨
      A.commands+28≤(header A n a b).children)
    (roots : ∀ i : Fin 2, (link A n a i).node+4≤A.commands ∨ A.commands+28≤(link A n a i).node) :
    InputRows A n L R (numeric (build A n a b m).commands) :=
  inputs_fill A n L R (build A n a b m).seeded A.commands 28 _ prior links roots


end
end ThreeFlat.RAM.HistoryPartyPairExec

end OAI
