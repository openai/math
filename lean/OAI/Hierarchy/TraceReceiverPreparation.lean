import OAI.Hierarchy.TraceReceiverAmounts
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.CountedProcedure

namespace OAI
/-! # Native preparation of the selected terminal task and prefix arrays -/
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open scoped Classical Fin.CommRing

variable {W : ℕ}

/-- Header scan extents are read from the selected root counter at runtime. -/
private def rangeWords (W head count width dst mul : ℕ) : Fin 7 → Term W 0 1 :=
  let n := Term.binary .mul (.literal mul) (.load (.literal count))
  ![.literal (head+1), .literal width, n, .literal (head+4), .literal 0,
    .literal dst, .binary .add n (.literal 1)]

private def pick (W start : ℕ) : List (Term W 0 1) → Term W 0 1
  | [] => .literal 0
  | x::xs => .select .eq (.result 0) (.literal start) x (pick W (start+1) xs)

def rangeSeed (W head count width dst mul : ℕ) : Procedure W :=
  PhysicalInputPhases.writing (pick W head (List.ofFn (rangeWords W head count width dst mul)))
    Fin.elim0 head 7

def rangeImage (head count width dst mul : ℕ) (m : Memory W) : Memory W :=
  fillSegment head 7 (fun a=>((rangeWords W head count width dst mul ⟨(a-head)%7,by omega⟩).eval
    Fin.elim0 m (fun _=>(a:Word W)))) m

private theorem pick_eval {terms : List (Term W 0 1)} (start : ℕ) (i : Fin terms.length)
    (fits : start+terms.length < 2^W) (m : Memory W) (a : Word W) (addr : a.val=start+i.val) :
    (pick W start terms).eval Fin.elim0 m (fun _=>a)=(terms.get i).eval Fin.elim0 m (fun _=>a) := by
  induction terms generalizing start with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    by_cases h : i.val=0
    · have eqn : a=(start:Word W) := Fin.ext (by rw [addr,h,Nat.add_zero,Fin.val_cast_of_lt (by omega)])
      have zi : i=⟨0,by simp⟩ := Fin.ext h
      simp [pick,Term.eval,Comparison.test,eqn,zi]
    · let j : Fin xs.length := ⟨i.val-1,by have := i.isLt; simp only [List.length_cons] at this;omega⟩
      have ii : i=j.succ := Fin.ext (by dsimp [j];omega)
      have ne : a≠(start:Word W) := fun eqn=>h (by
        have val := congrArg Fin.val eqn
        rw [addr,Fin.val_cast_of_lt (by omega)] at val
        omega)
      have hh := ih (start+1) j (by simp only [List.length_cons] at fits;omega)
        (by rw [addr];dsimp [j];omega)
      simpa [pick,Term.eval,Comparison.test,ne,ii] using hh

private theorem rangeWords_agree (head count width dst mul : ℕ) (m mem : Memory W) (a : Word W)
    (read : mem (count:Word W).val=m (count:Word W).val) (q : Fin 7) :
    ((rangeWords W head count width dst mul) q).eval Fin.elim0 mem (fun _=>a) =
      ((rangeWords W head count width dst mul) q).eval Fin.elim0 m (fun _=>a) := by
  change mem (count % 2^W) = m (count % 2^W) at read
  fin_cases q <;> simp [rangeWords,BinaryOp.eval,read]

theorem range_run (head count width dst mul : ℕ) (m : Memory W)
    (room : head+7 < 2^W) (off : (count:Word W).val < head ∨ head+7 ≤ (count:Word W).val) :
    (rangeSeed W head count width dst mul).Spec (·=m)
      (fun _ out=>out=rangeImage head count width dst mul m)
      (4+7*(2*(pick W head (List.ofFn (rangeWords W head count width dst mul))).binds+4)) := by
  let words (a : ℕ) := ((rangeWords W head count width dst mul ⟨(a-head)%7,by omega⟩).eval
    Fin.elim0 m (fun _=>(a:Word W)))
  intro P R K M pc reg pub exit installed data c start entry input
  subst start
  apply PhysicalInputPhases.writing_spec _ _ _ _ room (·=m) words ?_ M pc reg pub exit installed data c m entry rfl
  intro m' eqn a mem low high agree
  subst m'
  let t := rangeWords W head count width dst mul
  let j : Fin 7 := ⟨a.val-head,by omega⟩
  have idx : a.val=head+j.val := by dsimp [j];omega
  have r := pick_eval (terms:=List.ofFn t) head (Fin.cast (by simp) j) (by simpa) mem a idx
  rw [r]
  have av : (a.val : Word W)=a := Fin.cast_val_eq_self _
  have read := agree _ off
  dsimp only [words]
  rw [List.get_ofFn,av]
  let k : Fin 7 := ⟨(a.val-head)%7,Nat.mod_lt _ (by decide)⟩
  have kj : k=j := Fin.ext (Nat.mod_eq_of_lt (show a.val-head<7 by omega))
  change (t j).eval Fin.elim0 mem (fun _=>a)=(t k).eval Fin.elim0 m (fun _=>a)
  exact (rangeWords_agree head count width dst mul m mem a read j).trans
    (congrArg (fun q=>(t q).eval Fin.elim0 m (fun _=>a)) kj.symm)

theorem range_at (head count width dst mul : ℕ) (m : Memory W) (j : Fin 7) :
    rangeImage head count width dst mul m (head+j.val) =
      (![((head+1:ℕ):Word W),(width:Word W),(mul:Word W)*m (count:Word W).val,
        ((head+4:ℕ):Word W),0,(dst:Word W),(mul:Word W)*m (count:Word W).val+1] : Fin 7 → Word W) j := by
  have hit : head ≤ head+j.val ∧ head+j.val < head+7 := by have := j.isLt; omega
  simp only [rangeImage,fillSegment,ite_eq_left hit,Nat.add_sub_cancel_left,Nat.mod_eq_of_lt j.isLt]
  fin_cases j <;> simp [rangeWords,BinaryOp.eval,Nat.cast_add]

/-- One gathered S13 field and one exclusive prefix. The guessed value of
`edges` disappears from the executable, which reads both limits from RAM. -/
def column (W current count selected first results width dest cap : ℕ) (j : Fin 3) : Procedure W :=
  let x : TerminalWireArchive.Layout := ⟨current+3,0,0,0,cap,width,0,dest⟩
  ((rangeSeed W current count width dest 1).seq
    (amountScan W current width selected first results j)).seq
    (HeaderScan.procedure ((current+3:ℕ):Word W) 1 2 (HeaderScan.closed (TerminalWireArchive.prefixWord x)))

def prefixLayout (head cap width dest n : ℕ) : TerminalWireArchive.Layout :=
  ⟨head+3,0,0,0,cap,width,n,dest⟩

def columnImage (head count selected first results width dest cap n : ℕ) (j : Fin 3) (m : Memory W) :=
  let start := rangeImage head count width dest 1 m
  TerminalWireArchive.image (prefixLayout head cap width dest n)
    (amountImage width selected first results n j start)

private theorem compose {a b : Procedure W} {m z out : Memory W} {left right : ℕ}
    (first : a.Spec (·=m) (fun _ v=>v=z) left)
    (second : b.Spec (·=z) (fun _ v=>v=out) right) :
    (a.seq b).Spec (·=m) (fun _ v=>v=out) (left+right) :=
  Procedure.Spec.mono (A:=a.seq b) (first.seq second (fun _ _ h=>h))
    (fun _ h=>h) (fun _ _ h=>h.choose_spec.2) le_rfl

/-- The static seed, the dynamic S13 sweep and its exclusive prefix really
run in sequence at the selected count stored by the receiver. -/
theorem column_run (head count selected first results width dest cap n : ℕ) (j : Fin 3) (m : Memory W)
    (space : TerminalWireArchive.Bounds (prefixLayout head cap width dest n) W)
    (headBelow : head+7 ≤ width) (headFit : head+7 < 2^W)
    (counter : (m (count:Word W).val).val=n)
    (cn : (count:Word W).val < head ∨ head+7 ≤ (count:Word W).val)
    (selection : selected+n ≤ width) (headWord : first < width)
    (rows : ∀ i : Fin n,let start:=rangeImage head count width dest 1 m
      let a := (amountAddress selected first results j start (i.val:Word W)).val
      a < width ∨ width+n ≤ a)
    (tables : ∀ i < n,width+i < dest ∨ dest+n < width+i) :
    let e := pick W head (List.ofFn (rangeWords W head count width dest 1))
    let x := prefixLayout head cap width dest n
    (column W head count selected first results width dest cap j).Spec (·=m)
      (fun _ z=>z=columnImage head count selected first results width dest cap n j m)
      ((4+7*(2*e.binds+4)) + (13+n*(2*(amount W width selected first results j).binds+4)) +
        (11+(n+1)*(2*(TerminalWireArchive.prefixWord x).work+4))) := by
  let initial := rangeImage head count width dest 1 m
  let mid := amountImage width selected first results n j initial
  let x := prefixLayout head cap width dest n
  have nfit : n < 2^W := (counter ▸ (m (count:Word W).val).isLt)
  have nf1 : n+1 < 2^W := by have z:=space.«prefix»;change dest+(n+1)<2^W at z;omega
  have wfit : width+n < 2^W := space.widths
  have nword : m (count:Word W).val=(n:Word W) := Fin.ext (by rw [counter,Fin.val_cast_of_lt nfit])
  have atWord (i : Fin 7) := range_at head count width dest 1 m i
  have c0 : initial head=((head+1:ℕ):Word W) := by simpa [initial] using atWord 0
  have c1 : initial (head+1)=(width:Word W) := by simpa [initial] using atWord 1
  have c2 : initial (head+2)=(n:Word W) := by
    exact (atWord 2).trans (show (1:Word W)*m (count:Word W).val=(n:Word W) by rw [one_mul,nword])
  have c3 : initial (head+3)=((head+4:ℕ):Word W) := by simpa [initial] using atWord 3
  have c5 : initial (head+5)=(dest:Word W) := by simpa [initial] using atWord 5
  have c6 : initial (head+6)=((n+1:ℕ):Word W) := by
    exact (atWord 6).trans (show (1:Word W)*m (count:Word W).val+1=((n+1:ℕ):Word W) by rw [one_mul,nword,Nat.cast_add,Nat.cast_one])
  have kept (i : Fin 7) : mid (head+i.val)=initial (head+i.val) := by
    have h : ¬(width ≤ head+i.val ∧ head+i.val < width+n) := by have := i.isLt;omega
    simp only [mid,amountImage,fillSegment,ite_eq_right h]
  have c3' : mid (head+3)=((head+4:ℕ):Word W) := (kept 3).trans c3
  have c5' : mid (head+5)=(dest:Word W) := (kept 5).trans c5
  have c6' : mid (head+6)=((n+1:ℕ):Word W) := (kept 6).trans c6
  have val (i : ℕ) (hi : i ≤ 6) : ((head+i:ℕ):Word W).val=head+i := Fin.val_cast_of_lt (by omega)
  have plus (i j : ℕ) (h : i+j ≤ 6) : (((head+i:ℕ):Word W)+(j:Word W)).val=head+(i+j) := by
    rw [←Nat.cast_add,Nat.add_assoc,val _ h]
  have p11 : (((head+1:ℕ):Word W)+1).val=head+2 := by
    rw [←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  have p41 : (((head+4:ℕ):Word W)+1).val=head+5 := by
    rw [←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  have p42 : (((head+4:ℕ):Word W)+2).val=head+6 := by
    change (((head+4:ℕ):Word W)+(2:ℕ)).val=_
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  have ac : (amountScan W head width selected first results j).Spec (·=initial) (fun _ out=>out=mid)
      (13+n*(2*(amount W width selected first results j).binds+4)) := amount_run head width selected first results n j initial wfit (by
    rw [Fin.val_cast_of_lt (by omega),c0,add_zero,val 1 (by decide),c1]) (by
    rw [Fin.val_cast_of_lt (by omega),c0,p11,c2]) selection headWord rows
  have pc : (HeaderScan.procedure (x.current:Word W) 1 2 (HeaderScan.closed (TerminalWireArchive.prefixWord x))).Spec
      (·=mid) (fun _ out=>out=TerminalWireArchive.image x mid)
      (11+(x.edges+1)*(2*(TerminalWireArchive.prefixWord x).work+4)) := TerminalWireArchive.prefix_steps x space mid (by
    change (mid (mid ((head+3:ℕ):Word W).val+1).val).val=dest
    rw [val 3 (by decide),c3',p41,c5',Fin.val_cast_of_lt (by have := space.«prefix»; change dest+(n+1) < _ at this;omega)]) (by
    change (mid (mid ((head+3:ℕ):Word W).val+2).val).val=n+1
    rw [val 3 (by decide),c3',p42,c6',Fin.val_cast_of_lt nf1]) tables
  intro term fields P R K machine
  exact compose (compose (range_run head count width dest 1 m headFit cn) ac) pc machine

def before (W : ℕ) (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) : Procedure W :=
  let c (j : Fin 3) := column W D.current count D.selected D.first D.results (width j)
    (![D.pins,D.rows,D.bits] j) cap j
  ((((c 0).seq (c 1)).seq (c 2)).seq (rangeSeed W D.current count D.tasks 0 5)).seq (procedure D W)

/-- Fixed compiled term sizes; all operands and capacities are literals in the program. -/
private def headerBinds := (pick 1 0 (List.ofFn (rangeWords 1 0 0 0 0 1))).binds
private def widthBinds := (amount 1 0 0 0 0 0).binds
private def prefixWork := (TerminalWireArchive.prefixWord (prefixLayout 0 0 0 0 0)).work

private def headerClock := 4+7*(2*headerBinds+4)
private def columnClock (n : ℕ) :=
  headerClock + (13+n*(2*widthBinds+4)) + (11+(n+1)*(2*prefixWork+4))

private theorem header_binds (W head count width dst mul : ℕ) :
    (pick W head (List.ofFn (rangeWords W head count width dst mul))).binds=headerBinds := by
  simp [headerBinds,List.ofFn_succ,rangeWords,pick,Term.select,Term.binary,Term.load,Term.literal,Term.binds]

private theorem width_binds (W width selected first results : ℕ) (j : Fin 3) :
    (amount W width selected first results j).binds=widthBinds := by
  simp [widthBinds,amount,Term.binary,Term.load,Term.literal,Term.binds]

private theorem prefix_work (x : TerminalWireArchive.Layout) : (TerminalWireArchive.prefixWord x).work=prefixWork := by rfl

theorem range_bounded (head count width dst mul : ℕ) (m : Memory W)
    (room : head+7 < 2^W) (off : (count:Word W).val < head ∨ head+7 ≤ (count:Word W).val) :
    (rangeSeed W head count width dst mul).Spec (·=m)
      (fun _ out=>out=rangeImage head count width dst mul m) 4096 := by
  apply Procedure.Spec.mono (A:=rangeSeed W head count width dst mul) (range_run head count width dst mul m room off) (fun _ h=>h) (fun _ _ h=>h)
  rw [header_binds]
  decide

/-- All three width scans, three prefixes, four range headers and the final
five-word task scan. The additive cost includes the three empty-prefix sentinels. -/
def before_clock (n : ℕ) := 3*columnClock n + headerClock + (13+1300*n)

/-- The coefficient paid by each selected root is independent of the word
width, the number of roots, their cached sizes, and the numeric arena addresses. -/
def before_per_root := 3*((2*widthBinds+4)+(2*prefixWork+4)) + 1300

theorem before_rate (n : ℕ) : before_clock n=before_clock 0+before_per_root*n := by
  unfold before_clock before_per_root columnClock
  ring

def columnBase (D : Layout) : Fin 3 → ℕ := ![D.pins,D.rows,D.bits]

def afterColumn (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ)
    (j : Fin 3) (m : Memory W) :=
  columnImage D.current count D.selected D.first D.results (width j) (columnBase D j) cap n j m

def beforeStart (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ) (m : Memory W) :=
  let applyCol := afterColumn D count cap width n (W:=W)
  let cols := applyCol 2 (applyCol 1 (applyCol 0 m))
  rangeImage D.current count D.tasks 0 5 cols

def beforeImage (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ) (m : Memory W) :=
  output D n (beforeStart D count cap width n m)

/-- Bounds for the four actual memory scans that prepare the terminal tasks. -/
structure BeforeBounds (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n W : ℕ) : Prop where
  head : D.current+7 < 2^W
  countLow : count < D.current
  firstLow : D.first < D.current
  selectedLow : D.selected+n ≤ D.current
  tasksHigh : D.current+7 ≤ D.tasks
  tasksFit : D.tasks+5*n < 2^W
  col : ∀ j, TerminalWireArchive.Bounds (prefixLayout D.current cap (width j) (columnBase D j) n) W
  widthHigh : ∀ j, D.current+7 ≤ width j
  prefixHigh : ∀ j, D.current+7 ≤ columnBase D j
  tables : ∀ j i, i<n → width j+i < columnBase D j ∨ columnBase D j+n < width j+i
  reads : ∀ j, ReadRange D n W (columnBase D j)

/-- Execute all three genuine gather/prefix scans and physically write five
words per selected root. Only the input cache lookups and the count are data dependent. -/
theorem before_run (D : Layout) (count cap : ℕ) (width : Fin 3 → ℕ) (n : ℕ) (m : Memory W)
    (room : BeforeBounds D count cap width n W) (cnt : (m count).val=n)
    (cacheLow : ∀ j (i : Fin n), (amountAddress D.selected D.first D.results j m (i.val:Word W)).val < D.current) :
    (before W D count cap width).Spec (·=m)
      (fun _ out=>out=beforeImage D count cap width n m) (before_clock n) := by
  let head := D.current
  let next := afterColumn D count cap width n (W:=W)
  let same (z : Memory W) := ∀ a, a < D.current → z a=m a
  have headFit := room.head
  have countLow := room.countLow
  have firstLow := room.firstLow
  have selLow := room.selectedLow
  have cr : (count:Word W).val=count := Fin.val_cast_of_lt (by omega)
  have fr : (D.first:Word W).val=D.first := Fin.val_cast_of_lt (by omega)
  have anchor (i : Fin n) : ((D.selected:Word W)+(i.val:Word W)).val=D.selected+i.val := by
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by have := i.isLt;omega)]
  have one (j : Fin 3) (z : Memory W) (agree : same z) :
      (column W D.current count D.selected D.first D.results (width j) (columnBase D j) cap j).Spec
      (·=z) (fun _ out=>out=next j z) (columnClock n) := by
    unfold columnClock headerClock
    rw [←header_binds W D.current count (width j) (columnBase D j) 1,
      ←width_binds W (width j) D.selected D.first D.results j,
      ←prefix_work (prefixLayout D.current cap (width j) (columnBase D j) n)]
    apply column_run
    · exact room.col j
    · exact room.widthHigh j
    · exact headFit
    · rw [cr,agree _ countLow];exact cnt
    · exact Or.inl (by rwa [cr])
    · exact selLow.trans (by have := room.widthHigh j;omega)
    · have := room.widthHigh j;omega
    · intro i
      let ini := rangeImage D.current count (width j) (columnBase D j) 1 z
      have low (a : ℕ) (ha : a < D.current) : ini a=m a := by
        have outside : ¬(D.current≤a ∧ a<D.current+7) := by omega
        simpa only [ini,rangeImage,fillSegment,ite_eq_right outside] using agree a ha
      have a : amountAddress D.selected D.first D.results j ini (i.val:Word W)=
          amountAddress D.selected D.first D.results j m (i.val:Word W) := by
        simp only [amountAddress,low (D.first:Word W).val (by rwa [fr]),
          low ((D.selected:Word W)+(i.val:Word W)).val (by rw [anchor];have := i.isLt;omega)]
      apply Or.inl
      change (amountAddress D.selected D.first D.results j ini (i.val:Word W)).val < width j
      rw [a]
      have := cacheLow j i
      have := room.widthHigh j
      omega
    · exact room.tables j
  have stepFrame (j : Fin 3) (z : Memory W) (agree : same z) : same (next j z) := by
    intro a ha
    have p : ¬(columnBase D j ≤ a ∧ a<columnBase D j+(n+1)) := by have := room.prefixHigh j;omega
    have w : ¬(width j ≤ a ∧ a<width j+n) := by have := room.widthHigh j;omega
    have h : ¬(D.current≤a ∧ a<D.current+7) := by omega
    simpa only [next,afterColumn,columnImage,TerminalWireArchive.image,prefixLayout,rangeImage,
      amountImage,fillSegment,ite_eq_right p,ite_eq_right w,ite_eq_right h] using agree a ha
  have s0 : same m := fun _ _=>rfl
  let z1 := next 0 m
  let z2 := next 1 z1
  let z3 := next 2 z2
  have s1 : same z1 := stepFrame 0 m s0
  have s2 : same z2 := stepFrame 1 z1 s1
  have s3 : same z3 := stepFrame 2 z2 s2
  let z4 := rangeImage D.current count D.tasks 0 5 z3
  have cf : n<2^W := cnt ▸ (m count).isLt
  have nword : z3 (count:Word W).val=(n:Word W) := Fin.ext (by rw [cr,s3 _ countLow,cnt,Fin.val_cast_of_lt cf])
  have c0 : z4 D.current=((D.current+1:ℕ):Word W) := by simpa [z4] using range_at D.current count D.tasks 0 5 z3 0
  have c1 : z4 (D.current+1)=(D.tasks:Word W) := by simpa [z4] using range_at D.current count D.tasks 0 5 z3 1
  have c2 : z4 (D.current+2)=((5*n:ℕ):Word W) := by
    exact (range_at D.current count D.tasks 0 5 z3 2).trans (show (5:Word W)*z3 (count:Word W).val=((5*n:ℕ):Word W) by rw [nword,Nat.cast_mul];rfl)
  have h : (D.current:Word W).val=D.current := Fin.val_cast_of_lt (by omega)
  have h1 : ((D.current+1:ℕ):Word W).val=D.current+1 := Fin.val_cast_of_lt (by omega)
  have h2 : (((D.current+1:ℕ):Word W)+1).val=D.current+2 := by
    rw [←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  have tasksHigh := room.tasksHigh
  have last : (procedure D W).Spec (·=z4) (fun _ out=>out=output D n z4) (13+1300*n) := run_disjoint D n z4 room.tasksFit (by rw [h,c0,add_zero,h1,c1])
    (by rw [h,c0,h2,c2]) (by omega) (by omega) (room.reads 0) (room.reads 1) (room.reads 2)
  have seed : (rangeSeed W D.current count D.tasks 0 5).Spec (·=z3) (fun _ out=>out=z4) headerClock := by
    unfold headerClock
    rw [←header_binds W D.current count D.tasks 0 5]
    exact range_run D.current count D.tasks 0 5 z3 headFit (Or.inl (by rwa [cr]))
  have time : before_clock n=((columnClock n+columnClock n)+columnClock n)+headerClock+(13+1300*n) := by
    unfold before_clock;ring
  rw [time]
  intro P R K machine
  exact compose (compose (compose (compose (one 0 m s0) (one 1 z1 s1)) (one 2 z2 s2)) seed) last machine

end Hierarchy.TraceReceiverTasks

end OAI
