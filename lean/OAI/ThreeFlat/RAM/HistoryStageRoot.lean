import OAI.ThreeFlat.RAM.HistoryNodeValue
import OAI.ThreeFlat.RAM.HistoryBoundedJoin
import OAI.ThreeFlat.RAM.HistoryPortMap
import OAI.ThreeFlat.Diagonal.HistoryPackedSources

namespace OAI
/-! # Addressing the kernel and every actual old child of a chronological site -/

namespace ThreeFlat.RAM.HistoryStageRoot

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing

/-- The six low fields identify a real compact node and its previously
computed kernel. All remaining pointers are selected scratch allocations. -/
structure Input where
  id : ℕ
  nodeBase : ℕ
  resultBase : ℕ
  kernel : ℕ
  stream : ℕ
  maps : ℕ
  operand : ℕ
  ext : ℕ
  links : ℕ
  copyArguments : ℕ
  extArguments : ℕ

def Input.words (s : Input) : Fin 11→ℕ :=
  ![s.id,s.nodeBase,s.resultBase,s.kernel,s.stream,s.maps,s.operand,s.ext,s.links,s.copyArguments,s.extArguments]

def node (T : Input) := T.nodeBase+8*T.id
def childCount (T : Input) (m : ℕ→ℕ) := m (node T+4)
def childPtr (T : Input) (m : ℕ→ℕ) (i : ℕ) := T.resultBase+8*m (m (node T+3)+i)
def «prefix» (T : Input) (m : ℕ→ℕ) (i : ℕ) (f : Result→ℕ) :=
  ∑ j ∈ Finset.range i,f (atResult m (childPtr T m j))
def halfWidth (T : Input) (m : ℕ→ℕ) :=
  let header := m (node T+6)
  let n := m header
  let last := m (header+1)+4*(n-1)
  if n=0 then 0 else m (last+3)+m (last+2)

def oldHalf (s : Result) := s.pins-s.extCount
def hidden (T : Input) (m : ℕ→ℕ) := «prefix» T m (childCount T m) oldHalf
def outer (T : Input) (m : ℕ→ℕ) := m (node T+7)
def outPins (T : Input) (m : ℕ→ℕ) := outer T m+halfWidth T m
def ptr (T : Input) (m : ℕ→ℕ) (i : ℕ) := if i=0 then T.kernel else childPtr T m (i-1)
def mapPtr (T : Input) (m : ℕ→ℕ) (i : ℕ) := if i=0 then T.maps
  else T.maps+(atResult m T.kernel).pins+«prefix» T m (i-1) Result.pins

def hub (T : Input) (m : ℕ→ℕ) : HistoryBoundedJoin.Hub :=
  ⟨T.stream,outPins T m,hidden T m,childCount T m+1,T.links,T.copyArguments⟩

def link (T : Input) (m : ℕ→ℕ) (i : ℕ) : HistoryBoundedJoin.Child :=
  ⟨ptr T m i,mapPtr T m i,8,T.operand+5*i⟩

def operands (T : Input) (m : ℕ→ℕ) (i : ℕ) : Fin 5→ℕ :=
  let all := outPins T m
  let src := atResult m (ptr T m i)
  if i=0 then ![T.maps,src.pins,hidden T m,2+all,2+outer T m]
  else let z := i-1
       ![mapPtr T m i,src.pins,src.extCount,2+«prefix» T m z Result.extCount,2+all+«prefix» T m z oldHalf]

def result (T : Input) (m : ℕ→ℕ) : Fin 6→ℕ :=
  let c := childCount T m
  let kernel := atResult m T.kernel
  ![T.stream,outPins T m,kernel.rows+«prefix» T m c Result.rows,
    hidden T m+kernel.bits+«prefix» T m c Result.bits,T.ext,outer T m]

def endpointWords (T : Input) (m : ℕ→ℕ) (i : ℕ) : Fin 3→ℕ :=
  let x := atResult m (childPtr T m i)
  ![T.ext+«prefix» T m i Result.extCount,x.extCount,x.ext]

def endpointCommand (T : Input) (m : ℕ→ℕ) (i : ℕ) : Fin 7→ℕ :=
  let a := endpointWords T m i
  ![T.extArguments+3*i,a 0,10,0,0,0,a 0+a 1]

private abbrev E := Formula 13
def arg (j : ℕ) : E := .load (add (.reg 0) (.lit j))
def read (a : E) (j : ℕ) : E := .load (add a (.lit j))
def nd (j : ℕ) := read (add (arg 1) (mul (.lit 8) (arg 0))) j
def child (i : E) := add (arg 2) (mul (.lit 8) (.load (add (nd 3) i)))
/-- An eager prefix instruction reads only an actual child ID or an input
register word. Inactive result-field reads refer to the resident kernel. -/
def prefixChild (k : ℕ) (n : E) : E :=
  let slot := lt (.lit k) n (add (nd 3) (.lit k)) (.reg 0)
  lt (.lit k) n (add (arg 2) (mul (.lit 8) (.load slot))) (arg 3)

def info (a : E) (j : ℕ) := if j=6 then sub (read a 1) (read a 5) else read a j
def sum (n : E) (j : ℕ) : ℕ → E
  | 0 => .lit 0
  | k+1 => add (sum n j k) (lt (.lit k) n (info (prefixChild k n) j) (.lit 0))
def field (x : E) (xs : List E) : E :=
  match xs with
  | [] => .lit 0
  | a::as => eqz x (.lit 0) a (field (sub x (.lit 1)) as)

inductive Bank | hub | link | mapArgs | result | extArgs | extCommand deriving DecidableEq
def Bank.width : Bank → ℕ | .hub=>6 | .link=>4 | .mapArgs=>5 | .result=>6 | .extArgs=>3 | .extCommand=>7

def formula (cap : ℕ) (bank : Bank) : E :=
  let x : E := .reg 5
  let i := div x (.lit bank.width)
  let col := rem x (.lit bank.width)
  let z := sub i (.lit 1)
  let C := nd 4
  let ext := nd 7
  let half := nd 6
  let count : E := .load half
  let last := eqz count (.lit 0) (.reg 0) (add (read half 1) (mul (.lit 4) (sub count (.lit 1))))
  let width := eqz count (.lit 0) (.lit 0) (add (read last 3) (read last 2))
  let all := add ext width
  let old := sum C 6 cap
  let slot := eqz i (.lit 0) (.reg 0) (add (nd 3) z)
  let src := eqz i (.lit 0) (arg 3) (add (arg 2) (mul (.lit 8) (.load slot)))
  let pinMap := eqz i (.lit 0) (arg 5) (add (add (arg 5) (read (arg 3) 1)) (sum z 1 cap))
  let dest := add (arg 7) (sum i 5 cap)
  match bank with
  | .hub => field col [arg 4,all,old,add C (.lit 1),arg 8,arg 9]
  | .link => field col [src,pinMap,.lit 8,add (arg 6) (mul (.lit 5) i)]
  | .mapArgs => field col [pinMap,read src 1,eqz i (.lit 0) old (read src 5),
      add (.lit 2) (eqz i (.lit 0) all (sum z 5 cap)),
      add (.lit 2) (eqz i (.lit 0) ext (add all (sum z 6 cap)))]
  | .result => field col [arg 4,all,add (read (arg 3) 2) (sum C 2 cap),
      add (add old (read (arg 3) 3)) (sum C 3 cap),arg 7,ext]
  | .extArgs => field col [dest,read (child i) 5,read (child i) 4]
  | .extCommand => field col [add (arg 10) (mul (.lit 3) i),dest,.lit 10,.lit 0,.lit 0,.lit 0,add dest (read (child i) 5)]

def Bank.word (T : Input) (m : ℕ→ℕ) (i : ℕ) : (b : Bank) → Fin b.width → ℕ
  | .hub => (HistoryStageRoot.hub T m).words
  | .link => (HistoryStageRoot.link T m i).words
  | .mapArgs => operands T m i
  | .result => HistoryStageRoot.result T m
  | .extArgs => endpointWords T m i
  | .extCommand => endpointCommand T m i

private theorem empty_width (n a b : ℕ) (m : ℕ→ℕ) :
    (if n=0 then 0 else m ((if n=0 then a else b)+3)+m ((if n=0 then a else b)+2)) =
      (if n=0 then 0 else m (b+3)+m (b+2)) := by
  by_cases e : n=0 <;> simp [e]

private theorem measured (top : E) (j c W : ℕ) (d : Param→ℕ) (m : ℕ→ℕ) (vs : Fin 13→ℕ)
    (idx : (top.natural W d m vs)≤c) :
    (sum top j c).natural W d m vs=
      ∑ q∈Finset.range (top.natural W d m vs), (info (child (.lit q)) j).natural W d m vs := by
  have raw : (sum top j c).natural W d m vs=
      ∑ q∈Finset.range c,if q<top.natural W d m vs then (info (child (.lit q)) j).natural W d m vs else 0 := by
    clear idx
    induction c with
    | zero => simp [sum,Formula.natural]
    | succ c ih =>
      by_cases live : c<top.natural W d m vs
      · by_cases f : j=6
        · subst j
          simp [sum,prefixChild,child,info,read,Formula.natural,add,lt,natOp,natTest,ih,Finset.sum_range_succ,live]
        · simp [sum,prefixChild,child,info,read,Formula.natural,add,lt,natOp,natTest,ih,Finset.sum_range_succ,live,f]
      · simp [sum,prefixChild,info,read,Formula.natural,add,lt,natOp,natTest,ih,Finset.sum_range_succ,live]
  rw [raw,←Finset.sum_filter]
  congr 1
  ext q
  simp [Finset.mem_range]
  omega

private def item (j : ℕ) (m : ℕ→ℕ) (addr : ℕ) :=
  if j=6 then m (addr+1)-m (addr+5) else m (addr+j)

private theorem sum_at (T : Input) (base W cap : ℕ) (d : Param→ℕ) (m : ℕ→ℕ)
    (vs : Fin 13→ℕ) (words : ∀ j : Fin 11,m (base+j.val)=T.words j)
    (start : vs 0=base) {top : E} (bound : top.natural W d m vs≤cap) (field : ℕ) :
    (sum top field cap).natural W d m vs=
      ∑ q ∈ Finset.range (top.natural W d m vs),item field m (childPtr T m q) := by
  have z := words 0;have n := words 1;have r := words 2
  change m (base+0)=T.id at z
  change m (base+1)=T.nodeBase at n
  change m (base+2)=T.resultBase at r
  simp only [Nat.add_zero] at z
  rw [measured top field cap W d m vs bound]
  apply Finset.sum_congr rfl
  intro q _
  by_cases six : field=6 <;>
    simp [info,child,nd,arg,read,add,mul,sub,Formula.natural,natOp,start,z,n,r,childPtr,node,item,six]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
/-- The six generated banks at a real stage. The new pin sequence and old
half-bit offsets use the same ordering throughout the child RAM scans. -/
theorem bank_word (W cap : ℕ) (T : Input) (base : ℕ) (d : Param→ℕ) (m : ℕ→ℕ)
    (vs : Fin 13→ℕ) (bank : Bank) (i : ℕ) (j : Fin bank.width)
    (words : ∀ f : Fin 11,m (base+f.val)=T.words f)
    (start : vs 0=base) (key : vs 5=bank.width*i+j.val)
    (room : i≤cap) (owned : childCount T m≤cap) :
    (formula cap bank).natural W d m vs=bank.word T m i j := by
  have h0 := words (0:Fin 11);have h1 := words (1:Fin 11);have h2 := words (2:Fin 11)
  have h3 := words (3:Fin 11);have h4 := words (4:Fin 11);have h5 := words (5:Fin 11)
  have h6 := words (6:Fin 11);have h7 := words (7:Fin 11);have h8 := words (8:Fin 11)
  have h9 := words (9:Fin 11);have h10 := words (10:Fin 11)
  change m (base+0)=T.id at h0
  change m (base+1)=T.nodeBase at h1
  change m (base+2)=T.resultBase at h2
  change m (base+3)=T.kernel at h3
  change m (base+4)=T.stream at h4
  change m (base+5)=T.maps at h5
  change m (base+6)=T.operand at h6
  change m (base+7)=T.ext at h7
  change m (base+8)=T.links at h8
  change m (base+9)=T.copyArguments at h9
  change m (base+10)=T.extArguments at h10
  simp only [Nat.add_zero] at h0
  let ix : E := div (.reg 5) (.lit bank.width)
  have width : 0<bank.width := by cases bank <;> decide
  have bit := j.isLt
  have ii : ix.natural W d m vs=i := by
    change vs 5/bank.width=i
    rw [key,Nat.mul_add_div width,Nat.div_eq_of_lt bit,Nat.add_zero]
  have col : vs 5%bank.width=j.val := by
    rw [key,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt bit]
  have nn : (nd 4).natural W d m vs=childCount T m := by
    simp [nd,read,arg,mul,add,Formula.natural,natOp,childCount,node,start,h0,h1]
  have ni (f : ℕ) := sum_at T base W cap d m vs words start (top:=ix) (by rwa [ii]) f
  have pred : (sub ix (.lit 1)).natural W d m vs=i-1 := by simp [Formula.natural,ii]
  have zi (f : ℕ) := sum_at T base W cap d m vs words start (top:=sub ix (.lit 1)) (by rw [pred];omega) f
  have nc (f : ℕ) := sum_at T base W cap d m vs words start (top:=nd 4) (by rwa [nn]) f
  simp only [ii] at ni
  simp only [pred] at zi
  simp only [nn] at nc
  have divAt : vs 5 / bank.width = i := ii
  clear key
  simp only [nd,read,arg,add,mul] at nc
  have cases_i : i=0 ∨ i≠0 := eq_or_ne i 0
  rcases cases_i with hi|hi <;> cases bank <;> fin_cases j
  all_goals simp only [ix,div,sub,Bank.width] at ni zi
  all_goals simp [Bank.width] at col divAt
  all_goals
    simp [formula,Bank.word,Bank.width,field,ni,zi,nc,col,divAt,
      child,nd,arg,read,eqz,add,sub,mul,div,rem,Formula.natural,natOp,natTest,start,
      h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,node,childPtr,ptr,mapPtr,childCount,hub,link,
      operands,result,endpointWords,endpointCommand,HistoryBoundedJoin.Hub.words,HistoryBoundedJoin.Child.words,
      «prefix»,hidden,outer,outPins,oldHalf,atResult,halfWidth,item,hi,empty_width,Nat.add_assoc]

def program (W cap : ℕ) (bank : Bank) : Term W 1 13 := (formula cap bank).compile (fun _ => 0)

theorem program_word (W cap : ℕ) (T : Input) (base : ℕ) (d : Fin 1→ℕ) (m : ℕ→ℕ)
    (vs : Fin 13→ℕ) (b : Bank) (i : ℕ) (j : Fin b.width)
    (words : ∀ f : Fin 11,m (base+f.val)=T.words f)
    (start : vs 0=base) (key : vs 5=b.width*i+j.val)
    (room : i≤cap) (owned : childCount T m≤cap)
    (fit : (formula cap b).Fits W (fun _ => d 0) m vs) :
    (program W cap b).eval (fun f => (d f:Word W)) (fun a => (m a:Word W))
      (fun a => (vs a:Word W))=(b.word T m i j:Word W) := by
  rw [program,Formula.eval_compile]
  change (formula cap b).value (fun _ => (d 0 : Word W))
    (fun a => (m a : Word W)) (fun a => (vs a : Word W)) = _
  exact (Formula.value_eq_natural _ _ _ _ fit).trans
    (congrArg (fun n : ℕ => (n : Word W)) (bank_word W cap T base _ m vs b i j words start key room owned))

theorem program_size (W W' cap : ℕ) (bank : Bank) :
    (program W cap bank).binds=(program W' cap bank).binds := by simp [program,Formula.binds_compile]


section PhysicalWires
open Diagonal.HistoryContraction BitLayout
open scoped BigOperators Classical

variable {F Pins : Type*} [CommSemiring F] {S : Shape} {R : Rewrite S F} {t : Fin R.count}
  (L : PortLayout S Pins) (V : PortLayout (R.target t) Pins) (count : (R.target t).Site→ℕ)
  (order : ∀ v,Fin (count v)≃{j // R.owner t j=v}) (v : (R.target t).Site)
local notation "next" => L.inherit V count order

theorem oldWidth_read (T : Input) (m : ℕ→ℕ) (i : Fin (count v))
    (arity : (atResult m (childPtr T m i.val)).pins=L.form.width (order v i).val)
    (ext : (atResult m (childPtr T m i.val)).extCount=L.ext (order v i).val) :
    oldHalf (atResult m (childPtr T m i.val))=L.oldWidths count order v i := by
  rw [oldHalf,arity,ext];simp [PortLayout.form,PortLayout.oldWidths]

/-- Header words read from the selected node and its native child array.
The three address identities below use exactly these four physical columns. -/
structure Ports (T : Input) (m : ℕ→ℕ) : Prop where
  degree : childCount T m=count v
  fresh : halfWidth T m=V.halfBits v
  external : outer T m=(next).ext v
  childArity : ∀ i : Fin (count v),(atResult m (childPtr T m i.val)).pins=L.form.width (order v i).val
  childExt : ∀ i : Fin (count v),(atResult m (childPtr T m i.val)).extCount=L.ext (order v i).val

variable {T : Input} {m : ℕ→ℕ}

theorem prefix_value {num : ℕ} (f : Result→ℕ) (g : Fin num→ℕ)
    (eqn : ∀ i : Fin num,f (atResult m (childPtr T m i.val))=g i)
    (j : ℕ) (hj : j≤num) :
    «prefix» T m j f=∑ i : Fin j,g (i.castLE hj) := by
  rw [«prefix»,←Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _=>eqn (i.castLE hj)

theorem Ports.hidden (r : Ports L V count order v T m) :
    HistoryStageRoot.hidden T m=L.hidden count order v := by
  rw [HistoryStageRoot.hidden,r.degree]
  exact prefix_value oldHalf (L.oldWidths count order v)
    (fun i=>oldWidth_read L count order v T m i (r.childArity i) (r.childExt i)) _ le_rfl

theorem Ports.kernel_word (r : Ports L V count order v T m) (j : Fin (L.hidden count order v+V.halfBits v)) :
    let q := operands T m 0
    HistoryPortMap.piecewise j.val (q 2) (q 3) (q 4)=sourceAddress (L.kernelWire next count order v j) := by
  have eqn : outPins T m=(next).form.width v := by rw [outPins,r.external,r.fresh];rfl
  change HistoryPortMap.piecewise j.val (HistoryStageRoot.hidden T m) (2+outPins T m) (2+outer T m)=_
  rw [r.hidden,eqn,r.external]
  exact (HistoryPortMap.kernel_map L next count order v j).symm

theorem Ports.child_word (r : Ports L V count order v T m) (i : Fin (count v))
    (j : Fin (L.form.width (order v i).val)) :
    let q := operands T m (i.val+1)
    HistoryPortMap.piecewise j.val (q 2) (q 3) (q 4)=
      sourceAddress (L.previousWire next count order v i (L.inheritedIndex V count order v i) j) := by
  have all : outPins T m=(next).form.width v := by rw [outPins,r.external,r.fresh];rfl
  have rawExt := prefix_value Result.extCount (fun z=>L.ext (order v z).val) r.childExt i.val i.isLt.le
  have rawHalf := prefix_value oldHalf (L.oldWidths count order v)
    (fun z=>oldWidth_read L count order v T m z (r.childArity z) (r.childExt z)) i.val i.isLt.le
  change HistoryPortMap.piecewise j.val (atResult m (childPtr T m i.val)).extCount
    (2+«prefix» T m i.val Result.extCount) (2+outPins T m+«prefix» T m i.val oldHalf)=_
  rw [r.childExt i,rawExt,rawHalf,all]
  exact (HistoryPortMap.child_map L V count order v i j).symm


end PhysicalWires



end ThreeFlat.RAM.HistoryStageRoot

end OAI
