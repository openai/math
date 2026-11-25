import OAI.Hierarchy.DescentRawFieldOps
import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Native transport of scalar operand word coordinates through an ordinary stage -/

namespace Hierarchy.DescentOperandRouteRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentOrdinaryDestRAM
open scoped Fin.CommRing Classical
noncomputable section

inductive Ref (E : Type) where
  | port (name : ℕ)
  | hidden (name : ℕ)
  | cable (edge : E)
  deriving DecidableEq

inductive Field where | kind | name | offset deriving DecidableEq

variable {E : Type}

def Ref.kind : Ref E→ℕ | .port _=>0 | .hidden _=>1 | .cable _=>2
def Ref.index (ord : E→ℕ) : Ref E→ℕ | .port p | .hidden p=>p | .cable e=>ord e

def Field.read (f : Field) (ord : E→ℕ) (a : Ref E) (q : ℕ) :=
  match f with | .kind=>a.kind | .name=>a.index ord | .offset=>q

/-- The two endpoint pairs come from the same raw cable before and after hub grouping.
The prefix gives the first emitted output edge for this cable. -/
structure Headers (E : Type) where
  firstSrc : E→ℕ
  firstDst : E→ℕ
  lastSrc : E→ℕ
  lastDst : E→ℕ
  «prefix» : E→ℕ
  marked : E→Bool

/-- One unit of the offset may be one bit or one complete aligned word of p bits.
In the latter case `grain` is the number of those words in the emitted cable. -/
def transported (h : Headers E) (ord : E→ℕ) (grain q : ℕ) : Ref E→Ref ℕ × ℕ
  | .port p=>(.port p,q)
  | .hidden v=>(.hidden (4*v+3),q)
  | .cable e=>
    if h.firstSrc e=h.firstDst e then (.hidden (4*ord e+1),q)
    else if h.lastSrc e=h.lastDst e then (.hidden (2*ord e),q)
    else if h.marked e then (.cable (h.«prefix» e+q/grain),q%grain)
    else (.cable (h.«prefix» e),q)

structure Sources where
  kind : Bank
  name : Bank
  offset : Bank
  firstSrc : Bank
  firstDst : Bank
  lastSrc : Bank
  lastDst : Bank
  «prefix» : Bank
  marked : Bank
  quotient : Bank
  remainder : Bank

private def plus (a b : Expr) := Expr.op .add a b
private def choose (a b yes no : Expr) := Expr.branch .eq a b yes no

def expression (s : Sources) (f : Field) : Expr :=
  let tag := Expr.lookup s.kind .row
  let key := Expr.lookup s.name .row
  let q := Expr.lookup s.offset .row
  let capture (a b : Bank) (yes no : Expr) := choose (.lookup a key) (.lookup b key) yes no
  let kept (yes no : Expr) := choose (.lookup s.marked key) (.lit 0) no yes
  let emit (k n d : Expr) := match f with | .kind=>k | .name=>n | .offset=>d
  let port := emit (.lit 0) key q
  let hidden := emit (.lit 1) (plus (times 4 key) (.lit 3)) q
  let first := emit (.lit 1) (plus (times 4 key) (.lit 1)) q
  let last := emit (.lit 1) (times 2 key) q
  let start := Expr.lookup s.«prefix» key
  let split := emit (.lit 2) (plus start (.lookup s.quotient q)) (.lookup s.remainder q)
  let whole := emit (.lit 2) start q
  choose tag (.lit 0) port (choose tag (.lit 1) hidden
    (capture s.firstSrc s.firstDst first (capture s.lastSrc s.lastDst last (kept split whole))))

variable {w n : ℕ} {s : Sources} {h : Headers E} {ord : E→ℕ}
  {ref : Fin n→Ref E} {pos : Fin n→ℕ} {grain : ℕ} {m : Memory w}

/-- The addresses are raw ordinals, including the real selected old, arm and supply rows.
The division tables only depend on grain and the incoming offset. -/
structure Loaded (s : Sources) (h : Headers E) (ord : E→ℕ) (ref : Fin n→Ref E)
    (pos : Fin n→ℕ) (grain : ℕ) (m : Memory w) : Prop where
  tagRead : ∀i,s.kind.read m i.val=(ref i).kind
  nameRead : ∀i,s.name.read m i.val=(ref i).index ord
  offsetRead : ∀i,s.offset.read m i.val=pos i
  firstSource : ∀e,s.firstSrc.read m (ord e)=h.firstSrc e
  firstTarget : ∀e,s.firstDst.read m (ord e)=h.firstDst e
  finalSource : ∀e,s.lastSrc.read m (ord e)=h.lastSrc e
  finalTarget : ∀e,s.lastDst.read m (ord e)=h.lastDst e
  markRead : ∀e,s.marked.read m (ord e)=(if h.marked e then 1 else 0)
  prefixRead : ∀e,s.«prefix».read m (ord e)=h.«prefix» e
  divRead : ∀i,s.quotient.read m (pos i)=((pos i/grain:ℕ):Word w)
  modRead : ∀i,s.remainder.read m (pos i)=((pos i%grain:ℕ):Word w)
  endpoints : ∀e,h.firstSrc e<2^w ∧ h.firstDst e<2^w ∧ h.lastSrc e<2^w ∧ h.lastDst e<2^w

private theorem cast_eq {a b : ℕ} (ha : a<2^w) (hb : b<2^w) :
    (a:Word w)=(b:Word w) ↔ a=b := by
  constructor
  · intro h
    simpa only [Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb] using congrArg Fin.val h
  · rintro rfl;rfl

theorem read (d : Loaded s h ord ref pos grain m) (wide : 2<2^w) (f : Field) (i : Fin n) :
    let a:=transported h ord grain (pos i) (ref i)
    (expression s f).eval m (i.val:Word w)=(f.read id a.1 a.2:Word w) := by
  have distinct (a b : ℕ) (ha : a≤2) (hb : b≤2) := cast_eq (w:=w) (a:=a) (b:=b) (by omega) (by omega)
  have d10 : (1:Word w)≠0 := by exact fun h=>by simpa using (distinct 1 0 (by decide) (by decide)).mp h
  have d20 : (2:Word w)≠0 := by exact fun h=>by simpa using (distinct 2 0 (by decide) (by decide)).mp h
  have d21 : (2:Word w)≠1 := by exact fun h=>by simpa using (distinct 2 1 (by decide) (by decide)).mp h
  cases input : ref i with
  | port t=>cases f <;> simp [expression,choose,plus,Expr.eval,DescriptorExpr.Comparison.test,d.tagRead,d.nameRead,
      d.offsetRead,input,Ref.kind,Ref.index,transported,Field.read]
  | hidden t=>cases f <;> simp [expression,choose,plus,Expr.eval,DescriptorExpr.Comparison.test,d.tagRead,d.nameRead,
      d.offsetRead,input,Ref.kind,Ref.index,transported,Field.read,d10,times_eval,RowOp.opcode,BinaryOp.eval]
  | cable e=>
    obtain ⟨ha,hb,hc,hd⟩:=d.endpoints e
    by_cases pre : h.firstSrc e=h.firstDst e <;> by_cases post : h.lastSrc e=h.lastDst e <;>
      cases flag : h.marked e <;> cases f <;>
      simp [expression,choose,plus,Expr.eval,DescriptorExpr.Comparison.test,d.tagRead,d.nameRead,d.offsetRead,
        input,Ref.kind,Ref.index,transported,Field.read,d20,d21,d10,
        d.firstSource,d.firstTarget,d.finalSource,d.finalTarget,d.prefixRead,d.markRead,d.divRead,
        d.modRead,cast_eq ha hb,cast_eq hc hd,flag,pre,post,times_eval,RowOp.opcode,BinaryOp.eval]

/-- One genuine instruction loop publishes exactly one selected output column. -/
theorem run (d : Loaded s h ord ref pos grain m) (wide : 2<2^w) (f : Field) (out : ℕ)
    (before : (expression s f).inputEnd≤out) (room : out+n<2^w) :
    let e:=expression s f
    (scan w out n e).Exec m (image out n e m) (4+n*(2*e.work+4)) ∧
      ∀i : Fin n,
        let a:=transported h ord grain (pos i) (ref i)
        image out n e m (out+i.val)=(f.read id a.1 a.2:Word w) := by
  exact ⟨scan_exec _ _ _ _ ((expression s f).fits_of_inputEnd before (by omega)) room,
    fun i=>(ProtocolRAMGeneratedWrite.read_image ..).trans (read d wide f i)⟩

end
end Hierarchy.DescentOperandRouteRAM

end OAI
