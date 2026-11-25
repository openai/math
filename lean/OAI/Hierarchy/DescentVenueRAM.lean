import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.TraceIntervalScanner

namespace OAI
/-! # Add-only native publication of old and six-party physical venue ordinals -/

namespace Hierarchy.DescentVenueRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure ProtocolRAM ProtocolRAMGeneratedWrite
open scoped Fin.CommRing Classical
noncomputable section

/-- Fixed source banks in the matched nine-word format. The two schedule
banks are literal integer offsets for the six possible parties in each row. -/
structure Sources where
  pair : Bank
  pack : Bank
  layout : Bank
  rowAnchor : Bank
  colAnchor : Bank

def add (x y : Expr) : Expr := .op .add x y
def twice (x : Expr) := add x x
def nine (x : Expr) := add (twice (twice (twice x))) x

def field (S : Sources) (index : Expr) (off : ℕ) := Expr.lookup S.pair (add (nine index) (.lit off))
def side (S : Sources) (rowExpr col : Expr) := Expr.branch .eq (.lookup S.layout (.lit 0)) (.lit 0) rowExpr col

/-- Pair i is indexed into the actual packed venue of its thin source.
The reverse scatter stores a representative one-based pointer per venue. -/
def destination (S : Sources) := Expr.lookup S.pack (field S .row 5)

/-- A zero head leaves the old pack alone. Every representative of a live
thin slot yields the same genuine thick center. -/
def old (S : Sources) (heads : Bank) : Expr :=
  let pack := Expr.lookup S.pack .row
  let ptr := Expr.lookup heads pack
  let index := Expr.op .sub ptr (.lit 1)
  Expr.branch .eq ptr (.lit 0) pack
    (.lookup S.pack (side S (field S index 3) (field S index 4)))

/-- Six contiguous rows per pair; each selects an original site ordinal and
then reads the previously published old-site venue. -/
def born (S : Sources) (oldKey : Bank) : Expr :=
  .lookup oldKey (.lookup S.pair (side S (.lookup S.rowAnchor .row) (.lookup S.colAnchor .row)))

def roleOffset (l : Bool) : Fin 6→ℕ :=
  if l then ![3,4,4,6,6,4] else ![3,4,3,6,3,6]

def anchorWord (l : Bool) (u : ℕ) := 9*(u/6)+roleOffset l ⟨u%6,Nat.mod_lt _ (by decide)⟩

theorem anchor_at (l : Bool) (i : ℕ) (j : Fin 6) :
    anchorWord l (6*i+j.val)=9*i+roleOffset l j := by
  simp [anchorWord,Nat.mul_add_div (by decide : 0<6),Nat.div_eq_of_lt j.isLt,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]

variable {w n t c : ℕ}
structure Rows (n t c : ℕ) where
  packed : Fin t→Fin c
  thickSrc : Fin n→Fin t
  thickDst : Fin n→Fin t
  thinSrc : Fin n→Fin t
  thinDst : Fin n→Fin t
  layout : Bool
  coherent : ∀i j,packed (thinSrc i)=packed (thinSrc j)→
    packed (if layout then thickDst i else thickSrc i)=packed (if layout then thickDst j else thickSrc j)

def Rows.dest (r : Rows n t c) (i) := r.packed (r.thinSrc i)
def Rows.center (r : Rows n t c) (i) := r.packed (if r.layout then r.thickDst i else r.thickSrc i)
def Rows.resolve (r : Rows n t c) (v : Fin c) : Fin c :=
  if h : ∃i,r.dest i=v then r.center h.choose else v
def Rows.oldKey (r : Rows n t c) (u : Fin t) := r.resolve (r.packed u)
def Rows.anchor (r : Rows n t c) (i : Fin n) (j : Fin 6) :=
  if roleOffset r.layout j=3 then r.thickSrc i else if roleOffset r.layout j=4 then r.thickDst i else r.thinDst i

theorem Rows.active (r : Rows n t c) (i : Fin n) : r.resolve (r.dest i)=r.center i := by
  have hit : ∃j,r.dest j=r.dest i := ⟨i,rfl⟩
  exact (dite_eq_left hit).trans (r.coherent _ _ hit.choose_spec)

structure Loaded (S : Sources) (r : Rows n t c) (m : Memory w) : Prop where
  pack : ∀u,m (S.pack.base+u.val)=(r.packed u).val
  thickSrc : ∀i,m (S.pair.base+(9*i.val+3))=(r.thickSrc i).val
  thickDst : ∀i,m (S.pair.base+(9*i.val+4))=(r.thickDst i).val
  thinSrc : ∀i,m (S.pair.base+(9*i.val+5))=(r.thinSrc i).val
  thinDst : ∀i,m (S.pair.base+(9*i.val+6))=(r.thinDst i).val
  layout : m S.layout.base=if r.layout then 1 else 0
  rowAnchor : ∀i : Fin n,∀j : Fin 6,m (S.rowAnchor.base+(6*i.val+j.val))=(9*i.val+roleOffset false j:ℕ)
  colAnchor : ∀i : Fin n,∀j : Fin 6,m (S.colAnchor.base+(6*i.val+j.val))=(9*i.val+roleOffset true j:ℕ)

structure Bounds (S : Sources) (w n t stop : ℕ) : Prop where
  pair : S.pair.Fits w stop
  pack : S.pack.Fits w stop
  layout : S.layout.Fits w stop
  rowAnchor : S.rowAnchor.Fits w stop
  colAnchor : S.colAnchor.Fits w stop
  pairCount : 9*n≤S.pair.size
  siteCount : t≤S.pack.size
  rowCount : 6*n≤S.rowAnchor.size
  colCount : 6*n≤S.colAnchor.size

theorem bank_at (b : Bank) (m : Memory w) (i : ℕ) (hi : i<b.size) (room : b.size<2^w) :
    b.read m (i:Word w)=m (b.base+i) := by
  simp [Bank.read,Fin.val_cast_of_lt (hi.trans room),Nat.mod_eq_of_lt hi]

private theorem nine_eval (x : Expr) (m : Memory w) (a : Word w) :
    (nine x).eval m a=9*x.eval m a := by
  simp [nine,twice,add,Expr.eval,RowOp.opcode,BinaryOp.eval]
  ring

theorem field_at (S : Sources) (_r : Rows n t c) {stop : ℕ} (b : Bounds S w n t stop)
    {x : Expr} {a : Word w} {m : Memory w} (i : Fin n) (hx : x.eval m a=(i.val:Word w)) (off : ℕ) (small : off<9) :
    (field S x off).eval m a=m (S.pair.base+(9*i.val+off)) := by
  have hi := i.isLt
  have lim := b.pairCount
  have low : 9*i.val+off<S.pair.size := by omega
  simp only [field,Expr.eval,add,RowOp.opcode,BinaryOp.eval,nine_eval,hx]
  rw [←Nat.cast_ofNat (R:=Word w) (n:=9),←Nat.cast_mul,←Nat.cast_add]
  exact bank_at _ _ _ low b.pair.2.1

theorem eval_destination (S : Sources) (r : Rows n t c) {stop : ℕ} (b : Bounds S w n t stop)
    {m : Memory w} (load : Loaded S r m) (i : Fin n) :
    (destination S).eval m (i.val:Word w)=(r.dest i).val := by
  change S.pack.read m ((field S .row 5).eval m (i.val:Word w))=_
  rw [field_at S r b i rfl 5 (by decide),load.thinSrc,bank_at _ _ _ ((r.thinSrc i).isLt.trans_le b.siteCount) b.pack.2.1]
  exact load.pack _

theorem eval_side (S : Sources) (r : Rows n t c) {stop : ℕ} (b : Bounds S w n t stop)
    {m : Memory w} (load : Loaded S r m) (r0 r1 : Expr) (a : Word w) (hn : 1<2^w) :
    (side S r0 r1).eval m a=if r.layout then r1.eval m a else r0.eval m a := by
  simp only [side,Expr.eval,bank_at S.layout m 0 b.layout.1 b.layout.2.1,Nat.add_zero,load.layout]
  have distinct : (1 : Word w) ≠ 0 := by
    intro eqn
    apply Nat.one_ne_zero
    simpa only [Fin.val_one',Nat.mod_eq_of_lt hn,Fin.val_zero] using (congrArg Fin.val eqn)
  cases r.layout <;> simp [DescriptorExpr.Comparison.test,distinct]

theorem head_info {H N : ℕ} {r : Rows n t c} {m o : Memory w} (ran : TraceIntervalScanner.Output H N r.dest m o)
    (v : Fin c) : ((o (H+v.val)).val=0 ∧ ¬∃i,r.dest i=v) ∨
      ∃i,r.dest i=v ∧ (o (H+v.val)).val=i.val+1 := by
  let xs := (List.finRange n).filter (fun i=>r.dest i=v)
  have chain := ran.chain v
  have mem (i : Fin n) : i∈xs ↔ r.dest i=v := by simp [xs]
  cases e : xs with
  | nil =>
    have h : (o (H+v.val)).val=0 := by change TraceIntervalScanner.Chain N o (o (H+v.val)).val xs at chain;rw [e] at chain;exact chain
    exact Or.inl ⟨h,by rintro ⟨i,hi⟩; have := (mem i).mpr hi; simp [e] at this⟩
  | cons i is =>
    have hi : i∈xs := by simp [e]
    have h : (o (H+v.val)).val=i.val+1 := by change TraceIntervalScanner.Chain N o (o (H+v.val)).val xs at chain;rw [e] at chain;exact chain.1
    exact Or.inr ⟨i,(mem i).mp hi,h⟩

theorem eval_old (S : Sources) (r : Rows n t c) {stop N : ℕ} (b : Bounds S w n t stop)
    (H : Bank) (hr : c≤H.size) (hh : H.size<2^w) {m o : Memory w}
    (load : Loaded S r o) (ran : TraceIntervalScanner.Output H.base N r.dest m o)
    (more : 1<2^w) (u : Fin t) :
    (old S H).eval o (u.val:Word w)=(r.oldKey u).val := by
  let v := r.packed u
  let ptr := o (H.base+v.val)
  let count := Expr.lookup H (.lookup S.pack .row)
  have packRead : (.lookup S.pack .row:Expr).eval o (u.val:Word w)=(v.val:Word w) := by
    rw [Expr.eval,Expr.eval,bank_at _ _ _ (u.isLt.trans_le b.siteCount) b.pack.2.1]
    exact load.pack u
  have countRead : count.eval o (u.val:Word w)=ptr := by
    change H.read o ((.lookup S.pack .row:Expr).eval o _)=_
    rw [packRead,bank_at _ _ _ (v.isLt.trans_le hr) hh]
  rcases head_info ran v with ⟨zero,no⟩|⟨i,same,idx⟩
  · have word : ptr=0 := Fin.ext zero
    change (if DescriptorExpr.Comparison.eq.test (count.eval o (u.val:Word w)) 0
      then (.lookup S.pack .row : Expr).eval o (u.val:Word w) else _) = ((r.resolve v).val:Word w)
    rw [countRead,word]
    simp [DescriptorExpr.Comparison.test,packRead,Rows.resolve,no]
  · change ptr.val=i.val+1 at idx
    have nonzero : ptr≠0 := by
      intro zero
      have valZero : ptr.val = 0 := by rw [zero,Fin.val_zero]
      omega
    let index := Expr.op .sub count (.lit 1)
    have hidx : index.eval o (u.val:Word w)=(i.val:Word w) := by
      have hp : ptr = ((i.val+1 : ℕ) : Word w) := by
        have representable : i.val+1 < 2^w := idx ▸ ptr.isLt
        apply Fin.ext
        rw [Fin.val_cast_of_lt representable]
        exact idx
      change count.eval o (u.val:Word w) - (1:Word w) = (i.val:Word w)
      rw [countRead,hp,Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    have yes : r.resolve v=r.center i := same ▸ r.active i
    change (if DescriptorExpr.Comparison.eq.test (count.eval o (u.val:Word w)) 0
      then (.lookup S.pack .row : Expr).eval o (u.val:Word w)
      else S.pack.read o ((side S (field S index 3) (field S index 4)).eval o (u.val:Word w))) =
      ((r.resolve v).val:Word w)
    simp only [countRead,DescriptorExpr.Comparison.test,beq_iff_eq,nonzero,ite_false,yes]
    rw [eval_side S r b load _ _ _ more]
    cases h : r.layout with
    | false =>
      simp only [h,Bool.false_eq_true,ite_false,field_at S r b i hidx 3 (by decide),load.thickSrc,
        bank_at _ _ _ ((r.thickSrc i).isLt.trans_le b.siteCount) b.pack.2.1,load.pack,Rows.center]
    | true =>
      simp only [h,ite_true,field_at S r b i hidx 4 (by decide),load.thickDst,
        bank_at _ _ _ ((r.thickDst i).isLt.trans_le b.siteCount) b.pack.2.1,load.pack,Rows.center]

theorem eval_born (S : Sources) (r : Rows n t c) {stop : ℕ} (b : Bounds S w n t stop)
    (O : Bank) (hr : t≤O.size) (hh : O.size<2^w) {o : Memory w}
    (load : Loaded S r o) (previous : ∀u : Fin t,o (O.base+u.val)=(r.oldKey u).val)
    (more : 1<2^w) (i : Fin n) (j : Fin 6) :
    (born S O).eval o ((6*i.val+j.val:ℕ):Word w)=(r.oldKey (r.anchor i j)).val := by
  have hi := i.isLt
  have hj := j.isLt
  have ends : 6*i.val+j.val<6*n := by omega
  have data : (side S (.lookup S.rowAnchor .row) (.lookup S.colAnchor .row)).eval o
      ((6*i.val+j.val:ℕ):Word w)=((9*i.val+roleOffset r.layout j:ℕ):Word w) := by
    rw [eval_side S r b load _ _ _ more]
    cases h : r.layout <;> simp only [Bool.false_eq_true,ite_false,ite_true,Expr.eval,
      bank_at _ _ _ (ends.trans_le b.rowCount) b.rowAnchor.2.1,bank_at _ _ _ (ends.trans_le b.colCount) b.colAnchor.2.1,
      load.rowAnchor,load.colAnchor]
  have bound : roleOffset r.layout j<9 := by cases r.layout <;> fin_cases j <;> decide
  have inPair : 9*i.val+roleOffset r.layout j<S.pair.size := by have := b.pairCount;omega
  change O.read o (S.pair.read o _)=_
  rw [data,bank_at _ _ _ inPair b.pair.2.1]
  have chosen : o (S.pair.base+(9*i.val+roleOffset r.layout j))=((r.anchor i j).val:Word w) := by
    cases h : r.layout <;> fin_cases j <;>
      simp [Rows.anchor,roleOffset,h,load.thickSrc,load.thickDst,load.thinDst]
  rw [chosen,bank_at _ _ _ ((r.anchor i j).isLt.trans_le hr) hh]
  exact previous _

/-- The single deterministic native controller; all arithmetic operations in
the dense passes are addition, subtraction and a constant bit mask. -/
def program (w : ℕ) (S : Sources) (D N : ℕ) (H O : Bank) (bornKey n t c : ℕ) : Procedure w :=
  (((scan w D n (destination S)).seq (TraceIntervalScanner.procedure w D H.base N n c)).seq
    (scan w O.base t (old S H))).seq (scan w bornKey (6*n) (born S O))

def ticks (S : Sources) (H O : Bank) (n t c : ℕ) :=
  ((4+n*(2*(destination S).work+4))+(9+4*c+10*n))+
    (4+t*(2*(old S H).work+4))+(4+6*n*(2*(born S O).work+4))

end
end Hierarchy.DescentVenueRAM

end OAI
