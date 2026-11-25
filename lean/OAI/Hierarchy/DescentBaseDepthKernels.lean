import OAI.Hierarchy.DescentNativeProfileScan
import OAI.Hierarchy.ProtocolRAMSchedule
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Integer seed and propagation operations on the physical reset tape -/

namespace Hierarchy.DescentBaseProfile.DepthRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing BigOperators
variable {w H : ℕ}

def cell (a : ℕ) : Expr := .lookup ⟨a,0⟩ (.lit 0)
@[simp] theorem cell_read (a : ℕ) (m : Memory w) (i : Word w) : (cell a).eval m i=m a := by
  simp [cell,Expr.eval,Bank.read,Bank.size]
@[simp] theorem cell_end (a : ℕ) : (cell a).inputEnd=a+1 := by simp [cell,Expr.inputEnd,Bank.size]
@[simp] theorem cell_work (a : ℕ) : (cell a).work=6 := rfl

def rowSum (a : ℕ) : ℕ→Expr
  | 0=>.lit 0
  | j+1=>.op .add (rowSum a j) (cell (a+j))

theorem rowSum_read (m : Memory w) (a n : ℕ) (values : ℕ→ℕ) (row : Word w)
    (given : ∀ j < n, m (a + j) = (values j : Word w)) :
    (rowSum a n).eval m row=(∑j∈Finset.range n,values j:ℕ) := by
  induction n with
  | zero=>simp [rowSum,Expr.eval]
  | succ j ih=>simp only [rowSum,Expr.eval,RowOp.opcode,BinaryOp.eval,cell_read,
      ih (fun q h=>given q (by omega)),given j (by omega),Finset.sum_range_succ,Nat.cast_add]

theorem rowSum_bounds (a n : ℕ) : (rowSum a n).work=1+7*n ∧ (rowSum a n).inputEnd≤a+n := by
  induction n with
  | zero=>simp [rowSum,Expr.work,Expr.inputEnd]
  | succ n ih=>simp only [rowSum,Expr.work,Expr.inputEnd,ih.1,cell_work,cell_end,max_le_iff];omega

theorem lt_word {a b : ℕ} (ha : a<2^w) (hb : b<2^w) : (a:Word w)<(b:Word w) ↔ a<b := by
  change ((a:Word w).val<(b:Word w).val) ↔_
  rw [Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb]

private theorem test_lt {a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    DescriptorExpr.Comparison.lt.test (a : Word w) (b : Word w) = true ↔ a < b := by
  simpa only [DescriptorExpr.Comparison.test, decide_eq_true_eq] using lt_word ha hb

/-- The literal threshold can overflow the machine although all loads fit.
In that case every physical row has already met the threshold. -/
def probe (w mass lo : ℕ) : ℕ→ℕ→ℕ→Expr
  | 0,d,_=>.lit (max lo d)
  | i+1,d,p=>if 2^w≤p then .lit (max lo d) else
      .branch .lt (.lit p) (cell mass) (probe w mass lo i (d+1) (p+p)) (.lit (max lo d))

theorem probe_read (m : Memory w) (a W lo n d p : ℕ) (row : Word w) (fits : W<2^w) (read : m a=(W:Word w)) :
    (probe w a lo n d p).eval m row=(max lo (Native.probe W n d p).1:ℕ) := by
  induction n generalizing d p with
  | zero=>rfl
  | succ i ih=>
    by_cases full : 2^w≤p
    · simp [probe,Native.probe,full,show W≤p by omega,Expr.eval]
    · have small : p < 2^w := Nat.lt_of_not_ge full
      simp only [probe, ite_eq_right full, Native.probe, Expr.eval, cell_read, read, test_lt small fits]
      by_cases test : W≤p
      · simp [test,not_lt_of_ge test]
      · simp [test,Nat.lt_of_not_ge test,ih]

theorem probe_bounds (w a lo n d p : ℕ) :
    (probe w a lo n d p).work≤1+9*n ∧ (probe w a lo n d p).inputEnd≤a+1 := by
  induction n generalizing d p with
  | zero=>simp [probe,Expr.work,Expr.inputEnd]
  | succ i ih=>
    have h:=ih (d+1) (p+p)
    simp only [probe]
    split <;> simp [Expr.work,Expr.inputEnd,cell_work,cell_end]; omega

def maximum (a b : Expr) : Expr := .branch .lt a b b a

theorem max_read (m : Memory w) (row : Word w) (a b : Expr) (x y : ℕ)
    (xr : a.eval m row=(x:Word w)) (yr : b.eval m row=(y:Word w)) (xs : x<2^w) (ys : y<2^w) :
    (maximum a b).eval m row=(max x y:ℕ) := by
  by_cases order : x<y
  · simp [maximum,Expr.eval,xr,yr,test_lt xs ys,order,max_eq_right order.le]
  · simp [maximum,Expr.eval,xr,yr,test_lt xs ys,order,max_eq_left (Nat.le_of_not_gt order)]

def decrease (e : Expr) (g : ℕ) : Expr := .branch .lt e (.lit g) (.lit 0) (.op .sub e (.lit g))

theorem decrease_read (m : Memory w) (row : Word w) (e : Expr) (x g : ℕ)
    (read : e.eval m row=(x:Word w)) (xs : x<2^w) (gs : g<2^w) :
    (decrease e g).eval m row=(x-g:ℕ) := by
  by_cases order : x<g
  · simp [decrease,Expr.eval,read,test_lt xs gs,order,Nat.sub_eq_zero_of_le order.le]
  · have le : g≤x := by omega
    simp [decrease,Expr.eval,read,test_lt xs gs,order,RowOp.opcode,BinaryOp.eval,Nat.cast_sub le]

/-- One neighbor ID comes from the original sparse physical row. A sentinel
at least H contributes zero. A valid ID performs a genuine indirect lookup. -/
def neighbor (H old ℓ src g : ℕ) : Expr := .branch .lt (cell src) (.lit H)
  (decrease (.lookup ⟨old,ℓ⟩ (cell src)) g) (.lit 0)

def number (o : Option (Fin H)) := o.elim H Fin.val

theorem neighbor_read (m : Memory w) (old ℓ src g : ℕ) (row : Word w) (next : Option (Fin H))
    (h : H<2^w) (capacity : H≤2^ℓ) (gs : g<2^w) (source : m src=(number next:Word w))
    (values : Fin H→ℕ) (bounded : ∀i,values i<2^w) (prior : ∀i : Fin H,m (old+i.val)=(values i:Word w)) :
    (neighbor H old ℓ src g).eval m row=(next.elim 0 (fun u=>values u-g):ℕ) := by
  cases next with
  | none => simp [neighbor, Expr.eval, cell_read, source, number, test_lt h h]
  | some u=>
    have hu := u.isLt.trans h
    have idx : ((u.val:Word w)).val % 2^ℓ=u.val := by
      rw [Fin.val_cast_of_lt hu,Nat.mod_eq_of_lt (u.isLt.trans_le capacity)]
    have q : (Expr.lookup ⟨old,ℓ⟩ (cell src)).eval m row=(values u:Word w) := by
      change m (old + ((cell src).eval m row).val % 2^ℓ) = _
      rw [cell_read, source]
      change m (old + (u.val : Word w).val % 2^ℓ) = _
      rw [idx]
      exact prior u
    simp only [neighbor,Expr.eval,cell_read,source,number,Option.elim_some,test_lt hu h,
      u.isLt,ite_true]
    exact decrease_read m row _ _ _ q (bounded u) gs

/-- Balanced occurrence tree. The duplication from word comparisons costs
quadratic work in the public degree bound, independently of the host size. -/
def tournament (f : ℕ→Expr) : ℕ→ℕ→Expr
  | 0,i=>f i
  | s+1,i=>maximum (tournament f s i) (tournament f s (i+2^s))

def largest (f : ℕ→ℕ) : ℕ→ℕ→ℕ
  | 0,i=>f i
  | s+1,i=>max (largest f s i) (largest f s (i+2^s))

theorem largest_le {f : ℕ→ℕ} {x : ℕ} (s i : ℕ) (bound : ∀q,i≤q→q < i+2^s→f q≤x) : largest f s i≤x := by
  induction s generalizing i with
  | zero=>exact bound i le_rfl (by simp)
  | succ s ih=>
    rw [largest,max_le_iff];rw [pow_succ] at bound
    exact ⟨ih i (fun q a b=>bound q a (by omega)),ih (i+2^s) (fun q a b=>bound q (by omega) (by omega))⟩

theorem le_largest (f : ℕ→ℕ) (s i q : ℕ) (lo : i≤q) (hi : q < i+2^s) : f q≤largest f s i := by
  induction s generalizing i with
  | zero =>
    have eqn : q = i := by
      simp only [pow_zero] at hi
      omega
    subst q
    exact le_rfl
  | succ s ih=>
    rw [largest];rw [pow_succ] at hi
    by_cases low : q < i+2^s
    · exact (ih i lo low).trans (le_max_left ..)
    · exact (ih (i+2^s) (by omega) (by omega)).trans (le_max_right ..)

theorem tournament_read (m : Memory w) (row : Word w) (f : ℕ→Expr) (val : ℕ→ℕ) (s i : ℕ)
    (read : ∀q,(f q).eval m row=(val q:Word w)) (bound : ∀q,val q<2^w) :
    (tournament f s i).eval m row=(largest val s i:ℕ) := by
  induction s generalizing i with
  | zero=>exact read i
  | succ s ih=>
    have below (j : ℕ) : largest val s j<2^w :=
      Nat.lt_of_le_of_lt (largest_le s j (x:=2^w-1) (fun q _ _=>by have:=bound q;omega)) (by have:=Nat.two_pow_pos w;omega)
    exact max_read _ _ _ _ _ _ (ih i) (ih _) (below i) (below _)

end Hierarchy.DescentBaseProfile.DepthRAM

end OAI
