import OAI.Hierarchy.ProtocolRAMScan
import OAI.ThreeFlat.Diagonal.MotifHistogram

namespace OAI
/-! # Native histogram admission and installed-width calculation -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Diagonal.MotifOuterTerms
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing BigOperators

variable {w t q : ℕ}

def totals : (q : ℕ) → (Fin q → Expr) → Expr
  | 0,_ => .lit 0
  | n+1,x => .op .add (x 0) (totals n (fun i => x i.succ))

@[simp] theorem eval_totals (m : Memory w) (r : Word w) (q : ℕ) (x : Fin q → Expr) :
    (totals q x).eval m r = ∑ i, (x i).eval m r := by
  induction q with
  | zero => simp [totals,Expr.eval]
  | succ n ih => simp [totals,Expr.eval,ih,Fin.sum_univ_succ,RowOp.opcode,BinaryOp.eval]

/-- Check the available stock of every resource against its required amount before
deducting any resource. Each comparison is also used for the selector range check. -/
def ifEnough : (q : ℕ) → (Fin q → Expr) → (Fin q → Expr) → Expr → Expr → Expr
  | 0,_,_,yes,_ => yes
  | n+1,need,haveStock,yes,no =>
    .branch .lt (haveStock 0) (need 0) no
      (ifEnough n (fun i => need i.succ) (fun i => haveStock i.succ) yes no)

theorem eval_ifEnough (m : Memory w) (r : Word w) (q : ℕ)
    (need haveStock : Fin q → Expr) (yes no : Expr) :
    (ifEnough q need haveStock yes no).eval m r =
      if ∀ i, ((need i).eval m r).val ≤ ((haveStock i).eval m r).val
      then yes.eval m r else no.eval m r := by
  induction q with
  | zero => simp [ifEnough]
  | succ n ih =>
    simp only [ifEnough,Expr.eval,ih,Fin.forall_fin_succ,Comparison.test,decide_eq_true_eq,Fin.lt_def]
    split_ifs <;> simp_all; omega

/-- For an inactive or stock-deficient candidate the caller invokes this same check
with batch size zero. It then accepts exactly the all-zero selector block. -/
def ifHistogram (q t : ℕ) (field : Fin q → Expr) (yes no : Expr) : Expr :=
  ifEnough q field (fun _ => .lit t)
    (.branch .eq (totals q field) (.lit t) yes no) no

theorem eval_ifHistogram (m : Memory w) (r : Word w) (q t : ℕ)
    (field : Fin q → Expr) (yes no : Expr) (ht : t < 2^w) (sumFit : q*t < 2^w) :
    (ifHistogram q t field yes no).eval m r =
      if ∑ i, ((field i).eval m r).val = t then yes.eval m r else no.eval m r := by
  classical
  let counts (i : Fin q) := ((field i).eval m r).val
  have units : ∀ i, (field i).eval m r = (counts i : Word w) := fun _ => by simp [counts]
  rw [ifHistogram,eval_ifEnough]
  simp only [Expr.eval,Fin.val_cast_of_lt ht]
  by_cases bounded : ∀ i, counts i ≤ t
  · have limit : ∑ i, counts i ≤ q*t := by
      calc
        _ ≤ ∑ _ : Fin q, t := Finset.sum_le_sum fun i _ => bounded i
        _ = q*t := by simp
    have eqv : ((∑ i, (field i).eval m r) = (t : Word w)) ↔ ∑ i, counts i = t := by
      simp only [units,← Nat.cast_sum,Fin.ext_iff,Fin.val_cast_of_lt (limit.trans_lt sumFit),
        Fin.val_cast_of_lt ht]
    simp only [show (∀ i, ((field i).eval m r).val ≤ t) from bounded,ite_true,
      eval_totals,Comparison.test,beq_iff_eq,eqv,counts,implies_true]
  · have mismatch : (∑ i, counts i) ≠ t := by
      intro h
      apply bounded
      intro i
      exact h ▸ (Finset.single_le_sum (fun j _ => Nat.zero_le (counts j)) (Finset.mem_univ i))
    simp only [show ¬ (∀ i, ((field i).eval m r).val ≤ t) from bounded,ite_false,
      show (∑ i, ((field i).eval m r).val) ≠ t from mismatch]

theorem unused_fields (m : Memory w) (r : Word w) (field : Fin q → Expr) (yes no : Expr) :
    (ifHistogram q 0 field yes no).eval m r =
      if ∀ i, (field i).eval m r = 0 then yes.eval m r else no.eval m r := by
  rw [eval_ifHistogram m r q 0 field yes no (by positivity) (by simp)]
  have zero : (∑ i, ((field i).eval m r).val) = 0 ↔ ∀ i, (field i).eval m r = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le (((field i).eval m r).val))]
    constructor
    · intro h i
      exact Fin.ext (h i (Finset.mem_univ i))
    · intro h i _
      exact congrArg Fin.val (h i)
  simp only [zero]

/-- A coefficient in a local replacement packet has a fixed bound independent of
the data height. Test each of its possible values and reuse the corresponding static
addition program. This eliminates native general-purpose multiplication. -/
def scale : ℕ → Expr → Expr
  | 0,_ => .lit 0
  | n+1,x => .op .add x (scale n x)

@[simp] theorem eval_scale (m : Memory w) (r : Word w) (n : ℕ) (e : Expr) :
    (scale n e).eval m r = (n : Word w)*e.eval m r := by
  induction n with
  | zero => simp [scale,Expr.eval]
  | succ n ih => simp [scale,Expr.eval,RowOp.opcode,BinaryOp.eval,ih,Nat.cast_succ,add_mul,add_comm]

def boundedMul : ℕ → Expr → Expr → Expr
  | 0,_,_ => .lit 0
  | n+1,x,coeff => .branch .eq coeff (.lit (n+1)) (scale (n+1) x) (boundedMul n x coeff)

theorem eval_boundedMul (m : Memory w) (r : Word w) (n : ℕ) (x coeff : Expr)
    (bound : (coeff.eval m r).val ≤ n) (room : n < 2^w) :
    (boundedMul n x coeff).eval m r = x.eval m r * coeff.eval m r := by
  induction n with
  | zero =>
    have zero : coeff.eval m r=0 := Fin.ext (by simpa using bound)
    simp [boundedMul,Expr.eval,zero]
  | succ n ih =>
    rw [boundedMul,Expr.eval]
    simp only [Expr.eval,Comparison.test,beq_iff_eq]
    by_cases top : coeff.eval m r = ((n+1 : ℕ) : Word w)
    · simp [top,mul_comm]
    · rw [ite_eq_right top]
      apply ih _ (by omega)
      by_contra! high
      apply top
      apply Fin.ext
      rw [Fin.val_cast_of_lt room]
      omega

/-- Dot product of the admitted multiplicities and the per-term widths on one option.
Separate terms retain their own counters even if all their output widths coincide. -/
def installed (q maxWidth : ℕ) (field count : Fin q → Expr) : Expr :=
  totals q fun i => boundedMul maxWidth (field i) (count i)

theorem installed_histWidth {E : Type*} (m : Memory w) (r : Word w) (e : E)
    (maxWidth : ℕ) (field table : Fin q → Expr) (counts : Fin q → E → ℕ) (h : Histogram (Fin q) t)
    (fields : ∀ i, (field i).eval m r = ((h.val i).val : Word w))
    (options : ∀ i, (table i).eval m r = (counts i e : Word w))
    (maxBound : ∀ i, counts i e ≤ maxWidth) (fits : maxWidth < 2^w) :
    (installed q maxWidth field table).eval m r = (histWidth counts h e : Word w) := by
  have bounded (i : Fin q) : ((table i).eval m r).val ≤ maxWidth := by
    rw [options,Fin.val_cast_of_lt ((maxBound i).trans_lt fits)]
    exact maxBound i
  simp [installed,histWidth,eval_boundedMul m r maxWidth _ _ (bounded _) fits,fields,options]

theorem boundedMul_value_le (m : Memory w) (r : Word w) (cap : ℕ) (x coeff : Expr) :
    ((boundedMul cap x coeff).eval m r).val ≤ cap*(x.eval m r).val := by
  induction cap with
  | zero => simp [boundedMul,Expr.eval]
  | succ n ih =>
    rw [boundedMul,Expr.eval]
    split
    · rw [eval_scale,Fin.val_mul,Fin.val_natCast]
      exact (Nat.mod_le _ _).trans (Nat.mul_le_mul_right _ (Nat.mod_le _ _))
    · exact ih.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))

theorem totals_value_le (m : Memory w) (r : Word w) (q : ℕ) (x : Fin q → Expr) :
    ((totals q x).eval m r).val ≤ ∑ i, ((x i).eval m r).val := by
  induction q with
  | zero => simp [totals,Expr.eval]
  | succ k ih =>
    rw [totals,Expr.eval,Fin.sum_univ_succ]
    exact (Nat.mod_le _ _).trans (Nat.add_le_add_left (ih (fun i=>x i.succ)) _)

theorem installed_le (m : Memory w) (r : Word w) (q cap : ℕ) (field table : Fin q → Expr) :
    ((installed q cap field table).eval m r).val ≤ cap*(∑ i, ((field i).eval m r).val) := by
  rw [Finset.mul_sum]
  exact (totals_value_le ..).trans <| Finset.sum_le_sum fun i _=>boundedMul_value_le m r cap (field i) (table i)

/-- Price recommendations, inventory pointers and packed histogram fields can each
be indexed by previous lookups. The mixed-radix row selects the advised menu. -/
def priceLookup (prices stock : Bank) (kind stride : ℕ) (coordinate : Expr) : Expr :=
  .lookup prices (.op .add (.lit (kind*stride)) (.lookup stock coordinate))

def menuKey (radix : ℕ) : List Expr → Expr
  | [] => .lit 0
  | d::ds => .op .add d (scale radix (menuKey radix ds))

theorem scale_work (n : ℕ) (e : Expr) : (scale n e).work=1+n*(e.work+1) := by
  induction n with
  | zero => simp [scale,Expr.work]
  | succ n ih => simp only [scale,Expr.work,ih,Nat.succ_mul];omega

/-- A precision radix polynomial in log h still gives a polylogarithmic
per-row loop, since the local probe dimension is fixed. -/
theorem menuKey_work (radix bound : ℕ) (xs : List Expr) (h : ∀ x∈xs,x.work≤bound) :
    (menuKey radix xs).work+1 ≤ (bound+4)*(radix+2)^xs.length := by
  induction xs with
  | nil => simp [menuKey,Expr.work]
  | cons x xs ih =>
    let A := (bound+4)*(radix+2)^xs.length
    have pos : 0<(radix+2)^xs.length := pow_pos (by omega) _
    have full : bound+4≤A := Nat.le_mul_of_pos_right _ pos
    have head := h x (List.mem_cons_self ..)
    have tail := ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))
    calc
      _ = (x.work+3)+radix*((menuKey radix xs).work+1) := by simp [menuKey,Expr.work,scale_work];omega
      _ ≤ A+radix*A := Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ tail)
      _ ≤ A*(radix+2) := by rw [Nat.mul_add,Nat.mul_comm A radix];omega
      _ = _ := by simp [A,pow_succ,Nat.mul_assoc]

def menuLookup (table : Bank) (radix : ℕ) (quoted : List Expr) : Expr :=
  .lookup table (menuKey radix quoted)

/-- A skipped replacement returns the previous stock; an applied replacement
debits its complete demand and then credits its selected commodity output. -/
def stockUpdate (commit old debit credit : Expr) : Expr :=
  .branch .eq commit (.lit 0) old (.op .add (.op .sub old debit) credit)

theorem stockUpdate_applied (m : Memory w) (r : Word w) (commit old debit credit : Expr)
    (active : commit.eval m r ≠ 0) (funded : (debit.eval m r).val ≤ (old.eval m r).val) :
    (stockUpdate commit old debit credit).eval m r =
      (((old.eval m r).val - (debit.eval m r).val + (credit.eval m r).val : ℕ) : Word w) := by
  simp only [stockUpdate,Expr.eval,Comparison.test,beq_iff_eq,Nat.cast_zero,active,ite_false,
    RowOp.opcode,BinaryOp.eval,Nat.cast_add,Nat.cast_sub funded,Fin.cast_val_eq_self]


end Hierarchy.ProtocolRAM

end OAI
