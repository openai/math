import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # The words consumed by the weighted rank scan, in a supplied physical row order -/

namespace Hierarchy.ProtocolRAMRankGather

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMGeneratedWrite
open scoped Fin.CommRing

inductive Field where | rowID | zero | weight | key
  deriving DecidableEq

/-- A common ordinal expression handles chronological rows and rows read from a sorted
ordinal column. The grouped key column remains indexed by the original ordinal. -/
structure Columns where
  order : Expr
  weights : Bank
  keys : Bank

def twice (x : Expr) : Expr := .op .add x x

def four (x : Expr) : Expr := twice (twice x)

def three (x : Expr) : Expr := .op .add (twice x) x

def address (src keys : ℕ) (f : Field) (i : ℕ) : ℕ := match f with
  | .rowID => src+3*i
  | .zero => src+3*i+1
  | .weight => src+3*i+2
  | .key => keys+4*i

def addressExpr (src keys : ℕ) (f : Field) : Expr := match f with
  | .rowID => .op .add (.lit src) (three .row)
  | .zero => .op .add (.lit (src+1)) (three .row)
  | .weight => .op .add (.lit (src+2)) (three .row)
  | .key => .op .add (.lit keys) (four .row)

def valueExpr (banks : Columns) (f : Field) : Expr := match f with
  | .rowID => four banks.order
  | .zero => .lit 0
  | .weight => .lookup banks.weights banks.order
  | .key => .lookup banks.keys .row

variable {w n d : ℕ}

def value (order : Fin n→Fin n) (key : Fin n→Fin d) (width : Fin n→ℕ) (f : Field)
    (i : Fin n) : Word w := match f with
  | .rowID => ((4*(order i).val : ℕ) : Word w)
  | .zero => 0
  | .weight => (width (order i) : Word w)
  | .key => ((key i).val : Word w)

structure Loaded (banks : Columns) (order : Fin n→Fin n) (key : Fin n→Fin d)
    (width : Fin n→ℕ) (m : Memory w) : Prop where
  order_read : ∀ i : Fin n, banks.order.eval m (i.val:Word w)=((order i).val:Word w)
  weight_read : ∀ i, m (banks.weights.base+i.val)=(width i:Word w)
  key_read : ∀ i, m (banks.keys.base+i.val)=((key i).val:Word w)

structure Fits (banks : Columns) (w n scratch src keys : ℕ) : Prop where
  order_fit : banks.order.Fits w scratch
  weights_fit : banks.weights.Fits w scratch
  keys_fit : banks.keys.Fits w scratch
  weight_count : n ≤ banks.weights.size
  key_count : n ≤ banks.keys.size
  start : scratch+2*n ≤ src
  sep : src+3*n ≤ keys
  room : keys+4*n<2^w

private theorem address_eval (src keys : ℕ) (f : Field) (i : ℕ) (m : Memory w) :
    (addressExpr src keys f).eval m (i:Word w)=(address src keys f i:Word w) := by
  cases f <;> simp [addressExpr,address,three,four,twice,Expr.eval,RowOp.opcode,BinaryOp.eval,
    Nat.cast_add,Nat.cast_mul] <;> ring

private theorem fits_address (src keys : ℕ) (f : Field) (w at_ : ℕ) :
    (addressExpr src keys f).Fits w at_ := by cases f <;> repeat' constructor

private theorem fits_value {banks : Columns} {scratch src keys : ℕ}
    (layout : Fits banks w n scratch src keys) (f : Field) :
    (valueExpr banks f).Fits w scratch := by
  cases f with
  | rowID => exact ⟨⟨layout.order_fit,layout.order_fit⟩,⟨layout.order_fit,layout.order_fit⟩⟩
  | zero => trivial
  | weight => exact ⟨layout.weights_fit,layout.order_fit⟩
  | key => exact ⟨layout.keys_fit,trivial⟩

private theorem value_eval {banks : Columns} {scratch src keys : ℕ}
    (layout : Fits banks w n scratch src keys) (f : Field) {order : Fin n→Fin n}
    {key : Fin n→Fin d} {width : Fin n→ℕ} {m : Memory w} (h : Loaded banks order key width m)
    (i : Fin n) : (valueExpr banks f).eval m (i.val:Word w)=value order key width f i := by
  have fit : n<2^w := by have := layout.room; omega
  cases f with
  | rowID =>
    simp only [valueExpr,four,twice,Expr.eval,RowOp.opcode,BinaryOp.eval,h.order_read,value,Nat.cast_mul]
    ring
  | zero => rfl
  | weight =>
    simp only [valueExpr,value,Expr.eval,h.order_read,Bank.read,
      Fin.val_cast_of_lt ((order i).isLt.trans fit),
      Nat.mod_eq_of_lt ((order i).isLt.trans_le layout.weight_count),h.weight_read]
  | key =>
    simp only [valueExpr,value,Expr.eval,Bank.read,
      Fin.val_cast_of_lt (i.isLt.trans fit),
      Nat.mod_eq_of_lt (i.isLt.trans_le layout.key_count),h.key_read]

private theorem address_range {banks : Columns} {scratch src keys : ℕ}
    (layout : Fits banks w n scratch src keys) (f : Field) (i : Fin n) :
    scratch+2*n ≤ address src keys f i.val ∧ address src keys f i.val < 2^w := by
  have := i.isLt
  have := layout.start
  have := layout.sep
  have := layout.room
  cases f <;> simp only [address] <;> omega

private theorem address_inj {src keys : ℕ} (sep : src+3*n ≤ keys)
    {f g : Field} {i j : Fin n} (h : address src keys f i.val=address src keys g j.val) :
    f=g ∧ i=j := by
  have := i.isLt
  have := j.isLt
  cases f <;> cases g <;> simp only [address] at h <;>
    first | exact ⟨rfl,Fin.ext (by omega)⟩ | omega

def fields : List Field := [.rowID,.zero,.weight,.key]

def program (w n scratch src keys : ℕ) (banks : Columns) : List Field → Procedure w
  | [] => scan w scratch 0 (.lit 0)
  | f::fs => (program w n scratch src keys banks fs).seq
      (ProtocolRAMGeneratedWrite.program w scratch (scratch+n) n (addressExpr src keys f) (valueExpr banks f))

def work (n src keys : ℕ) (banks : Columns) : List Field → ℕ
  | [] => 4
  | f::fs => work n src keys banks fs +
      ProtocolRAMGeneratedWrite.work n (addressExpr src keys f) (valueExpr banks f)

def image (scratch src keys : ℕ) (banks : Columns) (order : Fin n→Fin n)
    (key : Fin n→Fin d) (width : Fin n→ℕ) (m : Memory w) : List Field → Memory w
  | [] => m
  | f::fs => ProtocolRAMGeneratedWrite.image scratch (scratch+n) (addressExpr src keys f)
      (valueExpr banks f) (fun i : Fin n => address src keys f i.val) (value order key width f)
      (image scratch src keys banks order key width m fs)

theorem below {scratch src keys : ℕ} {banks : Columns} (layout : Fits banks w n scratch src keys)
    (order : Fin n→Fin n) (key : Fin n→Fin d) (width : Fin n→ℕ) (m : Memory w)
    (fs : List Field) (a : ℕ) (ha : a < scratch) :
    image scratch src keys banks order key width m fs a=m a := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    apply Eq.trans (ProtocolRAMGeneratedWrite.frame _ _ _ _ _ _ _ _ _ (.inl ha) (.inl (by omega))) ih
    exact fun i eq => by have := (address_range layout f i).1; omega

theorem run {scratch src keys : ℕ} {banks : Columns} (layout : Fits banks w n scratch src keys)
    (order : Fin n→Fin n) (key : Fin n→Fin d) (width : Fin n→ℕ) (m : Memory w)
    (input : Loaded banks order key width m) (fs : List Field) :
    (program w n scratch src keys banks fs).Exec m
      (image scratch src keys banks order key width m fs) (work n src keys banks fs) := by
  have room : scratch+2*n<2^w := by have := layout.start; have := layout.sep; have := layout.room; omega
  induction fs with
  | nil =>
    have empty : ProtocolRAM.image scratch 0 (.lit 0) m=m := by
      funext a
      simp [ProtocolRAM.image,fillSegment]
    intro P R K mach pc reg pub exit installed vals cfg original entry same
    have exec := @scan_exec w scratch 0 (.lit 0) m trivial (by omega)
      P R K mach pc reg pub exit installed vals cfg original entry same
    simpa only [work,program,image,empty,Nat.zero_mul,Nat.add_zero] using exec
  | cons f fs ih =>
    let prev := image scratch src keys banks order key width m fs
    have loaded : Loaded banks order key width prev := by
      constructor
      · intro i
        exact (eval_below banks.order _ m prev layout.order_fit
          (below layout order key width m fs)).trans (input.order_read i)
      · intro i
        have h : banks.weights.base+i.val < scratch :=
          (Nat.add_lt_add_left (i.isLt.trans_le layout.weight_count) _).trans_le layout.weights_fit.2.2
        exact (below layout order key width m fs _ h).trans (input.weight_read i)
      · intro i
        have h : banks.keys.base+i.val < scratch :=
          (Nat.add_lt_add_left (i.isLt.trans_le layout.key_count) _).trans_le layout.keys_fit.2.2
        exact (below layout order key width m fs _ h).trans (input.key_read i)
    have step : (ProtocolRAMGeneratedWrite.program w scratch (scratch+n) n (addressExpr src keys f) (valueExpr banks f)).Exec
        prev (image scratch src keys banks order key width m (f::fs)) (ProtocolRAMGeneratedWrite.work n
          (addressExpr src keys f) (valueExpr banks f)) := by
      apply ProtocolRAMGeneratedWrite.run _ _ _ _ _ _ prev (fits_address ..) (fits_value layout f)
        (by omega) (by omega) (fun i => address_eval src keys f i.val prev) (value_eval layout f loaded)
        (fun i => (address_range layout f i).2)
      · intro i j; have := (address_range layout f j).1; have := i.isLt; omega
      · intro i j; have := (address_range layout f j).1; have := i.isLt; omega
    intro P R K mach pc reg pub exit installed vals cfg original entry same
    exact Procedure.Exec.then ih step mach pc reg pub exit installed vals cfg original entry same

theorem read {scratch src keys : ℕ} {banks : Columns} (layout : Fits banks w n scratch src keys)
    (order : Fin n→Fin n) (key : Fin n→Fin d) (width : Fin n→ℕ) (m : Memory w)
    {f : Field} (fs : List Field) (hf : f∈fs) (i : Fin n) :
    image scratch src keys banks order key width m fs (address src keys f i.val)=value order key width f i := by
  induction fs with
  | nil => simp at hf
  | cons g gs ih =>
    by_cases same : f=g
    · subst g
      exact ProtocolRAMGeneratedWrite.read _ _ _ _ _ _ _
        (fun _ _ eq => (address_inj layout.sep eq).2) i
    · have mem := (List.mem_cons.mp hf).resolve_left same
      have lo := (address_range layout f i).1
      apply Eq.trans (ProtocolRAMGeneratedWrite.frame _ _ _ _ _ _ _ _ _ (.inr (by omega))
        (.inr (by omega))) (ih mem)
      exact fun j eq => same (address_inj layout.sep eq).1


end Hierarchy.ProtocolRAMRankGather

end OAI
