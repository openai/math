import OAI.Computability.VPVNP.PairNodeArguments
import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
import Mathlib.Algebra.BigOperators.Fin

/-!
# Compiled addresses of a node's independent slot arguments

An argument buffer stores all outgoing fields followed by all incoming
fields. At an incoming port, the inverse incidence record identifies the
outgoing arc whose width must be counted. Static and runtime slot numbers
use the same ordering and the same width columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.ArgumentAddress

open BurstRAM BurstRAM.PrivateRAM Compression PhaseRecipe
open PairSimulation.NodeArguments

variable {a g w d : ℕ}

/-- Dynamic bases, node and site operands of the address calculation. -/
structure Input where
  /-- Expression for the first address of the private node argument arena. -/
  arenaBase : Expr
  /-- Expression for the number of words reserved for each node's argument frame. -/
  stride : Expr
  /-- Expression for the node index selecting an argument frame. -/
  node : Expr
  /-- Expression for the physical site ordinal used to index the incidence columns. -/
  siteOrd : Expr
  /-- Expression for the base of the inverse actual-incidence column. -/
  actualIn : Expr
  /-- Expression for the base of the widths indexed by outgoing actual slots. -/
  width : Expr

/-- Compute a node's frame address from the arena base, node index, and frame stride. -/
def Input.nodeBase (I : Input) := I.arenaBase.add (I.node.mul I.stride)

/-- Pack the runtime site ordinal and a fixed local slot number into an actual-slot index. -/
def Input.port (I : Input) (i : Fin d) := (I.siteOrd.mul (.lit d)).add (.lit i.val)

/-- Load one slot's width, looking up its outgoing mate first when the slot is incoming. -/
def Input.half (I : Input) (incoming : Bool) (i : Fin d) : Expr :=
  let port := I.port i
  let src := if incoming then Expr.load (I.actualIn.add port) else port
  .load (I.width.add src)

/-- When the dynamic slot is `j`, the factor is one for `i < j` and zero
otherwise. The first division detects whether `j` reaches `i + 1`. -/
def before (j : Expr) (i : Fin d) : Expr :=
  (Expr.lit 1).sub ((Expr.lit 1).div ((j.div (.lit (i.val+1))).add (.lit 1)))

/-- Sum a list of word-valued address expressions, using zero for the empty list. -/
def sum : List Expr → Expr
  | [] => .lit 0
  | x::xs => x.add (sum xs)

/-- Skip the outgoing fields when addressing the incoming half of a frame by summing all
outgoing widths. -/
def outgoing (d : ℕ) (I : Input) (incoming : Bool) : Expr :=
  if incoming then sum ((List.finRange d).map (I.half false)) else .lit 0

/-- Dynamic slot address. The loop bound is the fixed graph degree. -/
def field (d : ℕ) (I : Input) (incoming : Bool) (j : Expr) : Expr :=
  I.nodeBase.add ((outgoing d I incoming).add
    (sum ((List.finRange d).map fun i => (before j i).mul (I.half incoming i))))

/-- Static-slot version, reading just the preceding fields on the selected side. -/
def fieldStatic (I : Input) (incoming : Bool) (j : Fin d) : Expr :=
  I.nodeBase.add ((outgoing d I incoming).add
    (sum (((List.finRange d).take j.val).map (I.half incoming))))

variable (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)
variable (I : Input) (X : State a g) (u : X.network.Site) (T : IncidenceDirectory w)
  (A : Arena) (node : ℕ)

/-- Number a site by its base vertex and binary lane, with the lane as the low-order field. -/
def siteOrdinal : ℕ := (X.baseIndex u.1).val * 2^g + (bitWordFinEquiv g u.2).val

/-- The published values and the node's own runtime ordinals. -/
structure Represents : Prop where
  arena : I.arenaBase.eval pub state mem = CursorRAM.encode w A.start
  stride : I.stride.eval pub state mem = CursorRAM.encode w A.stride
  node : I.node.eval pub state mem = CursorRAM.encode w node
  site : I.siteOrd.eval pub state mem = CursorRAM.encode w (siteOrdinal X u)
  actualIn : I.actualIn.eval pub state mem = T.actualIn
  width : I.width.eval pub state mem = T.width

private theorem encode_add (x y : ℕ) :
    CursorRAM.encode w x + CursorRAM.encode w y = CursorRAM.encode w (x+y) :=
  Fin.ext (Nat.add_mod x y _).symm

private theorem encode_mul (x y : ℕ) :
    CursorRAM.encode w x * CursorRAM.encode w y = CursorRAM.encode w (x*y) :=
  Fin.ext (Nat.mul_mod x y _).symm

variable {pub state mem I X u T A node}

private theorem eval_nodeBase (h : Represents pub state mem I X u T A node) :
    I.nodeBase.eval pub state mem = CursorRAM.encode w (A.base node) := by
  change I.arenaBase.eval pub state mem + I.node.eval pub state mem * I.stride.eval pub state mem = _
  rw [h.arena,h.node,h.stride,encode_mul,encode_add]
  rfl

private theorem eval_port (h : Represents pub state mem I X u T A node) (j : Fin (2^a)) :
    (I.port j).eval pub state mem = IncidenceDirectory.actualPort X (u,j) := by
  change I.siteOrd.eval pub state mem * CursorRAM.encode w (2^a) + CursorRAM.encode w j.val = _
  rw [h.site,encode_mul,encode_add]
  rfl

theorem eval_half (h : Represents pub state mem I X u T A node) (cols : T.ActualColumns X mem)
    (dir : Bool) (j : Fin (2^a)) : (I.half dir j).eval pub state mem = CursorRAM.encode w (X.halfWidth u dir j) := by
  apply Eq.trans _ (WidthRead.value_actual X u T mem cols dir j)
  cases dir with
  | false =>
    change mem (I.width.eval pub state mem + (I.port j).eval pub state mem).val = _
    rw [h.width,eval_port h]
    rfl
  | true =>
    change mem (I.width.eval pub state mem + mem (I.actualIn.eval pub state mem + (I.port j).eval pub state mem).val).val = _
    rw [h.width,h.actualIn,eval_port h]
    rfl

private theorem eval_before (i j : Fin d) (slot : Expr) (fits : d < 2^w)
    (hj : slot.eval pub state mem = CursorRAM.encode w j.val) :
    (before slot i).eval pub state mem = if i.val < j.val then (1 : Word w) else 0 := by
  have hjv : (slot.eval pub state mem).val = j.val := (congrArg Fin.val hj).trans
    (Nat.mod_eq_of_lt (j.isLt.trans fits))
  have hinc : i.val+1 < 2^w := (Nat.succ_le_of_lt i.isLt).trans_lt fits
  have hdiv : (slot.div (.lit (i.val+1))).eval pub state mem = CursorRAM.encode w (j.val/(i.val+1)) := by
    change Fin.ofNat _ ((slot.eval pub state mem).val / (CursorRAM.encode w (i.val+1)).val) = _
    rw [hjv,show (CursorRAM.encode w (i.val+1)).val = i.val+1 from Nat.mod_eq_of_lt hinc]
  have denom : j.val/(i.val+1)+1 < 2^w := by
    have := Nat.div_le_self j.val (i.val+1)
    have := j.isLt
    omega
  have one : (1 : Word w).val = 1 := by
    change 1 % (2^w) = 1
    exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
  have hv : (((slot.div (.lit (i.val+1))).add (.lit 1)).eval pub state mem).val = j.val/(i.val+1)+1 := by
    change ((slot.div (.lit (i.val+1))).eval pub state mem + CursorRAM.encode w 1).val = _
    rw [hdiv,encode_add]
    exact Nat.mod_eq_of_lt denom
  change 1 - Fin.ofNat _ ((1 : Word w).val / (((slot.div (.lit (i.val+1))).add (.lit 1)).eval pub state mem).val) = _
  rw [one,hv]
  by_cases earlier : i.val < j.val
  · have hq : 0 < j.val/(i.val+1) := Nat.div_pos earlier (by omega)
    rw [ite_eq_left earlier,Nat.div_eq_of_lt (by omega)]
    change (1 : Word w) - 0 = 1
    exact sub_zero _
  · rw [ite_eq_right earlier,Nat.div_eq_of_lt (by omega : j.val < i.val+1)]
    change (1 : Word w) - 1 = 0
    exact sub_self _

private theorem eval_sum {J : Type*} (xs : List J) (expr : J → Expr) (vals : J → ℕ)
    (eqn : ∀ j, (expr j).eval pub state mem = CursorRAM.encode w (vals j)) :
    (sum (xs.map expr)).eval pub state mem = CursorRAM.encode w (xs.map vals).sum := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    change (expr i).eval pub state mem + (sum (is.map expr)).eval pub state mem = _
    rw [eqn,ih,encode_add]
    rfl

private theorem sum_range (f : Fin d → ℕ) : ((List.finRange d).map f).sum = ∑ i, f i := by
  rw [← List.ofFn_id,List.map_ofFn,List.sum_ofFn]
  rfl

private theorem eval_outgoing (h : Represents pub state mem I X u T A node) (cols : T.ActualColumns X mem)
    (dir : Bool) : (outgoing (2^a) I dir).eval pub state mem =
      CursorRAM.encode w (if dir then ∑ i, X.halfWidth u false i else 0) := by
  cases dir with
  | false => rfl
  | true =>
    change (sum ((List.finRange _).map (I.half false))).eval pub state mem = CursorRAM.encode w (∑ i, _)
    rw [eval_sum _ _ _ (eval_half h cols false),sum_range]

theorem eval_field (h : Represents pub state mem I X u T A node) (cols : T.ActualColumns X mem)
    (dir : Bool) (slot : Expr) (j : Fin (2^a)) (fits : 2^a < 2^w)
    (hj : slot.eval pub state mem = CursorRAM.encode w j.val) :
    (field (2^a) I dir slot).eval pub state mem = CursorRAM.encode w (A.fieldAddress X u node dir j) := by
  let f := X.halfWidth u dir
  have vals (i : Fin (2^a)) : ((before slot i).mul (I.half dir i)).eval pub state mem =
      CursorRAM.encode w (if i.val<j.val then f i else 0) := by
    change (before slot i).eval pub state mem * (I.half dir i).eval pub state mem = _
    rw [eval_before i j slot fits hj,eval_half h cols]
    split <;> simp [f]
  change I.nodeBase.eval pub state mem + ((outgoing (2^a) I dir).eval pub state mem +
    (sum ((List.finRange _).map _)).eval pub state mem) = _
  rw [eval_nodeBase h,eval_outgoing h cols,eval_sum _ _ _ vals,sum_range,encode_add,encode_add]
  unfold Arena.fieldAddress offset
  rw [List.sum_take_ofFn,Finset.sum_filter]

theorem eval_fieldStatic (h : Represents pub state mem I X u T A node) (cols : T.ActualColumns X mem)
    (dir : Bool) (j : Fin (2^a)) :
    (fieldStatic I dir j).eval pub state mem = CursorRAM.encode w (A.fieldAddress X u node dir j) := by
  change I.nodeBase.eval pub state mem + ((outgoing (2^a) I dir).eval pub state mem +
    (sum (((List.finRange _).take j.val).map _)).eval pub state mem) = _
  rw [eval_nodeBase h,eval_outgoing h cols,eval_sum _ _ _ (eval_half h cols dir),encode_add,encode_add]
  unfold Arena.fieldAddress offset
  rw [List.map_take,← List.ofFn_id,List.map_ofFn]
  rfl

/-- Reads needed for one slot width, counting any computed pointer operands. -/
def halfLoads (I : Input) (dir : Bool) : ℕ :=
  I.width.loads + I.siteOrd.loads + 1 + (if dir then I.actualIn.loads + 1 else 0)

private theorem loads_half (I : Input) (dir : Bool) (i : Fin d) :
    (I.half dir i).loads = halfLoads I dir := by
  cases dir <;> simp [Input.half,Input.port,Expr.loads,Expr.add,Expr.mul,halfLoads]
  omega

private theorem sum_loads {α : Type*} (xs : List α) (f : α → Expr) (n : ℕ)
    (h : ∀ i, (f i).loads = n) : (sum (xs.map f)).loads = xs.length*n := by
  induction xs with
  | nil => simp [sum,Expr.loads]
  | cons i xs ih =>
    change (f i).loads + (sum (xs.map f)).loads = (xs.length+1)*n
    rw [h,ih,Nat.succ_mul,Nat.add_comm]

private theorem loads_outgoing (d : ℕ) (I : Input) (dir : Bool) :
    (outgoing d I dir).loads = if dir then d*halfLoads I false else 0 := by
  cases dir with
  | false => rfl
  | true =>
    change (sum ((List.finRange d).map _)).loads = d*halfLoads I false
    rw [sum_loads _ _ _ (loads_half I false),List.length_finRange]

/-- Actual reads in the compiled dynamic expression, independent of machine
width, network size and field widths. Dynamic pointer loads are counted on
every occurrence. -/
theorem field_reads {r : ℕ} (d : ℕ) (I : Input) (dir : Bool) (j : Expr)
    (regs : ℕ → Fin r) (start : ℕ) :
    (((field d I dir j).compile regs start).map fun a => a.rhs.reads).sum =
      I.arenaBase.loads + I.node.loads + I.stride.loads + (if dir then d*halfLoads I false else 0) +
        d*(j.loads+halfLoads I dir) := by
  rw [Expr.compile_reads]
  have count (i : Fin d) : ((before j i).mul (I.half dir i)).loads = j.loads + halfLoads I dir := by
    change (before j i).loads + (I.half dir i).loads = _
    simp [before,Expr.sub,Expr.div,Expr.add,Expr.loads,loads_half]
  change (I.arenaBase.loads + (I.node.loads + I.stride.loads)) +
    ((outgoing d I dir).loads + (sum ((List.finRange d).map _)).loads) = _
  rw [loads_outgoing,sum_loads _ _ _ count,List.length_finRange]
  omega

/-- Compiling a static address reads only its preceding slots, with a single
additional inverse lookup for each incoming width. -/
theorem fieldStatic_reads {r : ℕ} (I : Input) (dir : Bool) (j : Fin d)
    (regs : ℕ → Fin r) (start : ℕ) :
    (((fieldStatic I dir j).compile regs start).map fun a => a.rhs.reads).sum =
      I.arenaBase.loads + I.node.loads + I.stride.loads + (if dir then d*halfLoads I false else 0) +
        j.val*halfLoads I dir := by
  rw [Expr.compile_reads]
  change (I.arenaBase.loads + (I.node.loads + I.stride.loads)) +
    ((outgoing d I dir).loads + (sum (((List.finRange d).take j.val).map _)).loads) = _
  rw [loads_outgoing,sum_loads _ _ _ (loads_half I dir),List.length_take,List.length_finRange,min_eq_left j.isLt.le]
  omega

end CompressorRecords.PortRefresh.ArgumentAddress

end VPVNP
end Computability
end OAI
