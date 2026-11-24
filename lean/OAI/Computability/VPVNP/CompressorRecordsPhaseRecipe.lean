import OAI.Computability.VPVNP.CompressorRecordsRowRecipe
import OAI.Computability.VPVNP.CompressorRecordsController
import Mathlib.Algebra.BigOperators.Fin

/-!
# Compiling current-level formulas to native row planners

Expressions can read the level pointer, the five controller ports, and memory
at computed addresses. The compiler allocates disjoint output registers and
reuses a bounded scratch interval between formulas. Natural literals are
synthesized from their binary digits using word additions. Every read finishes
before the row writer installs its first field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PhaseRecipe

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM RowRecipe
open scoped Fin.CommRing

variable {w r g : ℕ}

/-- A word formula for planning a directory row from constants, the controller's five public
words, the current level pointer, memory loads and RAM binary operations. -/
inductive Expr where
  | lit (value : ℕ)
  | publicWord (index : Fin 5)
  | state
  | load (address : Expr)
  | binary (op : BinaryOp) (left right : Expr)

/-- Compute the formula's machine word in the current level and entry memory. A load reads
memory at the address obtained by evaluating its subexpression. -/
def Expr.eval (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) : Expr → Word w
  | .lit n => (n : Word w)
  | .publicWord i => pub i
  | .state => state
  | .load a => m (a.eval pub state m).val
  | .binary op a b => op.eval (a.eval pub state m) (b.eval pub state m)

/-- Form the sum of two planner expressions using machine-word addition. -/
def Expr.add := Expr.binary .add
/-- Form the product of two planner expressions using machine-word multiplication. -/
def Expr.mul := Expr.binary .mul
/-- Subtract the second planner expression from the first at the machine's word width. -/
def Expr.sub := Expr.binary .sub
/-- Form the unsigned integer quotient of the two word values computed by planner expressions. -/
def Expr.div := Expr.binary .div
/-- Form the unsigned remainder of the first planner expression's value modulo the second's. -/
def Expr.mod := Expr.binary .mod
/-- Address expression for field offset `i` from the current level header, whose base is
carried in persistent state. -/
def Expr.headerAddress (i : ℕ) := Expr.state.add (.lit i)
/-- Load a level-header field at the given word offset from the current state pointer. -/
def Expr.header (i : ℕ) := Expr.load (Expr.headerAddress i)
/-- Address of the directory row to publish, computed as the directory base plus the stored
ordinal times the row width `g + 3`. -/
def Expr.rowBase (g : ℕ) := (Expr.publicWord 1).add ((Expr.load (.publicWord 2)).mul (.lit (g+3)))

theorem eval_rowBase (g : ℕ) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    (Expr.rowBase g).eval pub s m = Controller.rowBase g pub m := rfl

/-- Number of consecutive scratch registers used to compile this expression. Binary operations
keep the left result while compiling the right operand one register later. -/
def Expr.slots : Expr → ℕ
  | .lit _ => 2
  | .publicWord _ | .state => 1
  | .load a => a.slots
  | .binary _ a b => max a.slots (1+b.slots)

theorem Expr.slots_pos (e : Expr) : 0 < e.slots := by induction e <;> simp_all [Expr.slots]

private def run (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (ls : List (Assign r 5)) (rs : Regs w r) := (evaluate pub s m ls rs).2

private theorem run_append (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (as bs : List (Assign r 5)) (rs : Regs w r) :
    run pub s m (as++bs) rs = run pub s m bs (run pub s m as rs) := by
  induction as generalizing rs with
  | nil => rfl
  | cons a as ih => exact ih _

private theorem run_single (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (a : Assign r 5) (rs : Regs w r) :
    run pub s m [a] rs = Function.update rs a.dst (a.rhs.value pub s m rs) := rfl

private def digits (dst one : Fin r) (n : ℕ) : List (Assign r 5) :=
  if n = 0 then [⟨dst,.literal 0⟩]
  else digits dst one (n/2) ++ [⟨dst,.binary .add dst dst⟩] ++
    (if n%2 = 0 then [] else [⟨dst,.binary .add dst one⟩])
termination_by n
decreasing_by omega

private theorem digits_keep (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (dst one : Fin r) (n : ℕ) (rs : Regs w r) (j : Fin r) (hj : j ≠ dst) :
    run pub s m (digits dst one n) rs j = rs j := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [digits]
    by_cases hn : n = 0
    · simp [hn, run_single, Function.update_of_ne hj]
    · have hl := ih (n/2) (by omega)
      by_cases hb : n%2 = 0 <;> simp only [hn,hb,↓reduceIte,List.append_nil,run_append,run_single,Function.update_of_ne hj,hl]

private theorem digits_value (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (dst one : Fin r) (ne : one ≠ dst) (n : ℕ) (rs : Regs w r) (ho : rs one = 1) :
    run pub s m (digits dst one n) rs dst = (n : Word w) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [digits]
    by_cases hn : n = 0
    · subst n; simp [run_single, RHS.value]
    have hv := ih (n/2) (by omega)
    have keep := digits_keep pub s m dst one (n/2) rs one ne
    by_cases hb : n%2 = 0
    · simp only [hn, hb, ↓reduceIte, List.append_nil, run_append, run_single, RHS.value, BinaryOp.eval,
        Function.update_self, hv]
      rw [← Nat.cast_add, show n/2+n/2 = n by omega]
    · simp only [hn, hb, ↓reduceIte, run_append, run_single, RHS.value, BinaryOp.eval, Function.update_self,
        Function.update_of_ne ne, hv, keep, ho]
      rw [← Nat.cast_add, ← Nat.cast_one (R := Word w), ← Nat.cast_add, show n/2+n/2+1 = n by omega]

/-- The scratch register at `start` holds the result. A right subexpression
begins one register later and may reuse the left subexpression's temporaries. -/
def Expr.compile (slot : ℕ → Fin r) (start : ℕ) : Expr → List (Assign r 5)
  | .lit n => [⟨slot (start+1),.literal 1⟩] ++ digits (slot start) (slot (start+1)) n
  | .publicWord i => [⟨slot start,.publicWord i⟩]
  | .state => [⟨slot start,.state⟩]
  | .load a => a.compile slot start ++ [⟨slot start,.read (slot start)⟩]
  | .binary op a b => a.compile slot start ++ b.compile slot (start+1) ++
      [⟨slot start,.binary op (slot start) (slot (start+1))⟩]

private theorem compile_keep (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) (e : Expr)
    (slot : ℕ → Fin r) (start : ℕ) (rs : Regs w r) (j : Fin r)
    (free : ∀ i, start ≤ i → i < start+e.slots → j ≠ slot i) :
    run pub s m (e.compile slot start) rs j = rs j := by
  induction e generalizing start rs with
  | lit n =>
    have h0 := free start le_rfl (by simp [Expr.slots])
    have h1 := free (start+1) (by omega) (by simp [Expr.slots])
    rw [Expr.compile, run_append, digits_keep _ _ _ _ _ _ _ _ h0, run_single, Function.update_of_ne h1]
  | state | publicWord _ =>
    simp [Expr.compile, run_single, Function.update_of_ne (free start le_rfl (by simp [Expr.slots]))]
  | load a ih =>
    have h0 := free start le_rfl (by have := a.slots_pos; simp [Expr.slots, this])
    simp [Expr.compile, run_append, run_single, Function.update_of_ne h0, ih start rs free]
  | binary op a b ha hb =>
    have fL : ∀ i, start ≤ i → i < start+a.slots → j ≠ slot i :=
      fun i lo hi ↦ free i lo (by change i < start+max a.slots (1+b.slots); omega)
    have fR : ∀ i, start+1 ≤ i → i < start+1+b.slots → j ≠ slot i :=
      fun i lo hi ↦ free i (by omega) (by change i < start+max a.slots (1+b.slots); omega)
    have h0 := fL start le_rfl (by have := a.slots_pos; omega)
    rw [Expr.compile, run_append, run_append, run_single, Function.update_of_ne h0, hb _ _ fR, ha _ _ fL]

private theorem compile_value (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) (e : Expr)
    (slot : ℕ → Fin r) (cap start : ℕ) (rs : Regs w r)
    (room : start+e.slots ≤ cap) (inj : ∀ i < cap, ∀ j < cap, slot i = slot j → i = j) :
    run pub s m (e.compile slot start) rs (slot start) = e.eval pub s m := by
  induction e generalizing start rs with
  | lit n =>
    have span : start+2 ≤ cap := room
    have ne : slot (start+1) ≠ slot start := fun h ↦ by have := inj _ (by omega) _ (by omega) h; omega
    rw [Expr.compile, run_append]
    exact digits_value _ _ _ _ _ ne _ _ (by simp [run_single, RHS.value])
  | state | publicWord _ => simp [Expr.compile, run_single, Expr.eval, RHS.value]
  | load a ih =>
    simp [Expr.compile, run_append, run_single, Expr.eval, RHS.value, ih start rs room]
  | binary op a b ha hb =>
    have span : start+max a.slots (1+b.slots) ≤ cap := room
    have hL := ha start rs (by omega)
    let mid := run pub s m (a.compile slot start) rs
    have hR := hb (start+1) mid (by omega)
    have keep : run pub s m (b.compile slot (start+1)) mid (slot start) = mid (slot start) := by
      apply compile_keep
      intro i lo hi he
      have := inj start (by omega) i (by omega) he
      omega
    rw [Expr.compile, run_append, run_append, run_single, Function.update_self]
    change op.eval (run pub s m (b.compile slot (start+1)) mid (slot start))
      (run pub s m (b.compile slot (start+1)) mid (slot (start+1))) = _
    rw [keep, hR, show mid (slot start) = _ from hL]
    rfl

/-- Number of external reads when evaluating an expression. Repeated occurrences
are counted separately, including repeated loads of the same header field. -/
def Expr.loads : Expr → ℕ
  | .lit _ | .publicWord _ | .state => 0
  | .load a => a.loads+1
  | .binary _ a b => a.loads+b.loads

private def readCount (ls : List (Assign r 5)) := (ls.map fun a ↦ a.rhs.reads).sum

private theorem readCount_append (a b : List (Assign r 5)) : readCount (a++b) = readCount a + readCount b := by
  simp [readCount]

private theorem digits_reads (dst one : Fin r) (n : ℕ) : readCount (digits dst one n) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [digits]
    by_cases hn : n = 0
    · simp [hn,readCount,RHS.reads]
    · have h := ih (n/2) (by omega)
      by_cases hb : n%2 = 0 <;> simp only [hn,hb,↓reduceIte,readCount_append,h] <;> rfl

theorem Expr.compile_reads (e : Expr) (slot : ℕ → Fin r) (start : ℕ) :
    ((e.compile slot start).map fun a ↦ a.rhs.reads).sum = e.loads := by
  change readCount _ = _
  induction e generalizing start with
  | lit n => rw [Expr.compile,readCount_append,digits_reads]; rfl
  | state | publicWord _ => rfl
  | load a ih => rw [Expr.compile,readCount_append,ih]; rfl
  | binary op a b ha hb => rw [Expr.compile,readCount_append,readCount_append,ha,hb]; rfl

/-- Parameters occupy a full catalog-width row, including any padding. -/
structure Phase (g : ℕ) where
  /-- Numeric worker tag written at the start of the directory row so the launcher can select
  the pass. -/
  tag : ℕ
  /-- Expression for the worker's first cursor, stored immediately after its tag. -/
  initial : Expr
  /-- Expression for the exclusive cursor bound at which the worker scan returns to the
  controller. -/
  stop : Expr
  /-- Expressions for the worker's public operands in directory order, including any padding to
  the catalog width. -/
  params : Fin g → Expr

/-- Pad a worker's finite operand vector at the high end of the row. -/
def Phase.ofParams {k g : ℕ} (_ : k ≤ g) (tag : ℕ) (initial stop : Expr) (params : Fin k → Expr) : Phase g :=
  ⟨tag,initial,stop,fun i ↦ if h : i.val < k then params ⟨i.val,h⟩ else .lit 0⟩

private def Phase.formulas (P : Phase g) : Fin (g+4) → Expr :=
  Fin.cons (.rowBase g) (Fin.cons (.lit P.tag) (Fin.cons P.initial (Fin.cons P.stop P.params)))

private def Phase.scratch (P : Phase g) := Finset.univ.sup fun j ↦ (P.formulas j).slots
/-- Number of planner registers needed for the row address, its `g + 3` fields and the largest
scratch interval used by any one formula. -/
def Phase.registerCount (P : Phase g) := P.scratch + g + 4

private def Phase.out (P : Phase g) (j : Fin (g+4)) : Fin P.registerCount :=
  ⟨j.val,by have := j.isLt; unfold Phase.registerCount; omega⟩

private def Phase.slot (P : Phase g) (i : ℕ) : Fin P.registerCount :=
  ⟨(g+4+i) % P.registerCount, Nat.mod_lt _ (by unfold Phase.registerCount; omega)⟩

private theorem slot_val (P : Phase g) {i : ℕ} (hi : i < P.scratch) : (P.slot i).val = g+4+i :=
  Nat.mod_eq_of_lt (by unfold Phase.registerCount; omega)

private theorem room (P : Phase g) (i : Fin (g+4)) : (P.formulas i).slots ≤ P.scratch :=
  Finset.le_sup (f := fun j ↦ (P.formulas j).slots) (Finset.mem_univ i)

private def Phase.emit (P : Phase g) (i : Fin (g+4)) : List (Assign P.registerCount 5) :=
  (P.formulas i).compile P.slot 0 ++ [⟨P.out i,.copy (P.slot 0)⟩]

private theorem emit_value (P : Phase g) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (rs : Regs w P.registerCount) (i j : Fin (g+4)) :
    run pub s m (P.emit i) rs (P.out j) =
      if i = j then (P.formulas i).eval pub s m else rs (P.out j) := by
  have enough := room P i
  rw [Phase.emit, run_append, run_single]
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, Function.update_self, RHS.value]
    apply compile_value _ _ _ _ _ P.scratch _ _ (by omega)
    intro x hx y hy he
    have eqn := congrArg Fin.val he
    rw [slot_val P hx,slot_val P hy] at eqn
    omega
  · have hne : P.out j ≠ P.out i := fun e ↦ hij (Fin.ext (congrArg (fun t : Fin P.registerCount ↦ t.val) e.symm))
    simp only [hij,↓reduceIte,Function.update_of_ne hne]
    apply compile_keep
    intro t _ h e
    have eqn := congrArg Fin.val e
    rw [slot_val P (by omega)] at eqn
    change j.val = g+4+t at eqn
    have := j.isLt
    omega

private theorem emit_list (P : Phase g) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (rs : Regs w P.registerCount) (ls : List (Fin (g+4))) (j : Fin (g+4)) :
    run pub s m (ls.flatMap P.emit) rs (P.out j) =
      if j ∈ ls then (P.formulas j).eval pub s m else rs (P.out j) := by
  induction ls generalizing rs with
  | nil => simp [run,evaluate]
  | cons i ls ih =>
    rw [List.flatMap_cons, run_append, ih, emit_value]
    by_cases e : i = j
    · subst i; simp
    · by_cases h : j ∈ ls <;> simp [h,e,Ne.symm e]

/-- One fixed finite native recipe for a phase of the online calendar. -/
def Phase.recipe (P : Phase g) : Recipe P.registerCount 5 g where
  lines := (List.finRange (g+4)).flatMap P.emit
  dest := P.out 0
  tag := P.out (0 : Fin (g+3)).succ
  start := P.out (0 : Fin (g+2)).succ.succ
  stop := P.out (0 : Fin (g+1)).succ.succ.succ
  params i := P.out i.succ.succ.succ.succ

private theorem emit_reads (P : Phase g) (i : Fin (g+4)) :
    readCount (P.emit i) = (P.formulas i).loads := by
  rw [Phase.emit,readCount_append,show readCount ((P.formulas i).compile P.slot 0) = _ from
    Expr.compile_reads _ _ _]
  rfl

/-- The row address contributes one ordinal read. All remaining reads arise
from the starting cursor, stopping cursor, and padded public operands. -/
theorem Phase.recipe_reads (P : Phase g) :
    P.recipe.reads = 1 + P.initial.loads + P.stop.loads + (List.ofFn fun i ↦ (P.params i).loads).sum := by
  have fold (ls : List (Fin (g+4))) :
      readCount (ls.flatMap P.emit) = (ls.map fun i ↦ (P.formulas i).loads).sum := by
    induction ls with
    | nil => rfl
    | cons i ls ih => rw [List.flatMap_cons,readCount_append,emit_reads,ih]; rfl
  change readCount ((List.finRange (g+4)).flatMap P.emit) = _
  rw [fold, ← List.ofFn_eq_map]
  simp only [Phase.formulas,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,Expr.loads,Expr.rowBase,
    Expr.add,Expr.mul,List.sum_cons]
  omega

/-- Evaluate the directory row in the current header and memory, yielding the tag, starting
cursor, exclusive stop and all parameter words in storage order. -/
def Phase.words (P : Phase g) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :=
  (P.tag : Word w) :: P.initial.eval pub s m :: P.stop.eval pub s m ::
    List.ofFn (fun i ↦ (P.params i).eval pub s m)

private theorem eval_out (P : Phase g) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) (i : Fin (g+4)) :
    P.recipe.values pub s m (P.out i) = (P.formulas i).eval pub s m := by
  change run pub s m ((List.finRange _).flatMap P.emit) _ _ = _
  rw [emit_list]
  simp

theorem recipe_address (P : Phase g) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    P.recipe.address pub s m = Controller.rowBase g pub m := by
  change P.recipe.values pub s m (P.out 0) = _
  rw [eval_out]
  simp [Phase.formulas, eval_rowBase]

theorem recipe_words (P : Phase g) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    P.recipe.words pub s m = P.words pub s m := by
  simp only [Recipe.words, Recipe.fields, Phase.words, List.map_cons, List.map_ofFn]
  change P.recipe.values pub s m (P.out (0 : Fin (g+3)).succ) ::
    P.recipe.values pub s m (P.out (0 : Fin (g+2)).succ.succ) ::
    P.recipe.values pub s m (P.out (0 : Fin (g+1)).succ.succ.succ) ::
    List.ofFn (fun i : Fin g ↦ P.recipe.values pub s m (P.out i.succ.succ.succ.succ)) = _
  simp only [eval_out, Phase.formulas, Fin.cons_succ, Fin.cons_zero, Expr.eval]

/-- A completed native planner accepts with the computed worker row installed in
the current directory slot. All expression loads see the input memory. -/
theorem execute_phase (P : Phase g) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (cap : ℕ) (budget : P.recipe.code.length < cap)
    (fit : (Controller.rowBase g pub m).val + (g+3) ≤ 2^w) :
    let M := P.recipe.acceptTable.instantiate w pub
    let es := (P.recipe.report pub s m).events
    execute M.program cap (M.program.start s) m [] = some ⟨es,none⟩ ∧
      Greedy.Stores (after m es) (Controller.rowBase g pub m) (P.words pub s m) ∧
      (∀ a, a < (Controller.rowBase g pub m).val ∨ (Controller.rowBase g pub m).val + (g+3) ≤ a →
        after m es a = m a) ∧
      countProbes es = P.recipe.reads+(g+3) ∧ choiceBits es = [] := by
  refine ⟨execute_accept P.recipe pub s m [] cap budget, ?_, ?_, (report_cost ..).2⟩
  · rw [← recipe_address P pub s m, ← recipe_words]
    exact row_stores _ _ _ _ (by rwa [recipe_address])
  · intro a ha
    exact row_outside P.recipe pub s m (by rwa [recipe_address]) a (by rwa [recipe_address])

private theorem stored_at (m : Memory w) (dest : Word w) (xs : List (Word w))
    (stored : Greedy.Stores m dest xs) (j : ℕ) (hj : j < xs.length) :
    m (dest+(j : Word w)).val = xs[j] := by
  induction xs generalizing dest j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => simpa using stored.1
    | succ j =>
      have h := ih (dest+1) stored.2 j (by simpa using hj)
      have eqn : dest+((j+1 : ℕ) : Word w) = (dest+1)+(j : Word w) := by
        rw [Nat.cast_add,Nat.cast_one]; ac_rfl
      simpa only [eqn,List.getElem_cons_succ] using h

/-- Pointwise interface to the launcher's row reader. The last equality uses
the same origin and offset as the worker parameter frame. -/
theorem row_fields (P : Phase g) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (fit : (Controller.rowBase g pub m).val + (g+3) ≤ 2^w) :
    let base := Controller.rowBase g pub m
    let out := after m (P.recipe.report pub s m).events
    out base.val = (P.tag : Word w) ∧ out (base+1).val = P.initial.eval pub s m ∧
      out (base+2).val = P.stop.eval pub s m ∧
      ∀ j : Fin g, Controller.field (base+2) out (j.val+1) = (P.params j).eval pub s m := by
  let base := Controller.rowBase g pub m
  let out := after m (P.recipe.report pub s m).events
  have st := row_stores P.recipe pub s m (by rwa [recipe_address])
  rw [recipe_address,recipe_words] at st
  change Greedy.Stores out base ((P.tag : Word w) :: P.initial.eval pub s m :: P.stop.eval pub s m ::
    List.ofFn (fun i ↦ (P.params i).eval pub s m)) at st
  have two : base+1+1 = base+2 := by rw [add_assoc, one_add_one_eq_two]
  refine ⟨st.1,st.2.1,?_,?_⟩
  · simpa only [two] using st.2.2.1
  · intro j
    have h := stored_at out (base+1+1+1) _ st.2.2.2 j.val (by simp)
    have he : base+2+((j.val+1 : ℕ) : Word w) = (base+1+1+1)+(j.val : Word w) := by
      rw [two, Nat.cast_add, Nat.cast_one]; ac_rfl
    change out (base+2+((j.val+1 : ℕ) : Word w)).val = _
    rw [he]
    simpa only [List.getElem_ofFn] using h

theorem ofParams_value {k : ℕ} (hk : k ≤ g) (tag : ℕ) (initial stop : Expr)
    (v : Fin k → Expr) (i : Fin k) :
    (Phase.ofParams hk tag initial stop v).params (i.castLE hk) = v i := by
  simp [Phase.ofParams,i.isLt]

theorem ofParams_padding {k : ℕ} (hk : k ≤ g) (tag : ℕ) (initial stop : Expr)
    (v : Fin k → Expr) (i : Fin g) (hi : k ≤ i.val) :
    (Phase.ofParams hk tag initial stop v).params i = .lit 0 := by
  simp [Phase.ofParams,not_lt_of_ge hi]

/-- The seven pointer fields are in the native refresh visitor's public order:
old widths, bundle targets, port shifts, bundle totals, outgoing offsets,
incoming offsets, and incoming widths. -/
structure RefreshHeader where
  /-- Offset in the current level header of the vertex-count word used to compute the refresh
  scan length. -/
  vertices : ℕ
  /-- Offset of the degree word used both as the first refresh operand and to compute the
  numbers of bundles and slots. -/
  degree : ℕ
  /-- Offset of the residual-lane count used to expand each vertex and port into refresh
  bundles. -/
  residualLanes : ℕ
  /-- Offsets of the seven array pointers for old widths, bundle targets, port shifts, bundle
  totals, outgoing offsets, incoming offsets and incoming widths, in worker order. -/
  heads : Fin 7 → ℕ

/-- Planner expression multiplying the header's vertex count, degree and residual-lane count to
obtain the number of refresh bundles. -/
def RefreshHeader.bundles (H : RefreshHeader) :=
  ((Expr.header H.vertices).mul (.header H.degree)).mul (.header H.residualLanes)

/-- Planner expression for the exclusive end of the refresh scan, one degree-sized block of
slots per bundle. -/
def RefreshHeader.slots (H : RefreshHeader) := H.bundles.mul (.header H.degree)

/-- Plan a refresh scan from cursor zero to the slot count computed from the header. Its eight
public operands are the degree and the seven array pointers. -/
def refresh (tag : ℕ) (H : RefreshHeader) : Phase 8 where
  tag := tag
  initial := .lit 0
  stop := H.slots
  params := Fin.cons (.header H.degree) (fun i ↦ Expr.header (H.heads i))

/-- Read the machine word at offset `i` from the level header pointed to by the persistent
state. -/
def headerCell (m : Memory w) (s : Word w) (i : ℕ) := m (s+(i : Word w)).val

/-- Read the refresh worker's eight public words from the current header, placing the degree
first and the seven array pointers after it. -/
def refreshPublic (H : RefreshHeader) (m : Memory w) (s : Word w) : Fin 8 → Word w :=
  Fin.cons (headerCell m s H.degree) (fun i ↦ headerCell m s (H.heads i))

theorem refresh_words (tag : ℕ) (H : RefreshHeader) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    let V := headerCell m s H.vertices
    let D := headerCell m s H.degree
    let R := headerCell m s H.residualLanes
    let B := V*D*R
    (refresh tag H).recipe.words pub s m = (tag : Word w) :: 0 :: B*D :: List.ofFn (refreshPublic H m s) := by
  rw [recipe_words]
  change _ :: _ :: _ :: List.ofFn _ = _ :: _ :: _ :: List.ofFn _
  congr 3

/-- With the physical slot count in range the word multiplication computes the
natural exclusive stop, including zero vertices, degree or residual lanes. -/
theorem refresh_stop_val (tag : ℕ) (H : RefreshHeader) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (fit : (headerCell m s H.vertices).val * (headerCell m s H.degree).val *
      (headerCell m s H.residualLanes).val * (headerCell m s H.degree).val < 2^w) :
    ((refresh tag H).stop.eval pub s m).val = (headerCell m s H.vertices).val * (headerCell m s H.degree).val *
      (headerCell m s H.residualLanes).val * (headerCell m s H.degree).val := by
  change (headerCell m s H.vertices * headerCell m s H.degree * headerCell m s H.residualLanes *
    headerCell m s H.degree).val = _
  simp only [Fin.val_mul, Nat.mod_mul_mod, Nat.mod_eq_of_lt fit]

/-- The accepting planner for the refresh worker constructs the actual eight
public operands directly from the header and supplies the computed segment count. -/
theorem execute_refresh (tag : ℕ) (H : RefreshHeader) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (cap : ℕ) (budget : (refresh tag H).recipe.code.length < cap)
    (fit : (Controller.rowBase 8 pub m).val + 11 ≤ 2^w) :
    let R := (refresh tag H).recipe
    let M := R.acceptTable.instantiate w pub
    let D := headerCell m s H.degree
    let B := headerCell m s H.vertices * D * headerCell m s H.residualLanes
    execute M.program cap (M.program.start s) m [] = some ⟨(R.report pub s m).events, none⟩ ∧
      Greedy.Stores (after m (R.report pub s m).events) (Controller.rowBase 8 pub m)
        ((tag : Word w) :: 0 :: B*D :: List.ofFn (refreshPublic H m s)) := by
  obtain ⟨he,hs,_⟩ := execute_phase (refresh tag H) pub s m cap budget fit
  refine ⟨he,?_⟩
  rw [← recipe_words, refresh_words] at hs
  exact hs

end CompressorRecords.PhaseRecipe

end VPVNP
end Computability
end OAI
