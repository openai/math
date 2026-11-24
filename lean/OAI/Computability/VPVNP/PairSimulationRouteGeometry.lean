import OAI.Computability.VPVNP.CursorRouteChecker
import OAI.Computability.VPVNP.PrimedCounterGuessWord
import OAI.Computability.VPVNP.PairSimulationRouteSuccessorWord

/-!
# Native mask geometry at a cursor position

The successor entry constructs its low-bit mask and tests the site against
the unique nonwrapping successor. The sorting entry constructs a one-bit
mask from phase and step. Both entries extract the outgoing and incoming
bits from that mask, including the last cursor on arrival at cursor zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteGeometry

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork
open scoped Fin.CommRing

variable {D W p r k : ℕ}

/-- Value of the outer counter at this field, either a successor class or a sorting phase. -/
def outerIndex : RAMSystem D → ℕ
  | .inl k => k.val
  | .inr l => l.phase

/-- Entry row for the system's geometry calculation. -/
def entry : RAMSystem D → Fin 30
  | .inl _ => 0
  | .inr _ => 14

/-- Number of native instructions executed along the selected entry path. -/
def ticks : RAMSystem D → ℕ
  | .inl _ => 26
  | .inr _ => 16

/-- At cursor zero a failed successor test clamps the selected outgoing
field. Every other cursor compares the two selected fields. -/
def mode [NeZero D] (v : Position D) (s : RAMSystem D) : ℕ :=
  if v.1 = 0 then
    match s with
    | .inl j => if v.2.val + 1 < 2 ^ D ∧
        v.2.val ^^^ (v.2.val + 1) = (systemMask (.inl j)).val then 0 else 1
    | .inr _ => 0
  else 2

private inductive Operand
  | zero | one
  | binary (op : BinaryOp) (lhs rhs : Fin 12)

/-- Rows 0–13 generate a successor mask and the inactive-source flag.
Rows 14–17 generate a sorting mask and clear that flag. Rows 18–29 select
the mode, form the cyclic predecessor, and read the two mask bits. -/
private def row : Fin 30 → Fin 12 × Operand :=
  ![(8, .one), (9, .binary .shiftLeft 8 3), (9, .binary .add 9 9),
    (9, .binary .sub 9 8), (10, .binary .add 1 8), (10, .binary .bitXor 1 10),
    (10, .binary .bitXor 10 9), (10, .binary .div 10 10), (11, .binary .shiftLeft 8 2),
    (11, .binary .sub 11 8), (11, .binary .bitXor 11 1), (11, .binary .div 11 11),
    (11, .binary .sub 8 11), (7, .binary .bitOr 10 11),
    (8, .one), (10, .binary .sub 3 4), (9, .binary .shiftLeft 8 10), (7, .zero),
    (10, .binary .div 0 0), (11, .binary .sub 8 10), (7, .binary .mul 7 11),
    (10, .binary .add 10 10), (7, .binary .add 7 10), (11, .binary .mul 11 2),
    (11, .binary .add 11 0), (11, .binary .sub 11 8), (5, .binary .shiftRight 9 0),
    (5, .binary .bitAnd 5 8), (6, .binary .shiftRight 9 11), (6, .binary .bitAnd 6 8)]

private def next (pc : Fin 30 → Fin p) (done : Fin p) (i : Fin 30) : Fin p :=
  if i = 13 then pc 18 else if h : i.val + 1 < 30 then pc ⟨i.val + 1, h⟩ else done

/-- The finite native geometry table with relocated register operands and continuations. -/
def instruction (pc : Fin 30 → Fin p) (reg : Fin 12 ↪ Fin r) (done : Fin p)
    (i : Fin 30) : Instr W p r k :=
  let dst := reg (row i).1
  let j := next pc done i
  match (row i).2 with
  | .zero => .constant dst 0 j
  | .one => .constant dst 1 j
  | .binary op lhs rhs => .binary op dst (reg lhs) (reg rhs) j

theorem resize_instruction (pc : Fin 30 → Fin p) (reg : Fin 12 ↪ Fin r) (done : Fin p)
    (i : Fin 30) :
    (instruction (W := 1) (k := k) pc reg done i).resize W = instruction pc reg done i := by
  unfold instruction
  cases (row i).2 <;> rfl

/-- Every row of the geometry table occurs in the enclosing machine. -/
def Linked (M : Machine W p r k) (pc : Fin 30 → Fin p) (reg : Fin 12 ↪ Fin r) (done : Fin p) :=
  ∀ i, M.code (pc i) = instruction pc reg done i

/-- Registers outside the three results and four scratch slots. -/
def Preserved (reg : Fin 12 ↪ Fin r) (a : Fin r) : Prop :=
  ∀ i : Fin 12, 5 ≤ i.val → a ≠ reg i

/-- Position, dimension and loop counters supplied by the routing scheduler. -/
structure Ready (reg : Fin 12 ↪ Fin r) (v : Position D) (s : RAMSystem D)
    (c : Config W p r) : Prop where
  cursor : c.reg (reg 0) = (v.1.val : Word W)
  site : c.reg (reg 1) = (v.2.val : Word W)
  dimension : c.reg (reg 2) = (D : Word W)
  outer : c.reg (reg 3) = (outerIndex s : Word W)
  step : ∀ l, s = .inr l → c.reg (reg 4) = (l.step : Word W)

/-- The selected sides and mode at the continuation, together with the register and memory frame. -/
structure Result [NeZero D] (reg : Fin 12 ↪ Fin r) (done : Fin p) (v : Position D)
    (s : RAMSystem D) (c d : Config W p r) : Prop where
  pc : d.pc = done
  outgoing : d.reg (reg 5) = (((systemMask s).val.testBit v.1.val).toNat : Word W)
  incoming : d.reg (reg 6) =
    (((systemMask s).val.testBit ((finRotate D).symm v.1).val).toNat : Word W)
  modeWord : d.reg (reg 7) = (mode v s : Word W)
  frame : ∀ a, Preserved reg a → d.reg a = c.reg a
  memory : d.privateMem = c.privateMem
  persistent : d.persistent = c.persistent

private def Operand.value (get : Fin 12 → Word W) : Operand → Word W
  | .zero => 0
  | .one => 1
  | .binary op lhs rhs => op.eval (get lhs) (get rhs)

private def advance (pc : Fin 30 → Fin p) (reg : Fin 12 ↪ Fin r) (done : Fin p) (i : Fin 30)
    (c : Config W p r) :=
  c.put (next pc done i) (reg (row i).1) ((row i).2.value (c.reg ∘ reg))

variable {M : Machine W p r k} {pc : Fin 30 → Fin p} {reg : Fin 12 ↪ Fin r} {done : Fin p}

private theorem local_step (hl : Linked M pc reg done) (i : Fin 30) (c : Config W p r)
    (hc : c.pc = pc i) : M.program.step c = .localStep (advance pc reg done i c) := by
  change (M.code c.pc).run M.publicData c = _
  rw [hc, hl]
  unfold instruction advance
  cases (row i).2 <;> rfl

private def walk (pc : Fin 30 → Fin p) (reg : Fin 12 ↪ Fin r) (done : Fin p)
    (is : List (Fin 30)) (c : Config W p r) :=
  is.foldl (fun d i => advance pc reg done i d) c

private theorem advance_frame (i : Fin 30) (c : Config W p r) (a : Fin r)
    (ha : Preserved reg a) : (advance pc reg done i c).reg a = c.reg a := by
  have dst : ∀ j : Fin 30, 5 ≤ (row j).1.val := by decide
  exact Function.update_of_ne (ha _ (dst i)) _ _

private theorem walk_frame (is : List (Fin 30)) (c : Config W p r) (a : Fin r)
    (ha : Preserved reg a) : (walk pc reg done is c).reg a = c.reg a := by
  induction is generalizing c with
  | nil => rfl
  | cons i is ih => exact (ih _).trans (advance_frame _ _ _ ha)

private def successors : List (Fin 30) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13]
private def sorting : List (Fin 30) := [14,15,16,17]
private def finish : List (Fin 30) := [18,19,20,21,22,23,24,25,26,27,28,29]

private theorem walk_prefix (hl : Linked M pc reg done) (is : List (Fin 30))
    (c : Config W p r)
    (linked : List.IsChain (fun i j => next pc done i = pc j) is)
    (atHead : ∀ i ∈ is.head?, c.pc = pc i) :
    Prefix M c (List.replicate is.length .tick) (walk pc reg done is c) := by
  induction is generalizing c with
  | nil => exact .nil _
  | cons i is ih =>
    refine .tick (local_step hl i c (atHead i rfl)) (ih _ ?_ ?_)
    · exact linked.tail
    · cases is with
      | nil => simp
      | cons j js =>
        intro a ha
        have he : a = j := Option.some.inj ha.symm
        subst a
        exact (List.isChain_cons_cons.mp linked).1

private theorem native_path (hl : Linked M pc reg done) (s : RAMSystem D) (c : Config W p r)
    (hc : c.pc = pc (entry s)) :
    let first := match s with | .inl _ => successors | .inr _ => sorting
    Prefix M c (List.replicate (ticks s) .tick) (walk pc reg done finish (walk pc reg done first c)) := by
  have hf : List.IsChain (fun i j => next pc done i = pc j) finish := by
    simp only [finish, List.isChain_cons_cons, List.IsChain.singleton, and_true]
    repeat' first | rfl | constructor
  cases s with
  | inl k =>
    refine (walk_prefix hl successors c ?_ ?_).append (walk_prefix hl finish _ hf ?_)
    · simp only [successors, List.isChain_cons_cons, List.IsChain.singleton, and_true]
      repeat' first | rfl | constructor
    · intro i hi
      cases Option.some.inj hi
      exact hc
    · intro i hi
      cases Option.some.inj hi
      rfl
  | inr l =>
    refine (walk_prefix hl sorting c ?_ ?_).append (walk_prefix hl finish _ hf ?_)
    · simp only [sorting, List.isChain_cons_cons, List.IsChain.singleton, and_true]
      repeat' first | rfl | constructor
    · intro i hi
      cases Option.some.inj hi
      exact hc
    · intro i hi
      cases Option.some.inj hi
      rfl

private theorem read_row (j : Fin 12) (l : Fin 30) (c : Config W p r) :
    (advance pc reg done l c).reg (reg j) =
      if j = (row l).1 then (row l).2.value (c.reg ∘ reg) else c.reg (reg j) := by
  simp only [advance, Config.put, Function.update_apply, reg.injective.eq_iff]

private abbrev shl (x : Word W) := BinaryOp.shiftLeft.eval (1 : Word W) x
private abbrev nz (x : Word W) := BinaryOp.div.eval x x
private abbrev xor (x y : Word W) := BinaryOp.bitXor.eval x y
private abbrev flagOr (x y : Word W) := BinaryOp.bitOr.eval x y

private theorem successor_values (c : Config W p r) :
    let q := walk pc reg done successors c
    let i := c.reg (reg 3)
    let x := c.reg (reg 1)
    let m := shl i + shl i - 1
    q.reg (reg 8) = 1 ∧ q.reg (reg 9) = m ∧
      q.reg (reg 7) = flagOr (nz (xor (xor x (x + 1)) m))
        (1 - nz (xor (shl (c.reg (reg 2)) - 1) x)) := by
  dsimp only [walk, successors, List.foldl]
  simp [read_row, row, Operand.value, Function.comp_apply, shl, nz, xor, flagOr, BinaryOp.eval]

private theorem sorting_values (c : Config W p r) :
    let q := walk pc reg done sorting c
    q.reg (reg 8) = 1 ∧ q.reg (reg 9) = shl (c.reg (reg 3) - c.reg (reg 4)) ∧
      q.reg (reg 7) = 0 := by
  dsimp only [walk, sorting, List.foldl]
  simp [read_row, row, Operand.value, Function.comp_apply, shl, BinaryOp.eval]

private abbrev readBit (x i : Word W) :=
  BinaryOp.bitAnd.eval (BinaryOp.shiftRight.eval x i) 1

private theorem finish_values (q : Config W p r) (h1 : q.reg (reg 8) = 1) :
    let d := walk pc reg done finish q
    let cur := q.reg (reg 0)
    let nonzero := nz cur
    let atZero := 1 - nonzero
    let prev := atZero * q.reg (reg 2) + cur - 1
    let mask := q.reg (reg 9)
    d.reg (reg 5) = readBit mask cur ∧ d.reg (reg 6) = readBit mask prev ∧
      d.reg (reg 7) = q.reg (reg 7) * atZero + (nonzero + nonzero) := by
  dsimp only [walk, finish, List.foldl]
  simp [read_row, row, Operand.value, Function.comp_apply, readBit, nz, BinaryOp.eval, h1]
  rfl

private def initialClamp (x : Site D) : RAMSystem D → Bool
  | .inl j => decide (¬ (x.val + 1 < 2 ^ D ∧ x.val ^^^ (x.val + 1) = (systemMask (.inl j)).val))
  | .inr _ => false

private def startRows : RAMSystem D → List (Fin 30)
  | .inl _ => successors
  | .inr _ => sorting

private theorem kept_input (j : Fin 12) (hj : j.val < 5) : Preserved reg (reg j) := by
  intro i hi he
  have := congrArg Fin.val (reg.injective he)
  omega

private theorem prev_zero [NeZero D] : ((finRotate D).symm 0).val = D - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne D)
  have eq : (finRotate (n+1)).symm 0 = Fin.last n :=
    (finRotate (n+1)).symm_apply_eq.mpr finRotate_last.symm
  simp [eq]

private theorem cursor_values [NeZero D] (v : Position D) (s : RAMSystem D) (hw : D < W) :
    let cur := (v.1.val : Word W)
    let z := nz cur
    (1 - z) * (D : Word W) + cur - 1 = (((finRotate D).symm v.1).val : Word W) ∧
      ((initialClamp v.2 s).toNat : Word W) * (1 - z) + (z + z) = (mode v s : Word W) := by
  dsimp only
  rw [show nz (v.1.val : Word W) = _ from
    RouteWord.div_self (v.1.isLt.trans (hw.trans Nat.lt_two_pow_self))]
  by_cases h : v.1 = 0
  · rw [h, Fin.val_zero, ite_eq_left rfl, prev_zero]
    have hD : 1 ≤ D := Nat.pos_of_ne_zero (NeZero.ne D)
    simp only [Nat.cast_zero, sub_zero, one_mul, add_zero, Nat.cast_sub hD, Nat.cast_one,
      mul_one, true_and]
    cases s with
    | inl j =>
      simp only [mode, h, ite_true, initialClamp]
      split <;> simp_all
    | inr l => simp [mode, h, initialClamp]
  · have hn : v.1.val ≠ 0 := Fin.val_ne_zero_iff.mpr h
    rw [ite_eq_right hn, coe_finRotate_symm_of_ne_zero h]
    simp [Nat.cast_sub (Nat.pos_of_ne_zero hn), mode, h]
    exact one_add_one_eq_two

private theorem final_values [NeZero D] (v : Position D) (s : RAMSystem D) (hw : D < W)
    (q : Config W p r) (hc : q.reg (reg 0) = (v.1.val : Word W))
    (hD : q.reg (reg 2) = (D : Word W)) (hone : q.reg (reg 8) = 1)
    (hm : q.reg (reg 9) = ((systemMask s).val : Word W))
    (hs : q.reg (reg 7) = ((initialClamp v.2 s).toNat : Word W)) :
    let d := walk pc reg done finish q
    d.reg (reg 5) = (((systemMask s).val.testBit v.1.val).toNat : Word W) ∧
    d.reg (reg 6) = (((systemMask s).val.testBit ((finRotate D).symm v.1).val).toNat : Word W) ∧
    d.reg (reg 7) = (mode v s : Word W) := by
  have ⟨hout, hin, hmode⟩ := finish_values (pc := pc) (done := done) q hone
  dsimp only at hout hin hmode ⊢
  rw [hc, hm] at hout
  rw [hc, hD, hm, (cursor_values v s hw).1] at hin
  rw [hc, hs, (cursor_values v s hw).2] at hmode
  have bound := (systemMask s).isLt.trans (Nat.pow_lt_pow_right (by decide) hw)
  exact ⟨hout.trans (RouteWord.maskBit (v.1.isLt.trans hw) bound),
    hin.trans (RouteWord.maskBit (((finRotate D).symm v.1).isLt.trans hw) bound), hmode⟩

private theorem sort_ready (v : Position D) (l : RAMLayout.Layer D) (hw : D < W)
    (c : Config W p r) (h : Ready reg v (.inr l) c) :
    let q := walk pc reg done sorting c
    q.reg (reg 8) = 1 ∧ q.reg (reg 9) = ((systemMask (.inr l)).val : Word W) ∧
      q.reg (reg 7) = ((initialClamp v.2 (.inr l)).toNat : Word W) := by
  have ⟨h1, hm, hs⟩ := sorting_values (pc := pc) (reg := reg) (done := done) c
  rw [h.outer, h.step l rfl] at hm
  change _ = shl ((l.phase : Word W) - (l.step : Word W)) at hm
  rw [← Nat.cast_sub l.step_le] at hm
  exact ⟨h1, hm.trans (RouteWord.shl_one (l.siteBit_lt.trans hw)), hs⟩

private theorem setup_ready (v : Position D) (s : RAMSystem D) (hw : D < W)
    (c : Config W p r) (h : Ready reg v s c) :
    let q := walk pc reg done (startRows s) c
    q.reg (reg 8) = 1 ∧ q.reg (reg 9) = ((systemMask s).val : Word W) ∧
      q.reg (reg 7) = ((initialClamp v.2 s).toNat : Word W) := by
  cases s with
  | inr l => exact sort_ready v l hw c h
  | inl j =>
    have ⟨h1, hm, hs⟩ := successor_values (pc := pc) (reg := reg) (done := done) c
    rw [h.outer] at hm
    rw [h.outer, h.dimension, h.site] at hs
    have geom := RouteWord.successor_values v.2 j hw
    exact ⟨h1, hm.trans geom.1, hs.trans geom.2⟩

/-- The two fixed entry paths compute every field's side flags and test mode
from the live system counters and position words. -/
theorem native [NeZero D] (hl : Linked M pc reg done) (v : Position D) (s : RAMSystem D)
    (hw : D < W) (c : Config W p r) (hc : c.pc = pc (entry s)) (h : Ready reg v s c) :
    ∃ d, Prefix M c (List.replicate (ticks s) .tick) d ∧ Result reg done v s c d := by
  let q := walk pc reg done (startRows s) c
  let d := walk pc reg done finish q
  have ⟨one, mask, clamp⟩ := setup_ready (pc := pc) (done := done) v s hw c h
  have cursor : q.reg (reg 0) = (v.1.val : Word W) :=
    (walk_frame _ _ _ (kept_input 0 (by decide))).trans h.cursor
  have dim : q.reg (reg 2) = (D : Word W) :=
    (walk_frame _ _ _ (kept_input 2 (by decide))).trans h.dimension
  have ⟨outgoing, incoming, modeWord⟩ :=
    final_values (pc := pc) (done := done) v s hw q cursor dim one mask clamp
  refine ⟨d, ?_, rfl, outgoing, incoming, modeWord, ?_, ?_, ?_⟩
  · cases s <;> exact native_path hl _ c hc
  · intro a ha
    exact (walk_frame _ q a ha).trans (walk_frame _ c a ha)
  · cases s <;> rfl
  · cases s <;> rfl

end PairSimulation.RouteGeometry

end VPVNP
end Computability
end OAI
