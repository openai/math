import OAI.Computability.VPVNP.PairSimulationInlineLiteral
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Lowering a static public bank to a fixed native instruction table

The enclosing machine supplies only code labels and register positions. Its public
words are available to other routines. Each source instruction occupies an equally long
block consisting of a local constant synthesis followed by the relocated operation.
The final operation has the source's branches, probes and halt behavior.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.InlinePublic

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {v w C p r k P R K : ℕ}

/-- A fixed bound covering every source immediate and every fixed public word. -/
def capacity (T : Template p r k) (bank : Fin k → ℕ) := 2 ^ T.literalWidth + ∑ i, bank i

/-- Native locations of the relocated code, source registers, and the two scratch words. -/
structure Placement (C p r P R : ℕ) where
  /-- Host code address for each source instruction and offset in its block of `C + 3`
  instructions. -/
  pc : Fin p → Fin (C + 3) → Fin P
  /-- Embed the source registers into the host register file for the relocated instruction. -/
  reg : Fin r ↪ Fin R
  /-- Scratch register initialized to one for the increments used to synthesize a fixed
  operand. -/
  unit : Fin R
  /-- Scratch register that accumulates the fixed operand before the relocated instruction
  runs. -/
  acc : Fin R
  distinct : unit ≠ acc
  reg_unit : ∀ i, reg i ≠ unit
  reg_acc : ∀ i, reg i ≠ acc

namespace Placement

/-- Host address at offset zero of the block for a given source instruction. -/
def entry (D : Placement C p r P R) (i : Fin p) := D.pc i 0

/-- A host register reserved for the enclosing program, distinct from both scratch registers
and all relocated source registers. -/
def privateReg (D : Placement C p r P R) (j : Fin R) : Prop :=
  j ≠ D.unit ∧ j ≠ D.acc ∧ j ∉ Set.range D.reg

end Placement

/-- The word prepared by this source row. -/
def operand (bank : Fin k → ℕ) : Instr v p r k → ℕ
  | .constant _ a _ => a.val
  | .publicWord _ i _ => bank i
  | _ => 0

theorem operand_le (T : Template p r k) (bank : Fin k → ℕ) (j : Fin p) :
    operand bank (T.code j) ≤ capacity T bank := by
  cases T.code j with
  | constant dst a next => exact a.isLt.le.trans (Nat.le_add_right _ _)
  | publicWord dst i next =>
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (bank j)) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ _)
  | _ => exact Nat.zero_le _

/-- Only the two instructions with immediate data are replaced by a copy from the
accumulator. All other operands and control transfers are directly relocated. -/
def body (D : Placement C p r P R) : Instr v p r k → Instr w P R K
  | .constant a _ j | .publicWord a _ j => .copy (D.reg a) D.acc (D.entry j)
  | .stateWord a j => .stateWord (D.reg a) (D.entry j)
  | .copy a b j => .copy (D.reg a) (D.reg b) (D.entry j)
  | .binary op a b c j => .binary op (D.reg a) (D.reg b) (D.reg c) (D.entry j)
  | .loadPrivate a b j => .loadPrivate (D.reg a) (D.reg b) (D.entry j)
  | .storePrivate a b j => .storePrivate (D.reg a) (D.reg b) (D.entry j)
  | .jumpEq a b y n => .jumpEq (D.reg a) (D.reg b) (D.entry y) (D.entry n)
  | .jumpLt a b y n => .jumpLt (D.reg a) (D.reg b) (D.entry y) (D.entry n)
  | .choose y n => .choose (D.entry y) (D.entry n)
  | .readExternal a b j => .readExternal (D.reg a) (D.reg b) (D.entry j)
  | .writeExternal a b j => .writeExternal (D.reg a) (D.reg b) (D.entry j)
  | .returnState a => .returnState (D.reg a)
  | .accept => .accept
  | .reject => .reject

@[simp] theorem body_resize (D : Placement C p r P R) (i : Instr v p r k) :
    (body (w := 2) (K := K) D i).resize w = body D i := by cases i <;> rfl

/-- Code for one uniform block in a host with any public-word ABI. -/
def row (T : Template p r k) (bank : Fin k → ℕ) (D : Placement C p r P R)
    (j : Fin p) : Fin (C + 3) → Instr 2 P R K :=
  Fin.lastCases (body D (T.code j))
    (literalInstruction 2 C (operand bank (T.code j)) (D.pc j) D.unit D.acc)

/-- Consecutive code blocks and a trailing scratch register pair. -/
def canonical (C p r : ℕ) : Placement C p r (p * (C + 3)) (r + 2) where
  pc i t := finProdFinEquiv (i, t)
  reg := Fin.castAddEmb 2
  unit := ⟨r, by omega⟩
  acc := ⟨r + 1, by omega⟩
  distinct h := by have := congrArg Fin.val h; dsimp at this; omega
  reg_unit i h := by have := congrArg Fin.val h; exact i.isLt.ne this
  reg_acc i h := by have hh := congrArg Fin.val h; change i.val = r + 1 at hh; omega

/-- Closed width-two template. Neither its labels nor its code depends on the word width. -/
def compiled (K : ℕ) (T : Template p r k) (bank : Fin k → ℕ) :
    Template (p * (capacity T bank + 3)) (r + 2) K where
  literalWidth := 2
  entry := (canonical (capacity T bank) p r).entry T.entry
  code a := let jt := finProdFinEquiv.symm a
            row T bank (canonical (capacity T bank) p r) jt.1 jt.2

/-- The complete block is present at this source label. -/
def ContainsAt (M : Machine w P R K) (T : Template p r k) (bank : Fin k → ℕ)
    (D : Placement C p r P R) (j : Fin p) :=
  ∀ t, M.code (D.pc j t) = (row (K := K) T bank D j t).resize w

theorem compiled_contains (T : Template p r k) (bank : Fin k → ℕ) (pub : Fin K → Word w)
    (j : Fin p) : ContainsAt ((compiled K T bank).instantiate w pub) T bank
      (canonical (capacity T bank) p r) j := by
  intro t
  change (row T bank _ (finProdFinEquiv.symm (finProdFinEquiv (j, t))).1
    (finProdFinEquiv.symm (finProdFinEquiv (j, t))).2).resize w = _
  simp

/-- Observable configuration data. The enclosing code can reserve unrelated registers. -/
structure Agrees (D : Placement C p r P R) (frame : Fin R → Word w)
    (s : Config w p r) (h : Config w P R) : Prop where
  reg : ∀ i, h.reg (D.reg i) = s.reg i
  privateMem : h.privateMem = s.privateMem
  persistent : h.persistent = s.persistent
  frame : ∀ i, D.privateReg i → h.reg i = frame i

/-- The host is at the entry of the current source instruction's block, agrees on source
registers, private memory and persistent state, and matches the given frame on enclosing
registers. -/
def Related (D : Placement C p r P R) (frame : Fin R → Word w)
    (s : Config w p r) (h : Config w P R) : Prop := Agrees D frame s h ∧ h.pc = D.entry s.pc

private theorem agree_put {D : Placement C p r P R} {frame : Fin R → Word w}
    {s : Config w p r} {h : Config w P R} (a : Agrees D frame s h)
    (next : Fin p) (i : Fin r) (x : Word w) :
    Related D frame (s.put next i x) (h.put (D.entry next) (D.reg i) x) := by
  refine ⟨⟨?_, a.privateMem, a.persistent, ?_⟩, rfl⟩
  · intro l
    by_cases he : l = i <;> simp [Config.put, he, a.reg]
  · intro l hl
    have he : l ≠ D.reg i := fun e => hl.2.2 ⟨i, e.symm⟩
    simp [Config.put, Function.update_of_ne he, a.frame l hl]

private theorem agree_pc {D : Placement C p r P R} {frame : Fin R → Word w}
    {s : Config w p r} {h : Config w P R} (a : Agrees D frame s h) (next : Fin p) :
    Related D frame {s with pc := next} {h with pc := D.entry next} :=
  ⟨⟨a.reg, a.privateMem, a.persistent, a.frame⟩, rfl⟩

/-- A matching native action has the same observable event and relates all continuations. -/
inductive ActionsMatch {S H : Type*} (rel : S → H → Prop) :
    CallAction w S → CallAction w H → Prop
  | localStep {s h} (next : rel s h) : ActionsMatch rel (.localStep s) (.localStep h)
  | branch {s h} (next : ∀ b, rel (s b) (h b)) : ActionsMatch rel (.branch s) (.branch h)
  | read {addr s h} (next : ∀ v, rel (s v) (h v)) : ActionsMatch rel (.read addr s) (.read addr h)
  | write {addr val s h} (next : rel s h) : ActionsMatch rel (.write addr val s) (.write addr val h)
  | finish (res) : ActionsMatch rel (.finish res) (.finish res)
  | reject : ActionsMatch rel .reject .reject

private theorem body_action {D : Placement C p r P R} {frame : Fin R → Word w}
    {s : Config w p r} {h : Config w P R} (a : Agrees D frame s h) (bank : Fin k → ℕ)
    (pub : Fin K → Word w) (i : Instr v p r k) (ha : h.reg D.acc = (operand bank i : Word w)) :
    ActionsMatch (Related D frame) ((i.resize w).run (fun j => (bank j : Word w)) s)
      ((body D i).run pub h) := by
  cases i with
  | constant dst val next | publicWord dst val next =>
    apply ActionsMatch.localStep
    rw [ha]
    exact agree_put a _ _ _
  | stateWord dst next =>
    simp only [Instr.resize, Instr.run, body, a.persistent]
    exact .localStep (agree_put a _ _ _)
  | copy dst src next | binary _ dst src _ next | loadPrivate dst src next =>
    simp only [Instr.resize, Instr.run, body, a.reg, a.privateMem]
    exact .localStep (agree_put a _ _ _)
  | storePrivate addr src next =>
    simp only [Instr.resize, Instr.run, body, a.reg]
    exact .localStep ⟨⟨a.reg, congrArg (fun m => Function.update m _ _) a.privateMem,
      a.persistent, a.frame⟩, rfl⟩
  | jumpEq lhs rhs yes no | jumpLt lhs rhs yes no =>
    simp only [Instr.resize, Instr.run, body, a.reg]
    split <;> exact .localStep (agree_pc a _)
  | choose yes no =>
    exact .branch (fun b => by cases b <;> exact agree_pc a _)
  | readExternal dst addr next =>
    simp only [Instr.resize, Instr.run, body, a.reg]
    exact .read (fun _ => agree_put a _ _ _)
  | writeExternal addr src next =>
    simp only [Instr.resize, Instr.run, body, a.reg]
    exact .write (agree_pc a _)
  | returnState src =>
    simp only [Instr.resize, Instr.run, body, a.reg]
    exact .finish _
  | accept => exact .finish _
  | reject => exact .reject

/-- Exact one-row simulation, from an arbitrary source and host configuration. -/
theorem simulate_row {T : Template p r k} {bank : Fin k → ℕ} {D : Placement C p r P R}
    {M : Machine w P R K} {frame : Fin R → Word w} {s : Config w p r} {h : Config w P R}
    (bound : operand bank (T.code s.pc) ≤ C) (hc : ContainsAt M T bank D s.pc)
    (rel : Related D frame s h) :
    ∃ mid, Prefix M h (List.replicate (C + 2) .tick) mid ∧
      ActionsMatch (Related D frame)
        ((T.instantiate w (fun j => (bank j : Word w))).program.step s) (M.program.step mid) := by
  have installed (i : Fin (C + 2)) : M.code (D.pc s.pc i.castSucc) =
      literalInstruction w C (operand bank (T.code s.pc)) (D.pc s.pc) D.unit D.acc i := by
    rw [hc, row, Fin.lastCases_castSucc, literal_resize]
  obtain ⟨mid, pref, hp, ha, hr, hm, hs⟩ := literal_prefix D.distinct bound installed h rel.2
  refine ⟨mid, pref, ?_⟩
  change ActionsMatch _ (((T.code s.pc).resize w).run _ s) ((M.code mid.pc).run _ mid)
  rw [hp, hc, row, Fin.lastCases_last, body_resize]
  apply body_action _ _ _ _ ha
  exact ⟨fun i => (hr (D.reg i) (D.reg_unit i) (D.reg_acc i)).trans (rel.1.reg i),
    hm.trans rel.1.privateMem, hs.trans rel.1.persistent,
    fun i hi => (hr i hi.1 hi.2.1).trans (rel.1.frame i hi)⟩

/-- Nonterminal traces insert the constant block's local ticks before each source event. -/
def padded (pad : ℕ) : List (Event w) → List (Event w)
  | [] => []
  | e :: es => List.replicate pad .tick ++ e :: padded pad es

end PairSimulation.InlinePublic

end VPVNP
end Computability
end OAI
