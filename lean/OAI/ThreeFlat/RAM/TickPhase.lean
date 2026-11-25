import OAI.ThreeFlat.Diagonal.TickChronology
import OAI.ThreeFlat.RAM.LiteralTable

namespace OAI
/-! # A fixed-size native program computing the tick phase

The decoded transition number occupies one register. The clock's public
bounds appear as instruction literals and are independent of all tick pins.
-/

namespace ThreeFlat.RAM.TickPhase
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TickChronology
open scoped Fin.CommRing

variable {w k : ℕ}
private abbrev E (w k : ℕ) := Term w k 1
private def lit (a : ℕ) : E w k := .literal (a : Word w)
private def tv : E w k := .result 0
private def eq (a : E w k) (b : ℕ) (x y : E w k) := Term.select .eq a (lit b) x y
private def lt (a : E w k) (b : ℕ) (x y : E w k) := Term.select .lt a (lit b) x y
private def offset (c : Clock) : E w k :=
  .binary .mod (.binary .sub tv (lit c.beginTick)) (lit c.groupDuration)

/-- Decode the local offset after the reservation bounds have been checked. -/
def inside (c : Clock) : E w k :=
  eq tv 0 (lit 3) <| lt tv (c.chunks+1) (lit 4) <| lt tv (c.chunks+c.evaluateTicks+1) (lit 5) <|
    eq tv (c.groupDuration-1) (lit 6) (lit 0)

/-- Decode the absolute step and then its offset within the selected group. -/
def program (c : Clock) : E w k :=
  eq tv 0 (lit 1) <| eq tv c.last (lit 2) <| lt tv c.beginTick (lit 0) <|
    lt tv c.stop ((inside c).instantiate (fun _ => offset c)) (lit 0)

/-- At most a constant number of arithmetic, comparison and literal instructions. -/
theorem program_binds (c : Clock) : (program (w:=w) (k:=k) c).binds ≤ 64 := by
  simp [program, inside, eq, lt, offset, tv, lit, Term.binds_instantiate,
    Term.select, Term.binary, Term.literal, Term.binds]

private theorem cmp_eq {a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    Comparison.eq.test (a : Word w) (b : Word w) = decide (a=b) := by
  by_cases h : a = b
  · subst b; simp [Comparison.test]
  · have hn : (a : Word w) ≠ (b : Word w) := by
      intro e
      exact h (by simpa only [Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb] using congrArg Fin.val e)
    simp [Comparison.test,h,hn]

private theorem cmp_lt {a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    Comparison.lt.test (a : Word w) (b : Word w) = decide (a<b) := by
  simp [Comparison.test, Fin.lt_def, Fin.val_cast_of_lt ha, Fin.val_cast_of_lt hb]

theorem inside_eval (c : Clock) (hd : c.groupDuration < 2^w) {o : ℕ} (ho : o < c.groupDuration)
    (params : Fin k → Word w) (mem : Memory w) (v : Fin 1 → Word w) (arg : v 0 = (o : Word w)) :
    (inside c).eval params mem v = ((c.within o).tag : Word w) := by
  have r := c.room
  have small : o < 2^w := ho.trans hd
  have hz : 0 < 2^w := by positivity
  simp only [inside, eq, lt, tv, lit, Term.eval_select, Term.eval_literal, Term.eval, arg,
    cmp_eq small hz, cmp_lt small (show c.chunks+1 < 2^w by omega),
    cmp_lt small (show c.chunks+c.evaluateTicks+1 < 2^w by omega),
    cmp_eq small (show c.groupDuration-1 < 2^w by omega), decide_eq_true_eq, Clock.within]
  split_ifs <;> rfl

private theorem offset_eval (c : Clock) (hd : c.groupDuration < 2^w)
    {t : ℕ} (ht : t < 2^w) (hb : c.beginTick ≤ t)
    (params : Fin k → Word w) (mem : Memory w) (v : Fin 1 → Word w) (arg : v 0 = (t : Word w)) :
    (offset c).eval params mem v = (c.offset t : Word w) := by
  have hsub : t - c.beginTick < 2^w := by omega
  simp only [offset, tv, lit, Term.eval_binary, Term.eval_literal, Term.eval, arg,
    BinaryOp.eval, ← Nat.cast_sub hb, Fin.val_cast_of_lt hsub, Fin.val_cast_of_lt hd,
    Clock.offset]
  rfl

theorem program_eval (c : Clock) (hd : c.groupDuration < 2^w) (hlast : c.last < 2^w)
    {t : ℕ} (ht : t < 2^w) (params : Fin k → Word w) (mem : Memory w) (v : Fin 1 → Word w)
    (arg : v 0 = (t : Word w)) :
    (program c).eval params mem v = ((c.phase t).tag : Word w) := by
  have hs : c.stop < 2^w := lt_of_le_of_lt c.fits hlast
  have hb : c.beginTick < 2^w := by have := c.fits; omega
  have hz : 0 < 2^w := by positivity
  simp only [program, eq, lt, tv, lit, Term.eval_select, Term.eval_literal, Term.eval, arg,
    cmp_eq ht hz, cmp_eq ht hlast, cmp_lt ht hb, cmp_lt ht hs, decide_eq_true_eq, Clock.phase]
  split_ifs with h0 hlast' hlo hstop
  · rfl
  · rfl
  · rfl
  · rw [Term.eval_instantiate]
    exact inside_eval c hd (Nat.mod_lt _ c.duration_pos) _ _ _
      (offset_eval c hd ht (Nat.le_of_not_gt hlo) _ _ _ arg)
  · rfl

/-- The embedded instruction block terminates with the same external memory,
and returns the dispatch tag in its output register. -/
theorem advance_phase {p r : ℕ} (M : Machine w p r k) (clock : Clock)
    (hd : clock.groupDuration < 2^w) (hlast : clock.last < 2^w) {t : ℕ} (ht : t < 2^w)
    (loc : Fin (program (w:=w) (k:=k) clock).labels → Fin p) (reg : Fin 1 → Fin r)
    (tmp : Fin (program (w:=w) (k:=k) clock).binds ↪ Fin r) (dst : Fin r) (exit : Fin p)
    (fresh : ∀ i j, reg i ≠ tmp j)
    (rom : ∀ i, M.code (loc i) = (program clock).emit loc reg tmp dst exit i)
    (cfg : Config w p r) (mem : Memory w) (start : cfg.pc = loc (program clock).first)
    (timeReg : cfg.reg (reg 0) = (t : Word w)) :
    ∃ out : Config w p r,
      advance M.program (program (w:=w) (k:=k) clock).steps cfg mem = some (out,mem) ∧
      out.pc = exit ∧ out.reg dst = ((clock.phase t).tag : Word w) := by
  let e : E w k := program clock
  refine ⟨e.run M.publicData mem reg tmp dst exit cfg, e.advance_emit M _ _ _ _ _ rom _ _ start,
    e.run_pc .., ?_⟩
  exact (e.run_result M.publicData mem reg tmp dst exit cfg fresh tmp.injective).trans
    (program_eval clock hd hlast ht M.publicData mem (cfg.reg ∘ reg) timeReg)

end ThreeFlat.RAM.TickPhase

end OAI
