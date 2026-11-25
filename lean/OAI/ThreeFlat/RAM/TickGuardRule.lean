import OAI.ThreeFlat.Diagonal.TickAuxiliary
import OAI.ThreeFlat.RAM.LiteralTable
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Native calculation of the auxiliary constraint at a bit address -/

namespace ThreeFlat.RAM.TickGuardRule
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TickChronology Diagonal.TickAuxiliary
open scoped Fin.CommRing

private def phase (i : ℕ) : Phase :=
  match i with
  | 1 => .opening | 2 => .closing | 3 => .propose | 4 => .scan
  | 5 => .evaluate | 6 => .clear | _ => .idle

private theorem phase_tag (p : Phase) : phase p.tag = p := by cases p <;> rfl
private theorem tag_lt (p : Phase) : p.tag < 7 := by cases p <;> decide

variable {w k n : ℕ}
private def byPhase (f : Phase → Rule) (q : Term w k n) : Term w k n :=
  LiteralTable.atIndex (fun i => ((f (phase i)).tag : Word w)) 7 q

private theorem byPhase_eval (f : Phase → Rule) (q : Term w k n) (p : Phase)
    (fit : 7 ≤ 2^w) (data : Fin k → Word w) (m : Memory w) (v : Fin n → Word w)
    (hp : q.eval data m v = (p.tag : Word w)) :
    (byPhase f q).eval data m v = ((f p).tag : Word w) := by
  simpa only [byPhase, phase_tag] using LiteralTable.atIndex_eval
    (fun i => ((f (phase i)).tag : Word w)) 7 p.tag (tag_lt p) fit data m v q hp

/-- Input registers contain phase, branch flag, bit index, persistent end, and pair end. -/
def program (w k : ℕ) : Term w k 5 :=
  let q := Term.result 0
  let i := Term.result 2
  .select .eq (.result 1) (.literal 0) (.literal 4) <|
    .select .eq i (.literal 0) (byPhase markerRule q) <|
      .select .lt i (.result 3) (byPhase historyRule q) <|
        .select .lt i (.result 4) (byPhase pairRule q) (.literal 4)

theorem program_binds (w k : ℕ) : (program w k).binds ≤ 80 := by
  simp [program, byPhase, Term.select, Term.literal, Term.binds]

private theorem cmp (a b : ℕ) (ha : a < 2^w) (hb : b < 2^w) :
    Comparison.lt.test (a : Word w) (b : Word w) = decide (a < b) := by
  simp [Comparison.test, Fin.lt_def, Fin.val_cast_of_lt ha, Fin.val_cast_of_lt hb]

private theorem eq_zero (a : ℕ) (ha : a < 2^w) :
    Comparison.eq.test (a : Word w) 0 = decide (a = 0) := by
  by_cases h : a = 0
  · subst a; simp [Comparison.test]
  · have hn : (a : Word w) ≠ 0 := by
      intro e
      exact h (by simpa only [Fin.val_cast_of_lt ha,Fin.val_zero] using congrArg Fin.val e)
    simp [Comparison.test,h,hn]

def input (p : Phase) (run : Bool) (i h e : ℕ) : Fin 5 → Word w :=
  ![(p.tag : Word w), (run.toNat : Word w), (i : Word w), (h : Word w), (e : Word w)]

theorem program_eval {a : ℕ} (L : Layout a) (p : Phase) (run : Bool) (i : Fin a)
    (ha : a < 2^w) (fit : 7 ≤ 2^w) (data : Fin k → Word w) (mem : Memory w) :
    (program w k).eval data mem (input p run i.val L.wiresEnd L.pairsEnd) =
      ((L.rule p run i.val).tag : Word w) := by
  have hx := L.ordered.trans L.fits
  have hi : i.val < 2^w := i.isLt.trans ha
  let v : Fin 5 → Word w := input p run i.val L.wiresEnd L.pairsEnd
  have tag (f : Phase → Rule) := byPhase_eval f (Term.result (0 : Fin 5)) p fit data mem v rfl
  change (program w k).eval data mem v = _
  simp only [program, Term.eval_select, Term.eval, tag, Term.eval_literal]
  change (if Comparison.eq.test (run.toNat : Word w) 0 then _ else
    if Comparison.eq.test (i.val : Word w) 0 then _ else
    if Comparison.lt.test (i.val : Word w) (L.wiresEnd : Word w) then _ else
    if Comparison.lt.test (i.val : Word w) (L.pairsEnd : Word w) then _ else _) = _
  have hr : run.toNat < 2^w := by
    cases run
    · exact (show (0 : ℕ) < 2^w by omega)
    · exact (show (1 : ℕ) < 2^w by omega)
  simp only [eq_zero _ hr, eq_zero _ hi, cmp _ _ hi (lt_of_le_of_lt hx ha),
    cmp _ _ hi (lt_of_le_of_lt L.fits ha), decide_eq_true_eq, Layout.rule]
  cases run <;> simp <;> first | rfl | (split_ifs <;> rfl)

end ThreeFlat.RAM.TickGuardRule

end OAI
