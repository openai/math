import OAI.Computability.VPVNP.EvaluatorStreamCount
import OAI.Computability.VPVNP.EvaluatorRadixRows
import OAI.Computability.VPVNP.EvaluatorRepeatedEffect

/-!
# Counting the matrix steps of the nested digit loops

The machine loops over increasing column and label indices. Its table
starts with the most significant base digit, so column `j` selects power
`Z - 1 - j`. In each column the machine first chooses an index for a
Frobenius step, then chooses one index per repetition of each label. The
finite sums of these branches are exactly the chronological continuation
effects of the digit program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorScheduleEffects

open EvaluatorDigitSchedule
variable {S I : Type*} [Fintype I] {t Z : ℕ}

/-- Value at the machine's row and column indices. The stack supplies a
natural row number, so this definition also covers an out-of-range row. -/
def digitAt (Q : ℕ) (e : Fin t → BurstRAM.Word Z) (i j : ℕ) : ℕ :=
  if h : i < t then (e ⟨i,h⟩).val / Q^(Z-1-j) % Q else 0

@[simp] theorem digitAt_fin (Q : ℕ) (e : Fin t → BurstRAM.Word Z) (i : Fin t) (j : ℕ) :
    digitAt Q e i.val j = (e i).val / Q^(Z-1-j) % Q := by simp [digitAt, i.isLt]

/-- The unary offset selected by the machine yields the exact multiplicity
for its binary repetition routine. -/
theorem digitAt_table (w Q : ℕ) (e : Fin t → BurstRAM.Word Z) (i : Fin t) (j : Fin Z)
    (suffix : List Bool) :
    (((EvaluatorRadixRows.packedTable w Q (List.ofFn e) ++ suffix).drop ((i.val*Z+j.val)*w)).take w) =
      PrimedCounter.digits w (digitAt Q e i.val j.val) := by
  have hi : i.val < (List.ofFn e).length := by rw [List.length_ofFn]; exact i.isLt
  rw [EvaluatorRadixRows.packedTable_cell (z := Z) w Q (List.ofFn e) suffix i.val j.val hi j.isLt,
    List.getElem_ofFn, digitAt_fin]

/-- Summation over every index trace emitted by one binary repetition count. -/
def cellEffect (next : Option ℕ → S → I → S) (e : Fin t → BurstRAM.Word Z)
    (Q j i : ℕ) : (S → ℕ) → S → ℕ :=
  repeatEffect next (some i) (digitAt Q e i j)

/-- One column begins with Frobenius, followed by the repeated label steps
in order of increasing label number. -/
def columnEffect (next : Option ℕ → S → I → S) (e : Fin t → BurstRAM.Word Z)
    (Q j : ℕ) (f : S → ℕ) : S → ℕ :=
  stepEffect next none ((List.range t).foldr (cellEffect next e Q j) f)

/-- Continuation effect of the entire nested machine schedule. -/
def schedulerEffect (next : Option ℕ → S → I → S) (e : Fin t → BurstRAM.Word Z)
    (Q : ℕ) (f : S → ℕ) : S → ℕ :=
  (List.range Z).foldr (columnEffect next e Q) f

/-- Physical action number used by the matrix query callback. -/
def actionCode : Action t → Option ℕ
  | .frobenius => none
  | .label i => some i.val

theorem columns_eq_digits (Q : ℕ) (e : Fin t → BurstRAM.Word Z) :
    columns Q Z (fun i => (e i).val) =
      (List.range Z).map (fun j i => digitAt Q e i.val j) := by
  rw [columns_eq]
  apply List.ext_getElem (by simp)
  intro j _ _
  funext i
  simp [List.getElem_reverse]

private theorem label_range (t : ℕ) : (List.finRange t).map Fin.val = List.range t := by
  apply List.ext_getElem (by simp)
  intros; simp

/-- The fixed loop for a column has the same multiplicities and ordering as
the Frobenius and label actions of `emit`. -/
theorem columnEffect_eq_emit (next : Option ℕ → S → I → S) (e : Fin t → BurstRAM.Word Z)
    (Q j : ℕ) (f : S → ℕ) :
    columnEffect next e Q j f =
      ((emit (fun i : Fin t => digitAt Q e i.val j)).map actionCode).foldr (stepEffect next) f := by
  rw [columnEffect, ← label_range t, List.foldr_map]
  simp only [emit, List.map_cons, actionCode, List.map_flatMap, List.map_replicate,
    List.foldr_cons, List.foldr_flatMap]
  apply congrArg (stepEffect next none)
  apply congrArg (fun g => (List.finRange t).foldr g f)
  funext i g s
  exact repeatEffect_eq_foldr next (some i.val) (digitAt Q e i.val j) g s

/-- All branch choices of the nested range loops have exactly the same
effect as the chronological action list, for any index update and continuation. -/
theorem schedulerEffect_eq_actions (next : Option ℕ → S → I → S) (e : Fin t → BurstRAM.Word Z)
    (Q : ℕ) (f : S → ℕ) :
    schedulerEffect next e Q f =
      (((columns Q Z (fun i => (e i).val)).flatMap emit).map actionCode).foldr (stepEffect next) f := by
  rw [schedulerEffect, columns_eq_digits, List.flatMap_map, List.map_flatMap, List.foldr_flatMap]
  apply congrArg (fun g => (List.range Z).foldr g f)
  funext j g
  exact columnEffect_eq_emit next e Q j g

/-- Interpret the physical scheduler's continuation in the counted action
program of `EvaluatorStreamCount`. The interpretation may include fuel and
stack encoding, so the action count may charge a different delay on each
chosen index. -/
theorem schedulerEffect_eq_actionCount {P : Type*} (next : Option ℕ → S → I → S)
    (step : Action t → Evaluator.Continuation P → Evaluator.Continuation P)
    (pull : Evaluator.Continuation P → S → ℕ)
    (h : ∀ a c, stepEffect next (actionCode a) (pull c) = pull (step a c))
    (e : Fin t → BurstRAM.Word Z) (Q : ℕ) (finish : Evaluator.Continuation P) :
    schedulerEffect next e Q (pull finish) =
      pull (Evaluator.actionCount step finish ((columns Q Z (fun i => (e i).val)).flatMap emit)) := by
  rw [schedulerEffect_eq_actions]
  generalize (columns Q Z (fun i => (e i).val)).flatMap emit = ops
  induction ops with
  | nil => rfl
  | cons a ops ih => simp only [List.map_cons, List.foldr_cons, Evaluator.actionCount, ih, h]

/-- An implementation of the linear-map effect on all valid action codes
therefore realizes the concrete linear-map list of the algebra evaluator. -/
theorem schedulerEffect_eq_digitProgram (K : Type*) [Field K] [Fintype K]
    {A : Type*} [CommRing A] [Algebra K A] (X : Fin t → A)
    (next : Option ℕ → S → I → S) (effect : (A →ₗ[K] A) → (S → ℕ) → S → ℕ)
    (h : ∀ a : Action t, stepEffect next (actionCode a) = effect (actionMap K X a))
    (e : Fin t → BurstRAM.Word Z) (f : S → ℕ) :
    schedulerEffect next e (Fintype.card K) f =
      (Evaluator.digitProgram K X Z (fun i => (e i).val)).foldr effect f := by
  rw [schedulerEffect_eq_actions, ← actions_eq_digitProgram K X, List.foldr_map, List.foldr_map]
  simp only [h]

end EvaluatorScheduleEffects

end VPVNP
end Computability
end OAI
