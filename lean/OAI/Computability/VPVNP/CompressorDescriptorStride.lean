import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.CompressorFormulaRow
import OAI.Computability.VPVNP.CompressorRecordsCursorParameters

/-!
# Bootstrapping the runtime descriptor stride

The calendar multiplies the selected level number by a word stored immediately
before its directory. This deterministic burst reads the three coordinate
counts produced in the cursor parameter frame, computes the level stride,
and writes that single word. Only the pair workspace pointer is public.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DescriptorStride

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM RowRecipe
open scoped Fin.CommRing
open private low ptr one Assign.code lines_trace zeros eval_cost update_right from
  OAI.Computability.VPVNP.CompressorRecordsRowRecipe

variable {r k g w : ℕ}

/-- Evaluate the recipe's expressions, store the first field alone, and return
the next cursor. This form is used for the single stride word between the
active parameter frame and the directory. -/
def singleCode (R : Recipe r k g) : List (Op (r+2) k) :=
  R.lines.map Assign.code ++ [.write (low R.dest) (low R.tag),
    .stateWord (ptr r), .constant (one r) 1, .binary .add (ptr r) (ptr r) (one r)]

/-- Instruction template that evaluates a recipe, writes its selected field once, and returns
the advanced cursor. -/
def singleTable (R : Recipe r k g) := template (singleCode R) (ptr r)

/-- Report for a single-field recipe burst, including evaluation, the external write, and the
successor state. -/
def singleReport (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w) : Report w :=
  ⟨(evaluate pub s m R.lines (fun _ ↦ 0)).1 ++
    [.write (R.address pub s m) (R.values pub s m R.tag), .tick, .tick, .tick], some (s+1)⟩

private theorem single_trace (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w) :
    ∃ out, trace pub s (singleCode R) (fun _ ↦ 0) m = some ((singleReport R pub s m).events, out,
      writeMemory m (R.address pub s m) (R.values pub s m R.tag)) ∧ out (ptr r) = s + 1 := by
  rw [singleCode, zeros, trace_append, lines_trace]
  simp [trace, Op.effect, low, ptr, one, singleReport, Recipe.address, Recipe.values, BinaryOp.eval,
    Function.update, Fin.append_left]

theorem single_native (R : Recipe r k g) (pub : Fin k → Word w) (s : Word w) (m : Memory w) :
    let M := (singleTable R).instantiate w pub
    let rep := singleReport R pub s m
    execute M.program (1 + (singleCode R).length) (M.program.start s) m [] = some rep ∧
      after m rep.events = writeMemory m (R.address pub s m) (R.values pub s m R.tag) ∧
      rep.result = some (s+1) ∧ rep.events.length = (singleCode R).length ∧
      rep.probes = R.reads+1 ∧ choiceBits rep.events = [] := by
  obtain ⟨out,ht,hs⟩ := single_trace R pub s m
  intro M rep
  have hn : execute M.program (1 + (singleCode R).length) (M.program.start s) m [] = some rep := by
    change execute ((template (singleCode R) (ptr r)).instantiate w pub).program _
      ⟨((template (singleCode R) (ptr r)).instantiate w pub).entry, s, fun _ ↦ 0, fun _ ↦ 0⟩ m [] = _
    rw [execute_template, run_eq_trace, ht]
    simp [hs, rep, singleReport]
  obtain ⟨hl,hp⟩ := eval_cost pub s m R.lines (fun _ ↦ 0)
  refine ⟨hn, Greedy.trace_after ht, rfl, ?_, ?_, (execute_spec hn).2.2⟩
  · simp [rep, singleReport, singleCode, hl]
  · simp [rep, singleReport, Report.probes, Greedy.probes_append, countProbes, Recipe.reads, hp]

open PhaseRecipe DescriptorSpace

private def workspace : Expr := .publicWord 0
private def frame : Expr := workspace.add (.lit 9)
private def cursorCount (j : ℕ) : Expr := .load (frame.add (.lit j))

private def positionExpr := ((cursorCount 3).mul (cursorCount 4)).mul (cursorCount 5)

private def strideExpr (F : Shape) : Expr :=
  let slots := positionExpr.mul (.lit F.slots)
  let tables := (Expr.lit F.tables).mul (slots.mul (.lit F.fields))
  ((Expr.lit (F.scalarFields + 6 + F.tables)).add ((Expr.lit 6).mul slots)).add tables

/-- Only the first field is emitted by the single-cell store. -/
private def calculation (F : Shape) : FormulaRow 0 :=
  ⟨workspace.add (.lit (10 + F.arity)), ![strideExpr F, .lit 0, .lit 0]⟩

/-- Public operand two of the live pair is the workspace base. -/
def table (F : Shape) := LiveStageLink.widen (singleTable (calculation F).recipe)
  (Function.Embedding.refl _) (fun _ : Fin 5 ↦ (2 : Fin 11))

/-- Report of the level-stride calculation using the pair workspace pointer in public operand
two. -/
def report (F : Shape) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w) :=
  singleReport (calculation F).recipe (fun _ ↦ pub 2) s m

/-- Instruction count of the fixed program that computes and publishes the runtime level
stride. -/
def cost (F : Shape) := (singleCode (calculation F).recipe).length

/-- Run the actual Fin 11 bootstrap table. The input frame is the output
of `CursorRAM.ParametersInit.frame_ready`. No field of the directory itself
is required on entry. -/
theorem native (L : Layout) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    {row tag : Word w} {b l a W start : ℕ}
    (ready : Frame.data (pub 2 + 9) m = CursorRAM.ScheduleInit.inputs row tag b l a W start)
    (positions : (b+l) * 2^b * 2^l = L.positions) :
    let M := (table L.shape).instantiate w pub
    let rep := report L.shape pub s m
    execute M.program (1 + cost L.shape) (M.program.start s) m [] = some rep ∧
      rep.result = some (s+1) ∧
      after m rep.events = writeMemory m (pub 2 + ((10 + L.shape.arity : ℕ) : Word w))
        (levelWords L : Word w) ∧ rep.events.length = cost L.shape ∧ choiceBits rep.events = [] := by
  intro M rep
  let p : Fin 5 → Word w := fun _ ↦ pub 2
  let R := calculation L.shape
  have run := single_native R.recipe p s m
  have exec : execute M.program (1 + cost L.shape) (M.program.start s) m [] = some rep := by
    dsimp only [M, table]
    rw [LiveStageLink.execute_widen_start]
    exact run.1
  have hdest : R.recipe.address p s m = pub 2 + ((10 + L.shape.arity : ℕ) : Word w) := by
    rw [FormulaRow.recipe_address]; rfl
  have hw : R.recipe.values p s m R.recipe.tag = (strideExpr L.shape).eval p s m := by
    have h := congrArg List.head? (R.recipe_words p s m)
    simpa only [Recipe.words, Recipe.fields, List.map_cons, List.head?_cons, List.ofFn_succ,
      R, calculation, Matrix.cons_val_zero, Option.some.injEq] using h
  have h3 := congrFun ready (3 : Fin 8)
  have h4 := congrFun ready (4 : Fin 8)
  have h5 := congrFun ready (5 : Fin 8)
  change m (pub 2 + 9 + 3).val = ((b + l : ℕ) : Word w) at h3
  change m (pub 2 + 9 + 4).val = ((2 ^ b : ℕ) : Word w) at h4
  change m (pub 2 + 9 + 5).val = ((2 ^ l : ℕ) : Word w) at h5
  have hp : positionExpr.eval p s m = (L.positions : Word w) := by
    simp only [positionExpr, cursorCount, frame, workspace, Expr.eval, Expr.mul, Expr.add, BinaryOp.eval,
      p, Nat.cast_ofNat, h3, h4, h5, ← positions, Nat.cast_mul]
  have hs : (strideExpr L.shape).eval p s m = (levelWords L : Word w) := by
    simp only [strideExpr, Expr.eval, Expr.mul, Expr.add, BinaryOp.eval, hp, levelWords, levelHeaderWords,
      slotCapacity, tableWords, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  refine ⟨exec, run.2.2.1, ?_, run.2.2.2.1, run.2.2.2.2.2⟩
  rw [← hdest, ← hs, ← hw]
  exact run.2.1

end CompressorRecords.DescriptorStride

end VPVNP
end Computability
end OAI
