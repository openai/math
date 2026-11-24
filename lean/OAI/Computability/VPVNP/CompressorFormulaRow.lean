import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
import OAI.Computability.VPVNP.CompressorRecordsCursorInit

/-!
# Native publication of a consecutive row of computed descriptor fields

The finite program evaluates the destination and all field expressions against
entry memory before performing any store. The program works at every word width
and its instruction and probe counts depend only on the expressions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PhaseRecipe

open BurstRAM BurstRAM.PrivateRAM RowRecipe
open private Phase.emit Phase.out Phase.formulas emit_list run from
  OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
open private stores_at from OAI.Computability.VPVNP.CompressorRecordsCursorInit

/-- A computed starting address and the consecutive words installed there. -/
structure FormulaRow (g : ℕ) where
  /-- Expression computing the destination address of the first word of the published row. -/
  dest : Expr
  /-- Expressions for the consecutive row words, evaluated against the entry memory before
  publication. -/
  fields : Fin (g+3) → Expr

namespace FormulaRow

variable {g w : ℕ} (R : FormulaRow g)

/-- Use the phase compiler's scratch allocation for exactly the requested
expressions. The extra phase prefix is omitted from the emitted assignments. -/
private def carrier : Phase (g+4) := ⟨0, .lit 0, .lit 0, Fin.cons R.dest R.fields⟩

private def paramIndex (j : Fin (g+4)) : Fin ((g+4)+4) := j.succ.succ.succ.succ

/-- Compile the row's destination and fields into a recipe that publishes the tag, interval,
and parameters. -/
def recipe : Recipe R.carrier.registerCount 5 g where
  lines := ((List.finRange (g+4)).map paramIndex).flatMap (Phase.emit R.carrier)
  dest := Phase.out R.carrier (paramIndex 0)
  tag := Phase.out R.carrier (paramIndex (0 : Fin (g+3)).succ)
  start := Phase.out R.carrier (paramIndex (0 : Fin (g+2)).succ.succ)
  stop := Phase.out R.carrier (paramIndex (0 : Fin (g+1)).succ.succ.succ)
  params i := Phase.out R.carrier (paramIndex i.succ.succ.succ.succ)

private theorem eval_param (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) (j : Fin (g+4)) :
    R.recipe.values pub s m (Phase.out R.carrier (paramIndex j)) =
      Expr.eval pub s m (Fin.cons (α := fun _ ↦ Expr) R.dest R.fields j) := by
  change run pub s m (((List.finRange (g+4)).map paramIndex).flatMap (Phase.emit R.carrier)) _ _ = _
  rw [emit_list]
  have h : paramIndex j ∈ (List.finRange (g+4)).map paramIndex :=
    List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
  rw [ite_eq_left h]
  simp only [paramIndex, Phase.formulas, Fin.cons_succ, carrier]

theorem recipe_address (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    R.recipe.address pub s m = R.dest.eval pub s m := by
  exact R.eval_param pub s m 0

theorem recipe_words (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    R.recipe.words pub s m = List.ofFn (fun j ↦ (R.fields j).eval pub s m) := by
  rw [Recipe.words, Recipe.fields]
  simp only [List.map_cons, List.map_ofFn]
  conv_rhs => rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
  change R.recipe.values pub s m (Phase.out R.carrier (paramIndex (0 : Fin (g+3)).succ)) ::
    R.recipe.values pub s m (Phase.out R.carrier (paramIndex (0 : Fin (g+2)).succ.succ)) ::
    R.recipe.values pub s m (Phase.out R.carrier (paramIndex (0 : Fin (g+1)).succ.succ.succ)) ::
    List.ofFn (fun j : Fin g ↦ R.recipe.values pub s m
      (Phase.out R.carrier (paramIndex j.succ.succ.succ.succ))) = _
  simp only [eval_param, Fin.cons_succ]

/-- Normal entry executes one burst, returns the next state, installs each
field at its natural address and preserves all words outside the row. -/
theorem execute (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (fit : (R.dest.eval pub s m).val + (g+3) ≤ 2^w) :
    let M := R.recipe.table.instantiate w pub
    let rep := R.recipe.report pub s m
    let dest := (R.dest.eval pub s m).val
    BurstRAM.execute M.program (R.recipe.code.length+1) (M.program.start s) m [] = some rep ∧
      rep.result = some (s+1) ∧
      (∀ j : Fin (g+3), after m rep.events (dest+j.val) = (R.fields j).eval pub s m) ∧
      (∀ a, a < dest ∨ dest + (g+3) ≤ a → after m rep.events a = m a) ∧
      rep.events.length = R.recipe.code.length ∧ rep.probes = R.recipe.reads+(g+3) ∧
      choiceBits rep.events = [] := by
  intro M rep dest
  have hf : (R.recipe.address pub s m).val + (g+3) ≤ 2^w := R.recipe_address pub s m ▸ fit
  have hs := row_stores R.recipe pub s m hf
  rw [recipe_address, recipe_words] at hs
  obtain ⟨he,hp,hc⟩ := report_cost R.recipe pub s m
  refine ⟨execute_row R.recipe pub s m [] _ (by omega), rfl, ?_, ?_, he.trans (code_length _).symm, hp, hc⟩
  · intro j
    have hj : j.val < (List.ofFn (fun i ↦ (R.fields i).eval pub s m)).length := by simpa only [List.length_ofFn] using j.isLt
    exact (stores_at _ _ hs (by simpa using fit) hj).trans (List.getElem_ofFn hj)
  · intro a ha
    exact row_outside R.recipe pub s m hf a (R.recipe_address pub s m ▸ ha)

end FormulaRow

end CompressorRecords.PhaseRecipe

end VPVNP
end Computability
end OAI
