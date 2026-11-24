import OAI.Computability.VPVNP.CompressorBlockHeaderPlan
import OAI.Computability.VPVNP.CompressorRefreshLevelRecipe

/-!
# The degree-refresh phase list of a fixed compressor block

All phases share the same runtime input and allocation formulas. The
finite graph fixes each ROM pair and each local expander slot in the
program text. Six final scans copy the verified output columns to the
published incidence heads for the next level.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshBlockPlan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe BlockPlanner DescriptorSpace LevelFields
open PortRefresh LevelRecipe

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Computes the refresh dimensions from the block schedule and template, including the tie
count, term-record stride and selector width. -/
def shape : LevelRecipe.Shape :=
  ⟨S.portExponent,S.degreeExponent 0,2^S.expanderExponent,Fintype.card (Tie (2^S.portExponent)),
    2+(2^S.portExponent)*(2^S.expanderExponent),B.refresh.selectorBits⟩

/-- Numbers the ties between refresh ports in the order used by the block's motif worker. -/
def order : Fin (shape B).ties ≃ Tie (shape B).ports := (Fintype.equivFin _).symm

/-- Reads the arena start, vertex and residual-lane counts, and old incidence heads from the
specified descriptor level. -/
def input (F : DescriptorSpace.Shape) (step : ℕ) (arena : Fin F.tables) : LevelRecipe.Input :=
  ⟨table F step arena,vertices step,residualLanes step,incidence F step 0,incidence F step
    2,incidence F step 5⟩

/-- The motif worker pass for this template, using the block's tie ordering and one payload
entry per directed expander incidence. -/
abbrev term := TermWorker.motifPass B.refresh (order B) ((shape B).ports*(shape B).dH)

/-- Compiles a refresh stage to its worker visit with the corresponding cursor interval and
operand expressions. -/
def stage (I : LevelRecipe.Input) (j : LevelRecipe.Stage (shape B)) : Visit :=
  ⟨j.worker S.degree_bounds.2 (term B), j.initial, j.stop I,
    j.workerBank I S.degree_bounds.2 S.graph (order B) (term B)
      (TermWorker.motifExprs B.refresh (order B) finProdFinEquiv.symm)⟩

/-- Computes the copy length for a refreshed incidence column, counting base slots for columns
zero through two and actual slots for columns three through five. -/
def columnCount (I : LevelRecipe.Input) (c : Fin 6) : Expr :=
  if c.val < 3 then (I.vertices.mul (.lit (shape B).ports)).mul (.lit (shape B).degree)
  else capacity (shape B) I

/-- Copies one incidence column from the refresh allocation to its assigned column at the next
descriptor level. -/
def copyColumn (F : DescriptorSpace.Shape) (step : ℕ) (I : LevelRecipe.Input) (c : Fin 6) : Visit :=
  BlockPlanner.copy (columnCount B I c) (column (shape B) I c) (incidence F (step+1) c)

/-- The native refresh worker visits in execution order followed by the six incidence-column
copies. -/
def visits (F : DescriptorSpace.Shape) (step : ℕ) (arena : Fin F.tables) : List Visit :=
  let I := input F step arena
  (LevelRecipe.order (shape B)).map (stage B I) ++ List.ofFn (copyColumn B F step I)

theorem visits_length (F : DescriptorSpace.Shape) (step : ℕ) (arena : Fin F.tables) :
    (visits B F step arena).length = 12+(shape B).ties+(shape B).ports*(shape B).dH+(shape
      B).degree := by
  simp [visits,LevelRecipe.order]; omega

theorem stage_worker (I : LevelRecipe.Input) (j : LevelRecipe.Stage (shape B)) :
    (stage B I j).worker = j.worker S.degree_bounds.2 (term B) := rfl

/-- The native worker bank is exactly the bank for which the refresh recipe
proves pointwise agreement with the semantic stage's operands. -/
theorem stage_params (I : LevelRecipe.Input) (j : LevelRecipe.Stage (shape B)) :
    (stage B I j).params =
      j.workerBank I S.degree_bounds.2 S.graph (order B) (term B)
        (TermWorker.motifExprs B.refresh (order B) finProdFinEquiv.symm) := rfl

end CompressorRecords.RefreshBlockPlan

end

end VPVNP
end Computability
end OAI
