import OAI.Computability.VPVNP.CompressorBlockSlices
import OAI.Computability.VPVNP.CompressorHeaderOperands

/-!
# Memory reads of the fixed AB launch recipes

The row-indexed workers derive their public words from four level scalars,
the first scratch-table head and the AB-bank head. Each prologue parameter
is an affine base, a stride, or the zero bias.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkABSliceRecipe

open BurstRAM PhaseRecipe BlockPlanner
variable {w : ℕ} (D : ℕ → Prop) (pub : Fin 5 → Word w) (s : Word w) (mem : Memory w)
local notation "reads" => Expr.ReadsFrom D pub s mem

/-- Evaluating the AB recipe's row count, four input column heads, two strides and bank origin
reads only the allowed memory region. -/
structure Supported (I : Inputs) : Prop where
  rows : reads I.rows
  oldStarts : reads I.oldStarts
  oldWidths : reads I.oldWidths
  oldStride : reads I.oldStride
  newStarts : reads I.newStarts
  newWidths : reads I.newWidths
  newStride : reads I.newStride
  firstBank : reads I.firstBank

variable {I : Inputs} (h : Supported D pub s mem I)

private theorem arguments_supported {k : ℕ} {par : Fin k → Affine}
    (supported : ∀ j, reads (par j).1 ∧ reads (par j).2) (cursor : ℕ) (j : Fin (FlatRows.Params k)) :
    reads (arguments par cursor j) := by
  let a := finProdFinEquiv.symm j
  have all (i : Fin (k+1)) :
      let e := Fin.snoc (α := fun _ => Affine) par (constant cursor) i
      reads e.1 ∧ reads e.2 := by
    cases i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact ⟨trivial,trivial⟩
    | cast j => simpa only [Fin.snoc_castSucc] using supported j
  let e := Fin.snoc (α := fun _ => Affine) par (constant cursor) a.1
  change reads (![e.1,e.2,.lit 0] a.2)
  have p := all a.1
  generalize a.2 = c
  fin_cases c <;> first | exact p.1 | exact p.2 | trivial

include h in
theorem stage_supported {m n : ℕ} (j : Stage m n) :
    HeaderOperands.Supported D pub s mem (stage I j) := by
  have bank (off : ℕ) : reads (bankField I m n off).1 ∧ reads (bankField I m n off).2 :=
    ⟨⟨h.firstBank,trivial⟩,trivial⟩
  cases j with
  | clear k => exact ⟨trivial,h.rows,arguments_supported D pub s mem (fun _ => bank 0) k.val⟩
  | pair k =>
    refine ⟨trivial,h.rows,arguments_supported D pub s mem (par := pairParams I m n) ?_ k.val⟩
    intro u; fin_cases u
    exacts [⟨trivial,trivial⟩,⟨h.oldStarts,h.oldStride⟩,⟨h.oldWidths,h.oldStride⟩,
      ⟨h.newStarts,h.newStride⟩,⟨h.newWidths,h.newStride⟩,bank (m+n)]
  | refs k =>
    refine ⟨trivial,h.rows,arguments_supported D pub s mem (par := refParams I m n) ?_ k.val⟩
    intro u; fin_cases u
    exacts [⟨trivial,trivial⟩,⟨trivial,trivial⟩,bank (m+n),bank 0,bank (m+n+3*(m*n)),bank m,bank (m+n+4*(m*n))]

end CompressorRecords.ShrinkABSliceRecipe

namespace CompressorRecords.BlockSlices

open BurstRAM PhaseRecipe BlockPlanner Compression ShrinkBlockInputs ShrinkBundlePlan
open private firstRecord recordsEnd from OAI.Computability.VPVNP.CompressorGreedyLevelPlan

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (i : Fin S.steps) {w : ℕ}
variable (D : ℕ → Prop) (pub : Fin 5 → Word w) (s : Word w) (mem : Memory w)
local notation "reads" => Expr.ReadsFrom D pub s mem

/-- Exact block operands need four scalar and two table-pointer reads. -/
theorem ab_supported (origin abArena : Expr) (header : ∀ j : Fin 4, reads (LevelFields.scalar i.val j.val))
    (base : reads origin) (arena : reads abArena) :
    ShrinkABSliceRecipe.Supported D pub s mem (abInputs i origin abArena) := by
  have vert : reads (LevelFields.vertices i.val) := header 0
  have degree : reads (LevelFields.degree i.val) := header 1
  have lanes : reads (LevelFields.lanes i.val) := header 2
  have residual : reads (LevelFields.residualLanes i.val) := header 3
  have ending (width : ℕ) (x : Expr) (hx : reads x) : reads (recordsEnd i.val width x) := ⟨⟨hx,vert⟩,vert,trivial⟩
  have off : reads (GreedyLevelPlan.offsetBase i.val (a i) origin) := ending _ _ base
  have sh : reads (GreedyLevelPlan.shiftBase i.val (a i) origin) := ending _ _ off
  have pre : reads (preliminary i.val (a i) origin) := ⟨⟨sh,vert,degree⟩,trivial⟩
  have sites : reads (LevelFields.sites i.val) := ⟨vert,lanes⟩
  have slots : reads (LevelFields.slots i.val) := ⟨sites,degree⟩
  have own : reads (owner i.val (a i) origin) := ⟨pre,trivial,sites⟩
  have c : reads (counts i.val (a i) origin) := ⟨own,trivial,slots⟩
  have b : reads (bundles i.val (a i)) := ⟨⟨vert,trivial,residual⟩,degree⟩
  have bc : reads (bucketCount i.val (a i)) := ⟨trivial,b⟩
  have id : reads (ids i.val (a i) origin) := ⟨c,bc⟩
  have rect : reads (rectangle i.val (a i)) := ⟨bc,trivial⟩
  have rank : reads (ranks i.val (a i) origin) := ⟨⟨id,rect⟩,rect⟩
  have so : reads (sorted i.val (a i) origin) := ⟨rank,slots⟩
  have block : reads (blockSize i.val (a i)) := ⟨b,trivial⟩
  have ps : reads (prefixStart i.val (a i) origin) := ⟨so,trivial,block⟩
  have tot : reads (totalStart i.val (a i) origin) := ⟨ps,trivial,block⟩
  have ab : reads (abStart i.val (a i) origin) := ⟨tot,bc⟩
  exact ⟨b,ps,so,trivial,⟨ab,block⟩,ab,trivial,arena⟩

end CompressorRecords.BlockSlices

end VPVNP
end Computability
end OAI
