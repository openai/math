import OAI.Computability.VPVNP.CompressorRecordsBlockPlanner
import OAI.Computability.VPVNP.CompressorDescriptorScalars
import OAI.Computability.VPVNP.CompressorDescriptorHeads

/-!
# Initial and per-substep header visits

The initial cursor frame occupies scalar offsets six through thirteen.
Every level starts with a scalar visit and an array-head visit. At block
boundaries the next level is published with terminal metadata. Starting
another block relabels the same header in place, so a last block can end
with no residual lanes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockHeaderPlan

open BurstRAM BurstRAM.PrivateRAM PhaseRecipe BlockPlanner LevelFields DescriptorSpace
open scoped Fin.CommRing

/-- The address gap from the active frame to the directory is two plus the
catalog arity. Reading the runtime row count therefore locates level zero
without a literal for the arity of the program currently being constructed. -/
def firstHeader : Expr :=
  (Expr.publicWord 1).add ((((Expr.publicWord 1).sub (.publicWord 0)).add (.lit 1)).mul (.load
    (.publicWord 3)))

theorem firstHeader_eval {w : ℕ} (L : Layout) (base : Word w) (m : Memory w) (s : Word w)
    (hb : base = (L.base : Word w))
    (hr : m (base + 8).val = (directoryRows L : Word w)) :
    firstHeader.eval (Workspace.ports L.shape.arity base).data s m = (levelStart L 0 : Word w) := by
  change (base+((11+L.shape.arity : ℕ) : Word w)) +
    ((base+((11+L.shape.arity : ℕ) : Word w)-(base+9))+1) * m (base+8).val = _
  rw [hr,hb]
  simp only [levelStart, levelsBase, directoryBase, plannerTag, frameBase, Nat.zero_mul,
    Nat.add_zero, Nat.cast_add,
    Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  ring

/-- Address expression for the persistent cursor frame, beginning six words into the first
level header. -/
def persistentFrame := firstHeader.add (.lit 6)

/-- A single visit evaluating the supplied formula row at its source cursor and writing to the
destination operand. -/
def formula {g : ℕ} (row : FormulaRow g) (source dest : Expr) : Visit :=
  ⟨⟨_,_,_,row.recipe.table⟩,source,source.add (.lit 1),![dest,.lit 0,.lit 0,.lit 0,.lit 0]⟩

/-- A single deterministic visit sets the six input scalars of the first level. -/
def initialScalars (a : ℕ) : Visit :=
  formula (Scalars.initialRow (.terminal a)) persistentFrame firstHeader

/-- A single visit publishing the current level's array pointers from the current and initial
level headers. -/
def heads (F : Shape) (current : Expr) : Visit :=
  ⟨DescriptorHeads.worker F,.lit 0,.lit 1,![current,firstHeader,.lit 0,.lit 0,.lit 0]⟩

/-- The startup sequence that publishes initial scalar dimensions, publishes array heads and
scans the persistent cursor frame. -/
def initial (F : Shape) (a : ℕ) : List Visit :=
  [initialScalars a, heads F firstHeader, BlockPlanner.cursor persistentFrame]

/-- The source and destination may agree on the first visit of a block. The
formula row reads all six scalars before it begins the contiguous writes. -/
def update {a b c : ℕ} (p : Scalars.Pass a b) (q : Scalars.Pass b c) (source dest : Expr) : Visit :=
  formula (Scalars.advanceRow p q) source dest

/-- Start a fixed substep by installing its input metadata, then publish
terminal metadata and the incidence/record heads of the next level. -/
def substep {a b : ℕ} (F : Shape) (step : ℕ) (p : Scalars.Pass a b) : List Visit :=
  let old := atLevel step
  let next := atLevel (step+1)
  [update (.terminal a) p old old, update p (.terminal b) old next, heads F next]

theorem initial_length (F : Shape) (a : ℕ) : (initial F a).length = 3 := rfl
@[simp] theorem substep_length {a b : ℕ} (F : Shape) (step : ℕ) (p : Scalars.Pass a b) :
    (substep F step p).length = 3 := rfl

theorem substep_operands {a b w : ℕ} (F : Shape) (p : Scalars.Pass a b) (step : ℕ)
    {L : Layout} {first : ℕ} {pub : Fin 5 → Word w} {state : Word w} {m : Memory w}
    (e : Entry L first pub state m) :
    ((substep F step p)[0]).initial.eval pub state m = (levelStart L (first+step) : Word w) ∧
    (((substep F step p)[0]).params (0 : Fin 5)).eval pub state m = (levelStart L (first+step)
      : Word w) ∧
    ((substep F step p)[1]).initial.eval pub state m = (levelStart L (first+step) : Word w) ∧
    (((substep F step p)[1]).params (0 : Fin 5)).eval pub state m = (levelStart L (first+(step+1))
      : Word w) ∧
    (((substep F step p)[2]).params (0 : Fin 5)).eval pub state m = (levelStart L (first+(step+1))
      : Word w) :=
  ⟨eval_atLevel e step,eval_atLevel e step,eval_atLevel e step,eval_atLevel e
    (step+1),eval_atLevel e (step+1)⟩

end CompressorRecords.BlockHeaderPlan

end VPVNP
end Computability
end OAI
