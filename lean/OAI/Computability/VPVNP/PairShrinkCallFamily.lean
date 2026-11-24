import OAI.Computability.VPVNP.PairShrinkCallHeader
import OAI.Computability.VPVNP.PairSimulationMapHandlerImage
import OAI.Computability.VPVNP.PairSimulationMapInvocationClock

/-!
# Fixed map handlers at one shrinking substep

The grid point and party select an inlined handler with a fixed old degree.
Every handler evaluates its descriptor from the old header, popped node,
geometry, histogram, shrink scratch and selected motif ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallABI

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.PhaseRecipe
open Compression Compression.ShrinkMotif MotifConversion
open scoped Fin.CommRing

/-- Old header, popped node, geometry pointer, histogram, shrink scratch,
then the motif ordinal for the writer's state register. -/
def sourceSlot : Fin 6 → Fin 24 := ![11, 0, 9, 10, 8, 18]

/-- Identify each of the six recipe inputs with its register in the shared 24-register locator
bank. -/
def source (j : Fin 6) : MapHandlerImage.Source 24 := .inr (.inr (sourceSlot j))

/-- The popped DFS node address, supplied in public operand one of the shrinking map recipe. -/
def node : Expr := .publicWord 1

/-- Build the call's address expressions from the old header, dense motif, private scratch
base, and histogram. Header cell 17 supplies the live size used in both strides. -/
def operands (degree : ℕ) : ShrinkCallHeader.Operands :=
  let level := Expr.publicWord 0
  let n := Expr.load (level.add (.lit 17))
  ⟨level, .state, n, ((Expr.lit (2 * degree)).mul n).add (.lit 1),
    .publicWord 4, n.mul n, .publicWord 3⟩

/-- The shrink part of the common parameter-entry numbering, and the raw
descriptor and field expressions consumed by the installed map writer. -/
noncomputable def family {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    (degree a : ℕ) {t : ℕ} (ordinal : B.Entry → Fin t) : MapHandlerImage.Family B.shrink t 24 where
  regCount i := RegisterSetup.regCount (MapCallTable.formulas
    (MapEntryTable.allocation B.shrink i.1 i.2) (Fintype.equivFin _) (Fintype.equivFin _)) + 3
  portCount i := Nat.card (MapEntryTable.PublicPort B.shrink i.1 i.2)
  layout i := MapInline.layout B.shrink i.1 i.2
  ordinal := ordinal ∘ Sum.inl
  base _ := ((operands degree).inputs a).descriptor
  field i := ((operands degree).inputs a).fields i.2
  source _ := source

variable {w p r : ℕ} (c : Config w p r) (common : Fin 24 ↪ Fin r)

/-- Read the five public recipe operands from the common registers selected by the shrink call
interface. -/
def pub (j : Fin 5) : Word w := c.reg (common (sourceSlot j.castSucc))

/-- Read the sixth recipe input, the dense motif ordinal passed as the formula writer's state. -/
def state : Word w := c.reg (common (sourceSlot 5))

section Family

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  (degree a : ℕ) {t : ℕ} (ordinal : B.Entry → Fin t)
  (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (i : MapHandlerImage.Index B.shrink)

theorem input_reg (j : Fin 6) :
    (family B degree a ordinal).inputs dfs saved common i j = common (sourceSlot j) := rfl

/-- The writer and the gather programs evaluate their recipes on this same
five-word bank and state. -/
theorem inputs_readback :
    (fun j : Fin 5 ↦ c.reg ((family B degree a ordinal).inputs dfs saved common i j.castSucc)) =
      pub c common ∧
    c.reg ((family B degree a ordinal).inputs dfs saved common i 5) = state c common :=
  ⟨rfl, rfl⟩

end Family

end PairSimulation.ShrinkCallABI

end VPVNP
end Computability
end OAI
