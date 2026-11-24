import OAI.Computability.VPVNP.PairShrinkVertexStage
import OAI.Computability.VPVNP.PairShrinkCallABI
import OAI.Computability.VPVNP.PairSimulationShrinkGatherImage
import OAI.Computability.VPVNP.CompressorLevelCounts

/-!
# The fixed finite image of a shrinking vertex visit

The block schedule fixes the old and new degree of every shrinking substep. At the
selected substep the machine guesses the child packets and absorbed bits, selects the
recorded layout, gathers the actual party fields, executes the selected matrix, and
increments the private parameter histogram. Its only public bank is the terminal ABI.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkVertexImage

open BurstRAM BurstRAM.PrivateRAM VertexImage Compression CompressorRecords
open MotifConversion ShrinkMapImage

/-- The old header and packed owner already occupy locator registers 11 and 7. The
remaining map-control registers and its zero word have a separate interval. -/
def mapRegisters : Registers 24 where
  header := ⟨![11, 7, 14, 15, 16, 17, 18, 19, 20, 21, 22], by decide⟩
  zero := 23
  apart := by decide

@[simp] theorem mapRegisters_level : mapRegisters.header 0 = 11 := rfl
@[simp] theorem mapRegisters_owner : mapRegisters.header 1 = 7 := rfl
@[simp] theorem mapRegisters_ordinal : mapRegisters.header 6 = 18 := rfl

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    {t : ℕ} (ord : B.Entry → Fin t) (i : Fin S.steps)

/-- The six-party map handler family for this scheduled old degree and the global
parameter-entry numbering. -/
abbrev matrixFamily := ShrinkCallABI.family B (slotDegree S) (S.degreeExponent i.castSucc) ord

/-- Both layout gathers use the actual old and new degree and the same live operands
as the matrix writer. -/
def gatherFamily : ShrinkGatherBank.Family (matrixFamily B ord i) where
  a := S.degreeExponent i.castSucc
  b := S.degreeExponent i.succ
  operands _ := ShrinkCallABI.operands (slotDegree S)
  node _ := ShrinkCallABI.node

/-- The located native resident map handler, including its operand gathers and the locator
embedding into the shared register bank. -/
def maps : LocatedBody where
  code := Registers.segmentWithGather (matrixFamily B ord i) (gatherFamily B ord i) mapRegisters
  locator := (Fin.castAddEmb 10).trans
    (Registers.gatherShared (matrixFamily B ord i) (gatherFamily B ord i))

/-- A complete eleven-public-word shrinking segment, fixed across all visited levels and
all input lengths. The caller supplies only the numbering of its fixed parameter entries. -/
def shrinkSegment : Segment := ShrinkVertexStage.image B (maps B ord)

/-- The installed selected map body includes the input reader, both layout branches, the
gather loops, the matrix writer, and the actual rejecting opcode. -/
theorem map_linked {p r w : ℕ} (M : Machine w p r 11) (pc : Fin (maps B ord i).code.count → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
    (reg : Fin (maps B ord i).code.privateRegs ↪ Fin r) (done : Fin p)
    (rows : ∀ a, M.code (pc a) = ((maps B ord i).code.row pc dfs saved reg done a).resize w) :
    let F := matrixFamily B ord i
    let G := gatherFamily B ord i
    Registers.GatherLinked F G mapRegisters (pc ∘ Registers.gatherLocations F G)
      dfs saved ((Registers.gatherShared F G).trans reg) ((Registers.gatherMatrix F G).trans reg)
      ((Registers.gatherLocal F G).trans reg) (reg (Registers.layoutTemp F G)) done M := by
  intro F G
  apply Registers.gatherLinked
  exact Registers.gatherSegment_rows F G mapRegisters dfs saved done pc reg M rows

end PairSimulation.ShrinkVertexImage

end

end VPVNP
end Computability
end OAI
