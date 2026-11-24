import OAI.Computability.VPVNP.PairSimulationShrinkGatherRegisters
import OAI.Computability.VPVNP.PairShrinkVertexImage

/-!
# Live operands across the selected shrinking-row dispatch

The actual five public operand registers survive the resident ID, term and
layout reads. The state operand is exactly the overwritten motif ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkVertexImage

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords ShrinkMapImage
open ShrinkMapImage.Registers

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  {t r : ℕ} (ord : B.Entry → Fin t) (i : Fin S.steps)
  (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
  (locals : Fin (maps B ord i).code.privateRegs ↪ Fin r)

local notation "F" => matrixFamily B ord i
local notation "G" => gatherFamily B ord i
local notation "cm" => Function.Embedding.trans (gatherShared (F) (G)) locals
local notation "tmp" => locals (layoutTemp (F) (G))

theorem route_abi (ds : ∀ a j, locals a ≠ dfs j) (ss : ∀ a j, locals a ≠ saved j)
    (idx : MapHandlerImage.Index B.shrink) :
    (∀ j, Protected mapRegisters (cm) (tmp) (dfs j)) ∧
    (∀ j : Fin 5, Protected mapRegisters (cm) (tmp)
      ((F).inputs dfs saved (cm) idx j.castSucc)) ∧
    (F).inputs dfs saved (cm) idx (Fin.last 5) = (mapRegisters.headerReg (cm)) 6 := by
  have apart := (hosted_banks (F) (G) dfs saved locals ds ss).2.2
  have separated : ∀ j : Fin 5, ShrinkCallABI.sourceSlot j.castSucc ≠ mapRegisters.zero ∧
      ∀ l : Fin 11, 6 ≤ l.val → l.val ≤ 9 → ShrinkCallABI.sourceSlot j.castSucc ≠
        mapRegisters.header l := by decide
  refine ⟨?_, ?_, rfl⟩
  · intro j
    exact ⟨(ds _ _).symm, (ds _ _).symm, fun l _ _ ↦ (ds _ _).symm⟩
  · intro j
    have spec := separated j
    exact ⟨apart _, (cm).injective.ne spec.1,
      fun l lo hi ↦ (cm).injective.ne (spec.2 l lo hi)⟩

end PairSimulation.ShrinkVertexImage

end VPVNP
end Computability
end OAI
