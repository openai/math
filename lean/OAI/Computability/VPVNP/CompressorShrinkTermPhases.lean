import OAI.Computability.VPVNP.CompressorShrinkTermSelection
import OAI.Computability.VPVNP.CompressorShrinkDemandFrame

/-!
# The consecutive demand-gather and term-selection segments

The first segment reads the balanced AB table and old CD table. Its final
memory is the initial memory of the second segment. The second segment
admits precisely the paper's term choices. Its final memory contains
both the selected term rows and the original widths and starts needed
by the shrinking kernel.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkTermSelection

open Compression Compression.PackingData MotifGrid MotifBlocks ShrinkMotif BurstRAM
open scoped Classical

variable {a g w : ℕ} {k : Type*} [_root_.Field k] {factor : ℝ}
variable (F : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (X : State a (packingLaneBits a g))

/-- Number of directed packed bundles, counting each base vertex, packing tag, residual lane
and outgoing port. -/
abbrev bundles := Fintype.card X.Base * (2^(packingTagBits (2^a)) * 2^g) * 2^a
/-- Number of motif ranks or balanced pieces in one shrinking bundle at input degree exponent
`a`. -/
abbrev ranks (a : ℕ) := pieceCount (2^a) (2*2^a+1)

theorem motifCount_eq : ShrinkTermInputs.motifCount X = bundles X * ranks a :=
  (Fintype.card_congr (ShrinkMotifOrder.stateNumber X)).trans (Fintype.card_fin _)

/-- Readback of the thick and CD width rows and AB pieces in their physical per-bundle orders. -/
noncomputable abbrev oldRows (thick cdRows ab : Fin 5 → BurstRAM.Word w) (mem : Memory w) :=
  DemandWidths.Stored X.packingData (Shrink.packedIndex X.baseIndex) X.packingWidth
    X.shrinkOrder X.shrinkNumber thick cdRows ab mem

local notation "N" => ShrinkTermInputs.motifCount X

set_option maxHeartbeats 1000000 in
theorem gather_select (thick cdRows ab : Fin 5 → BurstRAM.Word w) (dense term : BurstRAM.Word w)
    (stride : ℕ) (wide : 10 ≤ stride) (sep : dense.val+N*2 ≤ term.val)
    (room : term.val+N*stride < 2^w) (ref : Memory w) (stored : oldRows X thick cdRows ab ref)
    (layout : ShrinkDemandGather.Layout (bundles X) (ranks a) (ShrinkTermInputs.operands cdRows ab dense))
    (earlier : ShrinkDemandFrame.Before (bundles X) (2^(2*2^a+1)*2^a/4) (ranks a) thick cdRows ab dense.val)
    (fit : fitConstant F+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (cap : ℕ) (gatherCap : ShrinkDemandGather.cost < cap) (termCap : TermWorker.budget F 2 8 w X.maxWireWidth ≤ cap) :
    ∃ gs, ShrinkDemandGather.Gathered (bundles X) (ranks a) (ShrinkTermInputs.operands cdRows ab dense) cap ref gs ∧
      let mem := after ref (eventLog gs)
      (∀ bs : Fin N → List Bool, (runSegment (termProgram F dense term stride) cap (some 0) mem (List.ofFn bs)).isSome ↔
        ∃! s : X.ShrinkSelection F, bs = tapes F X s w) ∧
      ∀ s : X.ShrinkSelection F, ∃ ts, Written F X dense term stride cap s mem ts ∧
        oldRows X thick cdRows ab (after mem (eventLog ts)) := by
  obtain ⟨gs,hgs,hpair⟩ := ShrinkTermInputs.gather X.packingData (Shrink.packedIndex X.baseIndex) X.packingWidth
    X.shrinkNumber X.shrinkOrder thick cdRows ab dense ref stored layout gatherCap
  let mid := after ref (eventLog gs)
  obtain ⟨legal,full⟩ := native F X dense term stride wide sep room mid hpair fit cap termCap
  refine ⟨gs,hgs,legal,fun s => ?_⟩
  obtain ⟨ts,hw⟩ := full s
  refine ⟨ts,hw,ShrinkDemandFrame.retain stored earlier (fun x hx => ?_)⟩
  exact (hw.frame x (.inl (by omega))).trans (hgs.frame x (.inl hx))

end CompressorRecords.ShrinkTermSelection

end VPVNP
end Computability
end OAI
