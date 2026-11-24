import OAI.Computability.VPVNP.LiveVirtualPairHistograms

/-! # The physical auxiliary header fits the virtual processor bank -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression CursorNetwork CursorBounds LiveProgram PairStages PairStages.Group
open PrimedInputRAM

variable {D : FixedProgramDiagonal.Program} {n C : ℕ} {K : Type*} [Field K] {S : BlockSchedule K}
    {B : S.Templates} {u : PairExponents B.growthConstant} {hn : 2 ≤ n}
    (V : D.VirtualPairs B u hn C) {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}

include V in
/-- Includes the seven input fields, both reserved exterior capacities,
and the whole dense grammar histogram. -/
theorem VirtualPairs.shadowCapacity (hC : D.constants.circuitExponent = C)
    (i : Fin (2^(Auxiliary.sizes (D.executionGroup n ht hf)).h)) :
    LiveAuxiliaryHeaders.span (Auxiliary.pairLengths (D.executionGroup n ht hf) i)
      (Auxiliary.histLength (D.executionGroup n ht hf)) ≤
        2^LiveProgram.Layout.virtualSiteBits.eval (D.geometry n) := by
  let j := i.cast (congrArg (2^·) (heights (D := D) (n := n) (ht := ht) (hf := hf))).symm
  have counts := (V.counts j (fun _ => false) (fun _ => 0)).fits.headers
  have eq : physicalPairIndex (ht := ht) (hf := hf) j = i := Fin.ext rfl
  have size := physicalPairLengths (ht := ht) (hf := hf) j
  rw [eq] at size
  rw [LiveAuxiliaryHeaders.span,size,physicalGrammarCount hC,LiveProgram.Layout.virtualSiteBits_eq
    _ (show 1 ≤ n by omega)]
  rw [V.scratch] at counts
  exact counts

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
