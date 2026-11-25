import OAI.Hierarchy.TraceNativeScale
import OAI.Hierarchy.CompressionBlock
import OAI.ThreeFlat.Diagonal.PhysicalBlockCharge

namespace OAI
/-! # A single physical compressor for every sufficiently large native verifier -/

noncomputable section
namespace Hierarchy.TraceDistribution

open ThreeFlat LinearAlgebra.SpectralBooks
open Diagonal
open scoped BigOperators Classical

variable {F : Type} [Field F]

def CompressionBlock.physical (B : CompressionBlock F) : PhysicalStage.Block F :=
  ⟨B.levels,B.positive,B.exponent,B.shrink,B.small,B.h,B.pad,B.γ,B.G.arcs,B.degree_pos,
    B.order_ge,B.G.symmetric,B.G.regular,B.G.loopless,B.real_bound,B.restore,B.refresh,B.contracts⟩

/-- A single compressor program serves every word width, machine and input at the
paper's scale. The actual native trace grid and all requested repetitions fit. -/
theorem feasible_native_block {F : Type} [Field F] [Fintype F]
    {d : ℕ} (large : 2≤d) (missing : ¬HasSpectralFlat F d) {u s : ℕ → ℕ} (scale : Scale u s)
    (pc regs words : ℕ) (program_pos : 0 < pc) :
    ∃ B : PhysicalStage.Block F, ∀ᶠ w : ℕ in Filter.atTop,
      B.blockCharge * s w ≤ u w+1-w/2 ∧ 2 ≤ u w+1-w/2 ∧ Fintype.card F ≤ 2^(64*w) ∧
      ∀ (M : Computability.VPVNP.BurstRAM.PrivateRAM.Machine (64*w) pc regs words) (b fuel : ℕ),
        b≤2^(u w) → fuel≤2^(u w) →
        NativeTrace.Fits M (b+(1+6*pc+words)*(64*w)) b ((u w+1-w/2)+w/2) fuel := by
  obtain ⟨C⟩ := compressionBlock_of_missing large missing
  let B := C.physical
  refine ⟨B,?_⟩
  filter_upwards [lane_room scale B.blockCharge,native_fits (F:=F) scale pc regs words program_pos]
    with w lanes h
  exact ⟨lanes,h.2.1,h.1,h.2.2.2.2⟩


end Hierarchy.TraceDistribution

end
end OAI
