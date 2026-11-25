import OAI.Computability.BorderVNP.CellLocalSweep
import OAI.Computability.BorderVNP.CellCQFMeasured

/-! # Actual cost of preparing a block and extracting its short per-factor packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Local

open ExactQuantumFactoring.BitStackProgram

/-- Computing the factor-list length is the only counting operation in block preparation.
The concrete projection, pairing, and length programs have a fourth-degree clock here. -/
theorem prepareBlock_measured : Procedure.Measured (fun x => (blockArgCode x).length) 4 prepareBlock id :=
  Procedure.Measured.of_degree _ 4 (by decide) _ _ (by cqf_degree) (H := 1) (by simp)

/-- Projecting a single precomputed header and a single table is a linear cost, independent
of the subsequent local table-printing time. -/
theorem itemPacket_measured :
    Procedure.Measured (fun x => (prodCode blockDataCode (prodCode Nat.bits Typed.factor) x).length) 1 itemPacket id :=
  Procedure.Measured.of_degree _ 1 (by decide) _ _ (by cqf_degree) (H := 1) (by simp)

/-- Materializing the block header retains one copy of the factor list. The binary factor
count consumes at most the length of that list's encoding. -/
theorem prepare_length (b : BlockArg) :
    (blockDataCode (prepare b)).length+1 ≤ 8*((blockArgCode b).length+1) := by
  have h : b.2.2.factors.length.bits.length ≤ b.2.2.factors.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have count := h.trans (list_length_le_code Typed.factor b.2.2.factors)
  simp only [blockDataCode,blockArgCode,prepare,fieldsCode,blockCode,prodCode,pairBits_length]
  omega

end CellSparse.Packet.Emit.Local

end BorderVNP
end Computability
end OAI
