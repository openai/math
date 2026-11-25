import OAI.Computability.BorderVNP.CellLocalSweep
import OAI.Computability.BorderVNP.CellBoxResolutionMeter

/-! # Preparing a resolved box with its original global ordinal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Local

open ExactQuantumFactoring.BitStackProgram
open private sum_length from OAI.Computability.BorderVNP.CellEmitBoxCounts
open private weights_le from OAI.Computability.BorderVNP.CellBoxResolutionMeter

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

/-- Physical size of the prepared sweep parameters and its compact directory. -/
def sweepSpan (x : SweepInput) := (paramsCode x.1).length+blockSpan x.2

/-- The additional input of a particular indexed visit contains one ordinal and block. -/
def visitSpan (x : SweepInput × ℕ × BoxBlock) :=
  sweepSpan x.1+x.2.1.bits.length+(blockCode x.2.2).length

/-- The actual local packet used by the indexed visit. -/
def visit (x : SweepInput) (i : ℕ) (b : BoxBlock) : BlockArg :=
  (x.1,((x.2.blocks.take i).map fun z => z.copies*z.factors.length).sum,b)

private theorem visit_code_size (x : SweepInput × ℕ × BoxBlock) :
    (visitCode x).length+1 ≤ 8*(visitSpan x+1) := by
  have hd : (Typed.directory x.1.2).length ≤ blockSpan x.1.2 := Nat.le_add_right ..
  change (prodCode (prodCode paramsCode Typed.directory) (prodCode Nat.bits blockCode) x).length+1 ≤ _
  rw [prodCode,pairBits_length,prodCode,pairBits_length,prodCode,pairBits_length]
  simp only [visitSpan,sweepSpan]
  omega

/-- The binary starting ordinal has length bounded by the encoded list of compact
block multiplicities, including when a block's repeat count is extremely large. -/
theorem start_bits_le (D : Directory) (i : ℕ) :
    ((D.blocks.take i).map fun b : BoxBlock => b.copies*b.factors.length).sum.bits.length ≤ blockSpan D := by
  let ws := D.blocks.map fun b => b.copies*b.factors.length
  have h := sum_length (ws.take i) 0
  have hc := (listCode_length_take_le Nat.bits i ws).trans (weights_le D.blocks)
  rw [List.map_take]
  change (ws.take i).sum.bits.length ≤ blockSpan D
  change ((ws.take i).sum+0).bits.length ≤ (listCode Nat.bits (ws.take i)).length+0 at h
  simp only [blockSpan,Nat.add_zero] at h ⊢
  omega

/-- The visited local argument contains no copy of the full private directory. -/
theorem visit_arg_size (x : SweepInput) (i : ℕ) (b : BoxBlock) (hb : b ∈ x.2.blocks) :
    (blockArgCode (visit x i b)).length+1 ≤ 5*(sweepSpan x+1) := by
  have h := start_bits_le x.2 i
  have hh := code_le_of_mem blockCode hb
  have hw : (listCode blockCode x.2.blocks).length ≤ blockSpan x.2 := Nat.le_add_left ..
  change (prodCode paramsCode (prodCode Nat.bits blockCode) (visit x i b)).length+1 ≤ _
  rw [prodCode,pairBits_length,prodCode,pairBits_length]
  simp only [visit,sweepSpan]
  omega

/-- Project the sweep directory once and recover the resolved one-copy list. -/
theorem measured_sweepBlocks : Procedure.Measured sweepSpan 30
    (getBlocks.comp (Procedure.second paramsCode Typed.directory)) id := by
  apply Procedure.Measured.comp
  · apply Procedure.Measured.of_degree _ 30 (by decide) _ _ (by cqf_degree) (H:=3)
    intro x
    simp only [id_eq,prodCode,pairBits_length,sweepSpan,blockSpan]
    omega
  · apply Procedure.Measured.reparam measured_getBlocks _ (H:=1)
    simp [sweepSpan]

/-- The physical subroutine computing the globally correct block start costs at most
degree thirty in the true directory, sweep parameters, block and index. -/
theorem measured_visitPacket : Procedure.Measured visitSpan 30 visitPacket id := by
  let owner := Procedure.first sweepCode (prodCode Nat.bits blockCode)
  let item := Procedure.second sweepCode (prodCode Nat.bits blockCode)
  let p := (Procedure.first paramsCode Typed.directory).comp owner
  let d := (Procedure.second paramsCode Typed.directory).comp owner
  let i := (Procedure.first Nat.bits blockCode).comp item
  let b := (Procedure.second Nat.bits blockCode).comp item
  have hp : Procedure.Measured visitSpan 30 p id :=
    Procedure.Measured.of_degree _ _ (by decide) _ _ (by cqf_degree) (H:=8) visit_code_size
  have hd : Procedure.Measured visitSpan 30 d id :=
    Procedure.Measured.of_degree _ _ (by decide) _ _ (by cqf_degree) (H:=8) visit_code_size
  have hi : Procedure.Measured visitSpan 30 i id :=
    Procedure.Measured.of_degree _ _ (by decide) _ _ (by cqf_degree) (H:=8) visit_code_size
  have hb : Procedure.Measured visitSpan 30 b id :=
    Procedure.Measured.of_degree _ _ (by decide) _ _ (by cqf_degree) (H:=8) visit_code_size
  unfold visitPacket
  apply Procedure.Measured.pair _ _ _ hp
  apply Procedure.Measured.pair _ _ _ _ hb
  apply Procedure.Measured.comp _ _ _ (Procedure.Measured.pair _ _ _ hd hi)
  apply Procedure.Measured.reparam measured_getBlockStart _ (H:=1)
  intro x
  simp only [visitSpan,sweepSpan,Nat.one_mul,id_eq,Function.comp_apply]
  omega

/-- An actual visit to an indexed block fits the entire sweep size within a fixed factor. -/
theorem visitSpan_le (x : SweepInput) (i : Fin x.2.blocks.length) :
    visitSpan (x,i.val,x.2.blocks[i])+1 ≤ 3*(sweepSpan x+1) := by
  have hi : i.val.bits.length ≤ i.val := by
    rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hn := list_length_le_code blockCode x.2.blocks
  have hb := code_le_of_mem blockCode (List.getElem_mem i.isLt)
  change (blockCode x.2.blocks[i]).length ≤ _ at hb
  have hh := i.isLt
  simp only [visitSpan,sweepSpan,blockSpan]
  omega

end CellSparse.Packet.Emit.Local

end BorderVNP
end Computability
end OAI
