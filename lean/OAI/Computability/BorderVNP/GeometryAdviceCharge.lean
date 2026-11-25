import OAI.Computability.BorderVNP.GeometryAdviceLiteral
import OAI.Computability.BorderVNP.GeometryOutputModel
import OAI.Computability.BorderVNP.GeometryAdvicePrepare
import OAI.Computability.BorderVNP.TransmissionSiteLiteral
import OAI.Computability.BorderVNP.TeamScales

/-! # Accounting for the actual geometry packet and its native instructions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdviceRate

open VPVNP VPVNP.BurstRAM GeometryFrameEncoding GeometryAdvice
open TeamScales TeamContraction

/-- Packed word count: six operands, three words per gate, query addresses, the
validity reference, and one address per output bit. -/
def packetWords (k u o b : ℕ) := 6+3*k+u+(o*b+1)

/-- The serialized packet length in the actual literal bit representation. -/
theorem bits_length {u o b W : ℕ} (base start : ℕ) (t : Table (Fin u ⊕ Fin 0) o b) (src : Fin u → ℕ) :
    (serialized (DiagonalResidueRAM.payload W base start t.circuit src ++
        GeometryOutput.referenceWords W base t)).length = packetWords t.size u o b*W := by
  simp [serialized_length,DiagonalResidueRAM.payload_length,packetWords]

/-- The combined native charge of literal-stripe reads, packet staging and output gathering. -/
def ticks (k u o b W : ℕ) :=
  beginStripe.slots + packetWords k u o b*W*(copyStripeBit.slots+1)+1 +
    GeometryAdvicePrepare.stageTicks u k (packetWords k u o b) W + GeometryOutput.ticks o b

/-- The live interpreter's cost, including serialization, is linear in the
number of wires times the machine word width. The upper bound permits the
four-gate AND/NOT expansion of each geometry frame gate. -/
theorem charge_le {g k u o b W : ℕ} (hk : k ≤ 4*g) (hb : 1 ≤ b) :
    ticks k u o b W + packetWords k u o b*W ≤ 3072*(g+u+o*b+1)*(W+1) := by
  let words := packetWords k u o b
  have hs := GeometryAdvicePrepare.stageTicks_le u k words W
  have ho := GeometryOutput.ticks_le o b
  have hinit : beginStripe.slots ≤ 100 := by decide
  have hbit : copyStripeBit.slots+1 = 10 := by decide
  have hrow : o ≤ o*b := Nat.le_mul_of_pos_right _ hb
  have hwords : words ≤ 12*(g+u+o*b+1) := by unfold words packetWords; omega
  have charge : ticks k u o b W + words*W ≤ 256*words*(W+1) := by
    unfold ticks
    change beginStripe.slots + words*W*(copyStripeBit.slots+1)+1 +
      GeometryAdvicePrepare.stageTicks u k words W + GeometryOutput.ticks o b + words*W ≤ _
    rw [hbit]
    have hu : u ≤ words := by unfold words packetWords; omega
    have hk' : k ≤ words := by unfold words packetWords; omega
    have hob : o*b ≤ words := by unfold words packetWords; omega
    have seven : 7 ≤ words := by unfold words packetWords; omega
    nlinarith
  calc
    _ ≤ 256*words*(W+1) := charge
    _ ≤ 256*(12*(g+u+o*b+1))*(W+1) := by gcongr
    _ = _ := by ring

/-- Both compact indices used in the site prefix fit the rounded physical address width. -/
theorem indexWidths {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) :
    1 ≤ logWidth r n ∧ Nat.clog 2 (n+1) ≤ logWidth r n ∧ Nat.clog 2 r ≤ logWidth r n := by
  have he : logWidth r n = Nat.clog 2 (2*n*r) := by
    unfold logWidth
    rw [← Real.natCeil_logb_natCast]
    norm_cast
  rw [he]
  have hn' := Nat.le_mul_of_pos_right (2*n) hr
  have hr' := Nat.le_mul_of_pos_left r (by omega : 0 < 2*n)
  exact ⟨Nat.clog_pos (by decide) (by omega),
    Nat.clog_mono_right _ (by omega), Nat.clog_mono_right _ hr'⟩

/-- The actual program prefix, two input cuts, three startup fields, site metadata
and the separate residue-advice bit all lie in this initial interval. -/
theorem prefix_le (p : UniversalMachine.Program) (args regs W : ℕ) {r n : ℕ}
    (hr : 1 ≤ r) (hn : 1 ≤ n) :
    entryLiteral p (W+1) n (ProcessorSlots.prefixCapacity r args regs W n+1) ≤
      (UniversalMachine.programPrefix p).length + (args+regs+12)*W + 12*logWidth r n+16 := by
  obtain ⟨_,h₁,h₂⟩ := indexWidths hr hn
  unfold entryLiteral cutWidth setupWidth ProcessorSlots.prefixCapacity TeamContraction.Wires.frameWidth
  nlinarith

end GeometryAdviceRate

end BorderVNP
end Computability
end OAI
