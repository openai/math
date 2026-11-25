import OAI.Computability.BorderVNP.TransmissionReferencePacket
import OAI.Computability.BorderVNP.DiagonalResidueRAMSources

/-! # Actual packed word banks in the native gathered reference packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA

variable {w d : ℕ}

private theorem word_window {w : ℕ} (mem : Memory w) (base : ℕ)
    (before after : List Bool) (xs : List (List Bool))
    (bits : ∀ j < (before ++ xs.flatten ++ after).length, (mem (base+j)).val =
      ((before ++ xs.flatten ++ after)[j]?.getD false).toNat) :
    DiagonalTallyBits.WordsAt mem (base+before.length) xs := by
  apply DiagonalResidueRAM.wordsAt_of_flat
  intro j
  have hj := j.isLt
  have mid : before.length+j.val < (before ++ xs.flatten).length := by
    simp only [List.length_append]
    omega
  have lt : before.length+j.val < (before ++ xs.flatten ++ after).length := by
    simp only [List.length_append] at mid ⊢
    omega
  have h := bits _ lt
  rw [List.getElem?_append_left mid, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hj, Option.getD_some, ← Nat.add_assoc] at h
  exact h

/-- The contiguous literal packet supplies the exact two decoded word banks and
the trailing reference index, all at their native addresses. -/
theorem ReferencePacket.word_banks (packet : ReferencePacket w d) (mem : Memory w) (dense : ℕ)
    (bitAt : ∀ i < packet.bits.length, (mem (dense+i)).val = (packet.bits[i]?.getD false).toNat) :
    DiagonalTallyBits.WordsAt mem dense (packet.entry.map wordBits) ∧
      DiagonalTallyBits.WordsAt mem (dense+packet.entry.length*w) ((List.ofFn packet.extension).map wordBits) ∧
      ∀ i : Fin d, (mem (dense+packet.offset+i.val)).val = (packet.reference i).toNat := by
  let front := (packet.entry.map wordBits).flatten
  let extension := (List.ofFn packet.extension).map wordBits
  have hfront : front.length = packet.entry.length*w := by
    change (packet.entry.flatMap wordBits).length = _
    simp [List.length_flatMap]
  have split : packet.bits = front ++ extension.flatten ++ List.ofFn packet.reference := by
    simp [ReferencePacket.bits,front,extension,List.flatMap_def]
  constructor
  · have h := word_window mem dense [] (extension.flatten ++ List.ofFn packet.reference) (packet.entry.map wordBits)
    apply (Nat.add_zero dense) ▸ h
    change ∀ i < ([] ++ front ++ (extension.flatten ++ List.ofFn packet.reference)).length, _
    simpa only [List.nil_append,List.append_assoc,split] using bitAt
  constructor
  · rw [← hfront]
    apply word_window mem dense front (List.ofFn packet.reference) extension
    simpa only [split] using bitAt
  · intro i
    have hi : packet.offset+i.val < packet.bits.length := by rw [packet.bits_length]; omega
    have h := bitAt _ hi
    simpa only [packet.reference_at i,Option.getD_some,Nat.add_assoc] using h

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
