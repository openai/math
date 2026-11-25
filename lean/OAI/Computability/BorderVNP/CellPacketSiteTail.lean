import OAI.Computability.BorderVNP.CellPacketDelivered

/-! # Disjoint one-copy box and tally regions of the original private string

The tally row list starts at a fixed public offset after the entire box reservation.
The native opaque packet copier and the weighted-unary scan never share a source
bit, even as the true body length varies.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Source

/-- The padded literal holds the box at the front and the separate unary-position
description at a fixed publicly known offset. -/
def siteWithTally {description : ℕ} (width capacity : ℕ) (fs : List Factor)
    (tally : List Bool) (b : Fin description) : Bool :=
  if b.val < width+capacity then siteString width fs b else (tally[b.val-(width+capacity)]?).getD false

/-- Receiving a site string with a tally section supplies the opaque chunk's exact
input precondition, as well as the real bit words for the separate tally reader. -/
theorem siteWithTally_read {description : ℕ} (mem : ℕ → ℕ) (slot width capacity : ℕ)
    (fs : List Factor) (tally : List Bool) (room : (boxBody fs).length ≤ capacity)
    (fits : width+capacity+tally.length ≤ description)
    (received : ∀ b : Fin description, mem (slot+b.val) = (siteWithTally width capacity fs tally b).toNat) :
    Delivered (description := description) mem slot width fs ∧
      ∀ i : Fin tally.length, mem (slot+(width+capacity)+i.val) = tally[i.val].toNat := by
  constructor
  · intro b hb
    have before : b.val < width+capacity := by simp only [siteData,List.length_append,List.length_ofFn] at hb; omega
    simpa [siteWithTally,before] using received b
  · intro i
    have h := received ⟨width+capacity+i.val,by have := i.isLt; omega⟩
    simp only [siteWithTally, Nat.not_lt.mpr (Nat.le_add_right _ _), ite_false,
      Nat.add_sub_cancel_left,List.getElem?_eq_getElem i.isLt,Option.getD_some] at h
    simpa only [Nat.add_assoc] using h

end CellSparse.Packet.Source

end BorderVNP
end Computability
end OAI
