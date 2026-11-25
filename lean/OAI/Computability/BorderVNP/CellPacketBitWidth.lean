import OAI.Computability.BorderVNP.CellPacketInputSize

/-! # Transport cost at the genuine bit width of the global packet fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet

open RationalHitting.StackLanguage
open private scalar_records_le from OAI.Computability.BorderVNP.CellPacketInputSize

/-- Each raw numeric field costs at most four bits per binary digit plus four framing
bits. The packet is delimited once before the external Boolean assignment. -/
theorem input_length_of_width (D : Directory) (p : ℕ) (ext : List Bool) {W L : ℕ}
    (hw : (words D p).length ≤ W) (width : ∀ x ∈ words D p, x.size ≤ L) :
    (input D p ext).length ≤ W*(4*L+4) + 1 + ext.length := by
  have hb : (bits D p).length ≤ W*(2*L+2) :=
    (scalar_records_le _ width).trans (Nat.mul_le_mul_right _ hw)
  rw [input, List.length_append, codeWord_length]
  calc
    _ ≤ 2*(W*(2*L+2)) + 1 + ext.length := by omega
    _ = _ := by ring

/-- The one-copy syntax weights determine the word count independently of the numerical
values of global gadget IDs and raw pointers. Only their actual binary width is charged. -/
theorem input_length_from_static (D : Directory) (p : ℕ) (ext : List Bool) {A M L : ℕ}
    (hs : D.StaticBounds A M) (hb : storedMass D ≤ A*(M+1)^2)
    (width : ∀ x ∈ words D p, x.size ≤ L) :
    (input D p ext).length ≤ (8*A+4)*(M+1)^2*(4*L+4) + 1 + ext.length :=
  input_length_of_width D p ext (words_length_from_static D p hs hb) width

end CellSparse.Packet

end BorderVNP
end Computability
end OAI
