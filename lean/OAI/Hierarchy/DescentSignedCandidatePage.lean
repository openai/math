import OAI.Hierarchy.DescentCalendarLiveOperand

namespace OAI
/-! The signed candidate word before resizing it to the receiver's destination bank. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentNextSignedWindow DescentOperandStateBanks DescentResetOperandComponents
open scoped Fin.CommRing
noncomputable section

def signedCandidateField {degree cap : ℕ} (signed : ℕ) (field : Field)
    (candidate : Option (Record degree cap)) : Cell signed :=
  (pointerField field).elim 0 (fun i => (Native.fields candidate i : Cell signed))

theorem signedCandidateField_resize {degree cap : ℕ} (signed coeff : ℕ) (field : Field)
    (candidate : Option (Record degree cap)) :
    ((signedCandidateField signed field candidate).val : Cell coeff) =
      nativeCandidateField signed coeff field candidate := rfl

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
