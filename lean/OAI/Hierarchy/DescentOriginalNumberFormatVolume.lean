import OAI.Hierarchy.DescentOriginalNumberInvoice

namespace OAI
/-! # A linear volume bound for all three native original-number formats -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs
noncomputable section
variable {s : CandidateSheets} (u : s.OriginalInputs)

def formatFactor (X Q stems privateSlots N U W C : ℕ) : ℕ :=
  let c := 2*U + 2*(U+1+N*(2*U+22)) + 33
  let jobs := X*(Q+1)
  staticCost C + staticCost (12*C) + (4+jobs*(4+(2*c+4))) +
    7*(15+jobs*(11+4*c)) +
    266240*(X*stems+1)*(2+C) + 2048*(X*privateSlots+1)*(W+1)*(2+C)

/-- The receiver supplies bounds on the actual mounted dictionaries. Its three
formats may have different widths and source-expression costs. -/
theorem format_volume (base U W C E : ℕ) (nonempty : 1≤E) (rows : s.rows≤E)
    (publicCount : (u.publicSide base).count≤C*E)
    (pub : 2^(u.publicSide base).date.width≤C*E)
    (stem : 2^(7*s.stemBits*s.lanes)≤C*E) (privatePage : 2^(u.privateSide base).width≤C*E) :
    u.publicCost base U + 266240*(s.blocks*u.stems+1)*(1+s.rows+2^(7*s.stemBits*s.lanes)) +
      (u.privateSide base).pagePrice W ≤
      formatFactor s.blocks s.contacts u.stems s.privates u.signedSlots U W C * E := by
  let jobs := s.blocks*(s.contacts+1)
  let cost := 2*U+2*(U+1+u.signedSlots*(2*U+22))+33
  have price : 2*U+2*max U (1+u.signedSlots*(2*U+22))+33 ≤ cost := by
    dsimp only [cost]
    omega
  change staticCost (u.publicSide base).count + staticCost (12*2^(u.publicSide base).date.width) +
      (4+jobs*(4+s.rows*(2*_+4))) + 7*(15+jobs*(11+4*_)) +
      266240*(s.blocks*u.stems+1)*(1+s.rows+2^(7*s.stemBits*s.lanes)) +
      2048*(s.blocks*s.privates+1)*(W+1)*(1+s.rows+2^(u.privateSide base).width) ≤ _
  calc
    _ ≤ staticCost (C*E) + staticCost (12*(C*E)) + (4+jobs*(4+E*(2*cost+4))) +
        7*(15+jobs*(11+4*cost)) + 266240*(s.blocks*u.stems+1)*(1+E+C*E) +
        2048*(s.blocks*s.privates+1)*(W+1)*(1+E+C*E) := by
      unfold staticCost
      gcongr
    _ ≤ _ := by
      cases E with
      | zero => omega
      | succ e =>
        dsimp only [formatFactor,staticCost,jobs,cost]
        ring_nf
        omega

end
end Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs

end OAI
