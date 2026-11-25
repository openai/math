import OAI.Hierarchy.DescentFundedClipChoice
import OAI.Hierarchy.DescentReturnUnitRate

namespace OAI
/-! # A common public lane amount for the signed, funded, and next-event banks -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentCompiler.TerminalScale
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

/-- Rounding the three funded source pitches uses exactly eight copies of the largest digit. -/
theorem funded_density_exact (extra : ℕ) :
    v.fundedWorkingUnit extra=8*v.fundedMaxUnit extra :=by
  change max (2*(4*v.fundedPanelUnit)) (max (2*(4*v.area.unit)) (8*(v.fundedClip extra).unit))=_
  unfold fundedMaxUnit
  omega

/-- The input amount and outgoing paid density are read from the original checkout price. -/
theorem source_density (extra : ℕ) :
    v.unit≤v.fundedMaxUnit extra ∧
    (2^v.area.k)*v.fundedWorkingUnit extra=8*((2^v.area.k)*v.fundedMaxUnit extra) :=by
  refine ⟨(le_max_left v.area.unit (v.fundedClip extra).unit).trans (le_max_right ..),?_⟩
  rw [v.funded_density_exact]
  ring
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
