import OAI.Hierarchy.DescentLateContactDatePrice
import OAI.Hierarchy.DescentScheduledContactRoom
import OAI.Hierarchy.DescentNamedResetSheetScale

namespace OAI
/-! # Contact tariff coefficients from the measured finite candidate sheets -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section
variable {ι : ℕ→Type*} (J : ℕ→ℕ) (p : ∀h,ι h→ResetOutput)

/-- The original capacity is the paid prefix of the cap calendar. All other
contact counts come from its physical candidate sheet and original degree. -/
theorem reached_contact_controls {original : ∀h,ι h→ℕ}
    (f : CandidateSheets.LocalFields J (fun h i=>(p h i).sheets) (fun h i=>(p h i).front.peer.shapes) original)
    (cap : SmallAt J (fun h i=>(p h i).front.donor.cap))
    (degree : SmallAt J (fun h i=>(p h i).front.donor.degree)) (aligned : ∀h i,ContactAligned (p h i)) :
    ∃e,∀ᶠ h : ℕ in atTop,∀i,(p h i).contactShape.Controls (scale (J h) e):=by
  have low : SmallAt J (fun h i=>(p h i).front.donor.lows):=
    f.block.of_le fun h i=>(aligned h i).blocks.symm.le
  have handles:=low.mul ((SmallAt.const J 2).mul cap)
  obtain ⟨e,fits⟩:=((((handles.add f.contact).add f.shapes).add f.block).add degree)
  refine ⟨e,fits.mono fun h room i=>?_⟩
  have packed:=room i
  dsimp only at packed
  have sockets:=(aligned h i).maskedContacts
  constructor
  · change (p h i).front.donor.lows*(2*(p h i).front.donor.cap)≤_
    omega
  · rw [sockets];omega
  · change (p h i).front.peer.shapes≤_
    omega
  · change (p h i).sheets.blocks≤_
    omega
  · change (p h i).front.donor.degree≤_
    omega

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
