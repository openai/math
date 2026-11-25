import OAI.Hierarchy.DescentResetReceivedContactScale
import OAI.Hierarchy.DescentContactFieldPolynomial

namespace OAI
/-! # Local calendar parameters for the two real contact scans -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentContactFieldPolynomial

def contactFields (v : ResetOutput) : Fields :=
  let a:=v.front.donor
  let c:=v.front.contact
  ⟨a.boardFields,a.laneFields,a.returnFields,(a.lows*(2*a.cap))*2,a.degree,
    DescentResetSignedHaloMatrix.termWork a.degree,c.oldFields,c.viewCount,c.shapes,c.sockets,c.donors⟩

theorem factor_eq (v : ResetOutput) (U : ℕ) :
    v.contactFactor U=coefficient v.contactFields U := rfl

variable {ι : ℕ→Type*} {J : ℕ→ℕ} (v : ∀h,ι h→ResetOutput)
    (U : ∀h,ι h→ℕ)

theorem contact_factor_paid (localFields : Bounds J (fun h i=>(v h i).contactFields))
    (work : SmallAt J U) : SmallAt J (fun h i=>(v h i).contactFactor (U h i)) := by
  simp only [factor_eq]
  exact paid localFields work

end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
