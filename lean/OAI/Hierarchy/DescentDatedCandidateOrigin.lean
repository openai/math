import OAI.Hierarchy.DescentDatedPeerAperture
import OAI.Hierarchy.DescentResetTrunkChip
import OAI.Hierarchy.DescentResetTrunkScalar

namespace OAI
/-! # From issued roots to the physical peer directory and the observed trunk tags -/
namespace Hierarchy.DescentDatedAddressBook.PeerAperture
open DescentDyadicSpan DescentSixParty Filter
noncomputable section
variable (a : PeerAperture)

def chipEnd (base : ℕ) := base+span (a.oldHosts*a.shapes)+span (a.shapes*2^a.evidenceLanes)
def rawEnd (base : ℕ) :=a.endAddress (a.chipEnd base)+a.hosts

theorem chip_placed {n h : ℕ} (board : NonlinearExpanders.Graph n h) (r height : ℕ)
    (count : a.shapes=(DescentDenseHostOrder.roster board r height).card) (base : ℕ) :
    a.chipEnd base=DescentResetTrunkChip.endAddress board r height base a.oldHosts a.evidenceLanes := by
  simp [chipEnd,DescentResetTrunkChip.endAddress,DescentResetTrunkChip.start,count]

theorem raw_extent (base : ℕ) : a.rawEnd base=base+a.rawEnd 0 := by
  unfold rawEnd
  rw [a.extent (a.chipEnd base),a.extent (a.chipEnd 0)]
  simp only [chipEnd,Nat.zero_add]
  omega

theorem raw_rate {ι : ℕ→Type*} (q : ∀h,ι h→PeerAperture)
    (old : Bounded (fun h i=>(q h i).oldHosts)) (shapes : Bounded (fun h i=>(q h i).shapes))
    (degree : Bounded (fun h i=>(q h i).oldDegree)) (evidence : Bounded (fun h i=>(q h i).evidence))
    (groups : Bounded (fun h i=>(q h i).groups)) (lanes : Bounded (fun h i=>(q h i).lanes))
    (packed : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(q h i).bits*(q h i).evidenceLanes≤K*h)
    (oneBit : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(q h i).evidenceLanes≤K*h) :
    Bounded (fun h i=>(q h i).rawEnd 0) := by
  obtain ⟨K,key⟩:=oneBit
  have page:=Bounded.pow_of_linear (K:=K) key
  have pub:=bounded q old shapes degree evidence groups lanes packed
  have H:=old.mul shapes
  apply (((H.padded.add (shapes.mul page).padded).add pub).add H).of_le
  intro h i
  rw [rawEnd,(q h i).extent]
  simp only [chipEnd,hosts,span,Nat.zero_add,Nat.le_refl]

end
end Hierarchy.DescentDatedAddressBook.PeerAperture

end OAI
