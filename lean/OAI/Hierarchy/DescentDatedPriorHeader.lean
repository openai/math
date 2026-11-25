import OAI.Hierarchy.DescentDatedAddressRate
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentHaloWalkRAM
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! Public words for the common rank directory used first by the donor
material program and then by both endpoint queries. -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentHaloWalkRAM DescentSIMDLookup DescentDyadicSpan
def stride (H G M D : ℕ) := span (1+H+H*(breadth D*breadth D)+H*chunks G M)
def start (H G M D base j : ℕ) := base+j*stride H G M D
def endAddress (H G M D base:ℕ):=start H G M D base (breadth D+20)
theorem translated (H G M D base:ℕ):endAddress H G M D base=base+endAddress H G M D 0:=by
  simp only [endAddress,start,Nat.zero_add]
theorem lower (H G M D base:ℕ):base≤endAddress H G M D base:=Nat.le_add_right _ _
theorem rate {ι:ℕ→Type*} (H G M D:∀h,ι h→ℕ) (hosts:Bounded H)
    (degree:Bounded fun h i=>breadth (D h i)) (rows:Bounded fun h i=>H h i*chunks (G h i) (M h i)):
    Bounded (fun h i=>endAddress (H h i) (G h i) (M h i) (D h i) 0):=by
  have threshold:=((((Bounded.const 1).add hosts).add (hosts.mul (degree.mul degree))).add rows).padded
  simpa only [endAddress,start,stride,span,Nat.zero_add] using (degree.add (Bounded.const 20)).mul threshold
end Hierarchy.DescentDatedAddressBook.PriorHeader

end OAI
