import Mathlib.Data.Finset.Union

namespace OAI
/-! # Sites in the original host graph within a given number of hops -/
namespace Hierarchy.DescentOrdinaryDonorHalo
variable {V : Type} [DecidableEq V]

/-- This public halo only traverses the fixed rack adjacency, including a
stay at each hop. The old block number is carried separately. -/
def around (near : V→Finset V) : ℕ→V→Finset V
  | 0,v=>{v}
  | t+1,v=>(around near t v).biUnion fun u=>insert u (near u)

end Hierarchy.DescentOrdinaryDonorHalo

end OAI
