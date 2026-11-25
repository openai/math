import OAI.Hierarchy.DescentPackedVenueOrdinals

namespace OAI
namespace Hierarchy.DescentHostDirectory.SiteDecode
def trim (k g slots : ℕ) (hub : Bool) (raw : ℕ) :=
  if hub then
    let node:=raw/slots
    let depth:=Nat.log 2 (node+1)
    let id:=node+1-2^depth
    nodeNumber (k-g) (id/2^(depth-(k-g)))*slots
  else raw

end Hierarchy.DescentHostDirectory.SiteDecode

end OAI
