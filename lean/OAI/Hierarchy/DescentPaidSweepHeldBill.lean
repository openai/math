import OAI.Hierarchy.DescentPaidSweepBill
import OAI.Hierarchy.DescentPaidSweepLayout
import OAI.Hierarchy.DescentReachedCountRepackBill

namespace OAI
/-! # The sum of the census pitch transfer and both final archive scans -/
namespace Hierarchy.DescentPaidResidentCount.Sweep.HeldRepacked
open DescentOrdinaryAtomFieldRAM
noncomputable section
variable (base H G old M k paths cap b n p : ℕ)
local notation "D₀" => paths*2^k

def bill (unit : ℕ) := RoleCounts.Repitch.bill H G old M k paths b base unit+
  (2*tableBill ((p*2)*2^maskBits D₀ cap n M)+tableBill (2*2^sumBits D₀ cap b M)+
    columnBill p (rowCount H G M) 37+columnBill p (rowCount H G M) 19)

end
end Hierarchy.DescentPaidResidentCount.Sweep.HeldRepacked

end OAI
