import Mathlib.Data.Nat.Basic

namespace OAI
/-! # The literal costs of mounting tables and scanning native output columns -/
namespace Hierarchy.DescentPaidResidentCount.Sweep

def tableBill (entries : ℕ) :=4+10*entries+7*(15*(entries+1))
def columnBill (p rows W : ℕ) :=(4+p*(4+rows*(2*W+4)))+7*(15+p*(11+4*W))

end Hierarchy.DescentPaidResidentCount.Sweep

end OAI
