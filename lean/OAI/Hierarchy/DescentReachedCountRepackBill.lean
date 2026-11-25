import OAI.Hierarchy.DescentReachedCountPageLayout
import OAI.Hierarchy.DescentVenueExprBill

namespace OAI
/-! # Geometry and numerical charge of the count snapshot at a new group pitch -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch
open DescentSIMDLookup
noncomputable section
set_option quotPrecheck false
variable (H G old M k paths b : ℕ)
def shape : DescentVenueSlabs.Shape := ⟨2^k,H,G,old,M,b⟩
local notation "S" => shape H G old M k b
def after (base : ℕ) := DescentVenueSlabs.endAddress (S) base
def count (base : ℕ) := layout (after H G old M k b base) H G M k paths b
local notation "L" base => count H G old M k paths b base

def bill (base unit : ℕ) :=
  let l:=(L base)
  DescentVenueSlabs.ExprInputs.tariff (S) unit+
    ((4+l.blocks*(4+l.rows*18))+(4+10*l.tableWords)+(4+l.rows*(2*(1+56*l.donors)+4))+
     7*(15+l.blocks*39+15*(l.tableWords+1)+(11+4*(1+56*l.donors))))

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch

end OAI
