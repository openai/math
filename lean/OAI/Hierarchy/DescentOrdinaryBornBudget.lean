import OAI.Hierarchy.DescentOrdinaryBornChart

namespace OAI
/-! Size and tariff of the original operand and role-port tables at an ordinary date. -/
namespace Hierarchy.DescentOrdinaryBorn
namespace Chart
variable (B : Chart)
def cpu := (4+10*B.bookWords)+(4+B.fields*(4+B.rows*(2*32+4)))
def textCost :=15*(B.bookWords+1)+(15+B.fields*(11+4*32))

end Chart

namespace RolePorts
variable (B : Chart)
def fields := ((B.donors*6)*B.args)*3
def bookWords := (1+fields B)*(2*2^((B.chipBits*1+B.chipBits)*B.lanes))
def output (base : ℕ) := base+bookWords B
def endAddress (base : ℕ) := output B base+fields B*B.pitch

end RolePorts
end Hierarchy.DescentOrdinaryBorn

end OAI
