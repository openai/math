import OAI.Hierarchy.DescentHaloWalkRAM

namespace OAI
/-! # Word charges for the two original source-path headers -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentHaloWalkRAM

def columnCost (n hosts work h ratio : ℕ) :=
  ratio*((109+n*(81+28*work))*h+n*(2*work+4)*(hosts*h))
/-- Both headers gather the complete set of earlier distinct native endpoints. -/
def rankWork (D : ℕ) :=
  let P:=breadth D
  (P+1)*(30+4*P+4*(P*P))
def hostCost (H D h ratio : ℕ) :=
  columnCost (breadth D*(D+1)) H (rankWork D) h ratio
def rankCost (H D h ratio : ℕ) :=
  columnCost (breadth D) H (rankWork D) h ratio

def pathCharge (H G D h u ratio : ℕ) :=
  hostCost H D h ratio+ratio*(109*h+115*(4*(H*h+H*G*u)+
    (3+2*(h+1)*(2*(breadth D+1)+1))*h))

end Hierarchy.DescentDatedSourcePathDirectory

end OAI
