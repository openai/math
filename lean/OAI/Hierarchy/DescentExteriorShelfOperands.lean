import OAI.Hierarchy.DescentExteriorHeader

namespace OAI
/-! # Operand planes and row addresses for the three exterior passes -/
namespace Hierarchy.DescentExteriorFetch
open DescentExterior DescentGL
open scoped Classical
noncomputable section
variable {j r t e : ℕ}
local notation "R" => 2^(j+r)
local notation "I" => Fin (e*R)

def slab (i : I) : Fin e := (finProdFinEquiv.symm i).1
def dest (i : I) : Rows j r := (rowOrd j r).symm (finProdFinEquiv.symm i).2

def passInputs (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) (s : Fin 3) :
    Fin e→Plane j r→Fin t→Bool :=
  ![x,(fun a=>swapWire (projected z false a)),(fun a=>swapWire (projected z true a))] s

def phase (s : Fin 2) : Bool := decide (s=1)

end
end Hierarchy.DescentExteriorFetch

end OAI
