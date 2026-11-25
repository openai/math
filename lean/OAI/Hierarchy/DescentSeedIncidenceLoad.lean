import OAI.Hierarchy.DescentInitialHost

namespace OAI
/-! Initial directed incidence weights on sites and exterior hubs. -/
namespace Hierarchy.DescentInitialHost
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _=>1))
def hubFlag : Site N→Bool := Sum.elim (fun _=>false) (fun _=>true)

def incidenceLoad (w β : ℕ) (u : Site N) :=
  (∑e : Wire N,if u=source N e then w*(if hubFlag N (source N e) then β else 1) else 0)+
  (∑e : Wire N,if u=target N e then w*(if hubFlag N (target N e) then β else 1) else 0)

end
end Hierarchy.DescentInitialHost

end OAI
