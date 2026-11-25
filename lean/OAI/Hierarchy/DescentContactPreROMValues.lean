import OAI.Hierarchy.DescentContactPreROMLayout

namespace OAI
/-! # Eight numerical operands of the measured contact-marker row -/
namespace Hierarchy.DescentContactPreROM.Layout
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable (A : Layout)

def markerValues {b : ℕ} (prior : Bool→Fin A.half→Fin 5→Cell b)
    (measured : Bool→Fin A.half→Fin 2→Cell b) (shape : Cell b) (j : Fin A.jobs) (i : Fin 8) : Cell b :=
  let (q,k):=finProdFinEquiv.symm j
  let (side,donor):=finProdFinEquiv.symm k
  match A.query q with
  | some (s,_,_)=>if finTwoEquiv side=s then
      ![prior s donor 0,prior s donor 1,measured s donor 0,measured s donor 1,
        prior s donor 2,prior s donor 3,prior s donor 4,shape] i
    else 0
  | none=>0

end
end Hierarchy.DescentContactPreROM.Layout

end OAI
