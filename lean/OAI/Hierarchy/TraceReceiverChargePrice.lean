import OAI.Hierarchy.TraceReceiverPrices
import OAI.Hierarchy.TraceFactorWork

namespace OAI
/-! # Paying the persistent terminal maps out of the same registered resource word -/
namespace Hierarchy.TraceFactorReceiver.Gather
open TraceDistribution

/-- The saved pin pass costs twenty-two instructions for every physical port.
That count is bounded by twice the native root charge even on a one-node
history whose root has many unused ports. The new unit is issued once for
both the previous execution and the additional saved-map and task work. -/
theorem charged_maps (w depth degree stages coefficient stageRate rootRate : ℕ)
    (perRoot perLevel price charge ports : ℕ)
    (height : depth≤ stages+4) (k : 0<coefficient) (positive : 0<charge)
    (localPins : ports≤2*charge)
    (covered : price≤FactorWork.archiveTariff w depth (setupPrice stages stageRate)
      (mapPrice degree rootRate) stages coefficient * charge) :
    price+(perRoot+22*ports)+perLevel*depth*charge ≤
      FactorWork.archiveTariff w depth (setupPrice stages (stageRate+(perRoot+44)+perLevel))
        (mapPrice degree rootRate) stages coefficient * charge := by
  let rows:=(2*stages+1)*(coefficient*(16*w^10+1)^3)
  let maps:=mapPrice degree rootRate
  let old:=10025+1016*depth+setupPrice stages stageRate+maps
  let extra:=perRoot+44+perLevel*depth
  let new:=10025+1016*depth+setupPrice stages (stageRate+(perRoot+44)+perLevel)+maps
  have one : 1≤rows:=Nat.succ_le_of_lt (by dsimp [rows]; positivity : 0<rows)
  have units : charge≤rows*charge:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right charge one
  have gain : old+extra≤new:=by
    have inc:=increase_stage_rate stages depth stageRate (perRoot+44) perLevel height
    dsimp [old,extra,new];omega
  have rootPrice := Nat.le_mul_of_pos_right perRoot positive
  have portPrice:=Nat.mul_le_mul_left 22 localPins
  have extraCost : perRoot+22*ports+perLevel*depth*charge≤extra*charge:=by
    dsimp [extra]
    rw [Nat.add_mul,Nat.add_mul]
    omega
  change price≤old*rows*charge at covered
  change _≤new*rows*charge
  calc
    _ ≤ old*rows*charge+extra*charge := by omega
    _ ≤ old*(rows*charge)+extra*(rows*charge) := by
      rw [Nat.mul_assoc]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left extra units) _
    _ = (old+extra)*(rows*charge) := (Nat.add_mul ..).symm
    _ ≤ new*(rows*charge) := Nat.mul_le_mul_right _ gain
    _ = _ := (Nat.mul_assoc ..).symm

end Hierarchy.TraceFactorReceiver.Gather

end OAI
