import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentDatedOperandNativePreparation

namespace OAI
/-! The registered ordinary date includes its entire ticket workspace in its declared address limit. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem prepared_limit (floor : ℕ)
    (reserve : v.origin.preparationWords=v.originControlWords+v.originMouthWords+v.rootSourceSize) :
    v.preparedUntil floor≤v.normalizedEnd floor ∧ v.normalizedEnd floor≤v.endAddress floor :=by
  rw [←v.grain_after_sources floor reserve]
  refine ⟨?_,Nat.le_add_right ..⟩
  change v.routedStart floor+v.origin.preparationWords≤v.routedStart floor+
    (v.origin.preparationWords+v.resolver.span+v.resolver.jobs*8*v.resolver.span)
  exact Nat.add_le_add_left ((Nat.le_add_right ..).trans (Nat.le_add_right ..)) _

theorem registered_prepared_limit (ports : DatePorts) (stageFloor : ℕ) :
    let b:=v.registeredFrom ports stageFloor
    b.preparedUntil stageFloor≤b.endAddress stageFloor :=by
  let f:=v.fundedFrom ports stageFloor
  let b:=v.registeredFrom ports stageFloor
  obtain ⟨before,after⟩:=b.prepared_limit stageFloor f.origin_reservation
  exact before.trans after

end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
