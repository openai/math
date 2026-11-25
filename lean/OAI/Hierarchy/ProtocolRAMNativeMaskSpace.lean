import OAI.Hierarchy.ProtocolRAMCalendarRun

namespace OAI
/-! # Placement of the real test, repair-bit, audit and verdict words -/
namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProbeStage ProbeStage.Native PurchaseStage
open scoped Fin.CommRing Classical
noncomputable section
variable {q d : ℕ}

/-- Every measured gate precedes the mask and each mask word precedes the
verdict and the audit PCs that write computed fields. -/
structure MaskSpace (L : Dispatch) (B : Repair q d) : Prop where
  stop : B.policy.stop.base<B.repairBits.base
  excess : B.policy.excess.base<B.repairBits.base
  payload : B.policy.payload.base<B.repairBits.base
  discrepancy : B.policy.discrepancy.base<B.repairBits.base
  audit : ∀ j : Fin L.candidates,∀ u∈audits L B,B.repairBits.base+j.val<u.low
  verdict : ∀ j : Fin L.candidates,B.repairBits.base+j.val<B.verdict

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
