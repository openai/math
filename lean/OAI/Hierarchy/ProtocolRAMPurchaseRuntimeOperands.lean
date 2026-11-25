import OAI.Hierarchy.ProtocolRAMPurchaseShelfGeometry
import OAI.Hierarchy.ProtocolRAMPurchaseSignedAllocation

namespace OAI
/-! # Registers and size conditions for the signed scan at one physical purchase stage -/

namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

abbrev sign (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) :=
  (geom S t c).signedInputs c.threshold c.stock

abbrev embedded (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) := (geom S t c).plan (banks t)

structure Ready (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) : Prop where
  heap : heapEnd z d copies ≤ c.threshold.base
  raw : 2^z ≤ c.threshold.base
  stocks : ∀ j, heapEnd z d copies≤(c.stock j).base ∧ (c.stock j).Fits (wordBits z d copies) c.threshold.base
  threshold : c.threshold.Fits (wordBits z d copies) c.start
  ct : (geom S t c).CTFits (banks t) (wordBits z d copies)
  wide : 0<wordBits z d copies
  directions : 2*k<2^(wordBits z d copies)
  degree : S.degree≤2^(wordBits z d copies)
  sockets : (stageAt z d t).span≤2^(wordBits z d copies)
  room : (geom S t c).endAddress<2^(wordBits z d copies)

end
end Hierarchy.ProtocolRAM.PurchaseCT

end OAI
