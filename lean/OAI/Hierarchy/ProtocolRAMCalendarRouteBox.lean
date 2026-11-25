import OAI.Hierarchy.ProtocolRAMCalendarRouteRange
import OAI.Hierarchy.ProtocolRAMCalendarNativeAccounts
import OAI.Hierarchy.ProbeCoreWalks

namespace OAI
/-! # Pricing the actual core paths in the live commodity table -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ProbeStage AdaptiveProbe AdaptiveProbe.OuterBank
open scoped BigOperators Classical
noncomputable section

/-- Each term in the two-prefix overflow account charges the true prescribed
bounded-hop route from its actual pair, including the occurrence's permutation. -/
theorem native_account_route {h d k q goods K : ℕ} (c : Mesh) (arena : Arena)
    (f : Attempt→Format h d k q goods) (initial payload : ℕ) (billed : Event→WordRows)
    (baseFee a M beta : ℝ) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (place : CoreBoard.Site h d k→Fin K) (i : Commodity (Fin (2^h)) (CoreBoard.Stages h d) k) :
    let A := nativeAccounts (N:=CoreBoard.Stages h d) c arena f initial payload billed baseFee a M beta
      (routeCap (CoreBoard.Stages h d) M)
    ((CoreBoard.commodityWalk (S:=S) π i).map (coreLength (CoreBoard.freeLength M))).sum=A.box i :=
  ((CoreBoard.commodity_walk (S:=S) π place M i).2).trans (routeCap_named h d k M i).symm

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
