import OAI.Hierarchy.ProtocolRAMCalendarPhysicalCharges
import OAI.Hierarchy.ProtocolRAMReserveUse

namespace OAI
/-! # The released-catalyst term is exactly the sum of native reserve-use counters -/

namespace Hierarchy.ProtocolRAM.Calendar
open AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical
noncomputable section
variable {w n count : ℕ}

/-- Enumerating actual chronological debit rows by event and original local
ordinal. Boundary events carry zero such rows. -/
def debitRows (events : List Event) (widths : Event→List ℕ) := events.flatMap widths

theorem debitRows_sum (events : List Event) (widths : Event→List ℕ) :
    (debitRows events widths).sum=(events.map (fun ev=>(widths ev).sum)).sum := by
  induction events with
  | nil => rfl
  | cons ev rest ih =>
    change (widths ev++debitRows rest widths).sum=_
    rw [List.sum_append,ih]
    rfl

theorem debits_from_history (mesh : Mesh) (widths : Event→List ℕ) (report : Event→Charges)
    (m : Memory w) (a : ReserveUse.Archive) (b : RouteSettlement.Banks) (reserve : ℕ)
    (site : Fin (debitRows (events mesh) widths).length→Fin count)
    (ok : ReserveUse.Mounted a b reserve site (debitRows (events mesh) widths).get m)
    (sizeUsed : count≤b.used.size) (sizeReserved : count≤b.reserved.size)
    (bound : ∀i,(∑j,if site j=i then (debitRows (events mesh) widths).get j else 0)≤reserve)
    (wide : reserve<2^w)
    (issued : ∀ev∈events mesh,(widths ev).sum=(report ev).releasedBits) :
    ((events mesh).map (fun ev=>(report ev).releasedBits)).sum=
      ∑i : Fin count,RouteSettlement.actual b.used
        (ReserveUse.output a b reserve site (debitRows (events mesh) widths).get m) i.val := by
  rw [sum_reported_debits _ _ _ _ _ _ ok sizeUsed sizeReserved bound wide]
  have cast : (∑j : Fin (debitRows (events mesh) widths).length,(debitRows (events mesh) widths).get j)=
      (debitRows (events mesh) widths).sum := by
    rw [←List.sum_ofFn,List.ofFn_get]
  rw [cast,debitRows_sum]
  exact congrArg List.sum (List.map_congr_left (fun ev hev=>(issued ev hev).symm))

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
