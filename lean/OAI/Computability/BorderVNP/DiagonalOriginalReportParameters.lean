import OAI.Computability.BorderVNP.DiagonalOriginalReportDelivery

/-! # Original description bytes in the receiver's local report layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Crossing Packing CellAddresses DiagonalTallyCellReports RoutingISA

/-- Changing the report scanner's other registers preserves each supplied
description, provided the field width and opaque-body capacity agree. -/
theorem OriginalReportDelivery.atReport {D C w teams : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    {t t' : SignedTaskArena.Layout} {dir : Directory.Layout} {N : Network D P bits} {cell : N.Site → Fin C}
    {hosts : Fin dir.entries → N.Site} {owner : ℕ → Fin teams} {issued : Fin teams → Memory w}
    {report target : ReportLayout} {packets : Fin dir.entries → ReportBundle}
    (original : OriginalReportDelivery t dir N cell hosts owner issued report packets)
    (arena : t=t') (width : target.fieldWidth=report.fieldWidth) (capacity : target.bodyCap=report.bodyCap) :
    OriginalReportDelivery t' dir N cell hosts owner issued target packets := by
  subst t'
  refine ⟨original.cells,?_,original.supplied,original.lower,original.upper,?_⟩
  · intro j
    simpa only [ReportBundle.delivered,width,capacity] using original.words j
  · intro j
    obtain ⟨body,description,values,marked,padding,translated⟩ := original.site j
    exact ⟨by simpa only [capacity] using body,by simpa only [width,capacity] using description,
      by simpa only [width] using values,marked,padding,translated⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
