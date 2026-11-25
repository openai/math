import OAI.Computability.BorderVNP.DiagonalReportSourcePlacement

/-! # Transport the original report along the same placements as the funded writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open Packing VPVNP.BurstRAM

/-- Equal private and live placement functions name the same published directory
at the same RAM, frame, owned output, and signed report. -/
theorem ReportWords.withEqualPlacements {w frame first base : ℕ} {a : Layout} {D : Directory.Layout}
    {m : Memory w} {pp lp pp' lp' : ℕ → ℕ × ℕ} {written out : ℕ → ℕ} {signed : Bool}
    (ret : ReportWords a frame (readings (Directory.ISA.publish m first base (D.directory pp lp))) written out signed)
    (placements : pp=pp' ∧ lp=lp') :
    ReportWords a frame (readings (Directory.ISA.publish m first base (D.directory pp' lp'))) written out signed := by
  obtain ⟨rfl,rfl⟩ := placements
  exact ret

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
