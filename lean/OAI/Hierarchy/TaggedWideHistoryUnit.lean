import OAI.Hierarchy.ProbeFixedCalendarParameters
import OAI.Hierarchy.ProbeCatalystArchiveRows

namespace OAI
/-! # Public clock and uniform width per registered calendar role -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open ProtocolRAM.Calendar

def clock (m : Mesh) := (m.inject+m.cool)*(m.outerFuel*(1+m.reserveSteps*(m.innerFuel+1))+1)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage.CoreBoard

def wideJobs {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) := (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def wideHistoryUnit (unitCost : ℕ) :=
  HistoryRoles.clock v.mesh*unitCost+(2*v.keepLimit+1)+CatalystArchive.fuel v.mesh

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
