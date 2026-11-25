import OAI.Hierarchy.DescentPublicDateMachine
import OAI.Hierarchy.DescentOrdinaryWordTariff

namespace OAI
/-! Exact word charges of the two compiled bodies of an ordinary public date. -/
namespace Hierarchy.DescentSixParty.Chronology.DateCode
open DescentPacking.PackedMatch.Local.Stage ThreeFlat.RAM PhysicalProcedure

theorem ordinary_tariff {w : ℕ} (body store : Procedure w) (clock meter : ℕ) :
    (DateCode.ordinary body clock store meter).tariff =
      DateBill.bitTariff body clock + DateBill.bitTariff store meter := by
  simp only [DateCode.tariff, DateCode.ticks, DateCode.names, DateBill.bitTariff]
  ring

end Hierarchy.DescentSixParty.Chronology.DateCode

end OAI
