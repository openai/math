import OAI.Hierarchy.DescentOrdinaryDonorDateCode
import OAI.Hierarchy.DescentNativePhaseInvoice
import OAI.Hierarchy.DescentDateCodeTariff

namespace OAI
/-! # Exact word tariff of the loaded ordinary date, including its final private meter -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch.Local.Stage.Dated
open DescentStaticWordColumn
noncomputable section

theorem loaded_tariff {F : Type} [Field F] (d : DonorDate) (gadget : PoweredGadget F)
    (pos : 0 < d.exponent) (payload seats board floor header w : ℕ) (input : Operands) (v : Measures)
    (load finish : NativePhase w) :
    let a:=d.schedule payload seats board
    let base:=a.rotationEnd input.roster floor
    let donor:=d.afterMatcher payload seats input board floor w
    let meter:=d.counter payload base header
    (d.codeLoadedAfter gadget pos payload seats board floor header w input v
      load.program load.ticks finish.program finish.ticks).tariff =
      load.wordInvoice+DateBill.bitTariff (a.program gadget pos input v w floor) (a.ticks gadget pos input v w floor)+
        donor.wordInvoice+finish.wordInvoice+DateBill.bitTariff (meter.program w) meter.ticks :=by
  intro a base donor meter
  dsimp only [a,base,donor,meter]
  simp only [codeLoadedAfter,DateCode.ordinary_tariff,DateBill.bitTariff_seq,NativePhase.wordInvoice]

end
end Hierarchy.DescentSixParty.Chronology.DonorDate

end OAI
