import OAI.Hierarchy.DescentOrdinaryWordTariff
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open DescentPacking.PackedMatch.Local.Stage
namespace NativePhase

def wordInvoice {w : ℕ} (phase : NativePhase w) : ℕ := DateBill.bitTariff phase.program phase.ticks

theorem wordInvoice_seq {w : ℕ} (left right : NativePhase w) :
    (left.seq right).wordInvoice=left.wordInvoice+right.wordInvoice :=
  DateBill.bitTariff_seq ..

end NativePhase

end Hierarchy.DescentSixParty.Chronology

end OAI
