import OAI.Hierarchy.DescentArchiveRankData
import OAI.Hierarchy.DescentSeedNodeOrder
import OAI.Hierarchy.DescentHiddenOrder

namespace OAI
/-! # The original coefficient archive and its seed node and private-word orders -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentKernelHistory DescentInitialHost Catalyst
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}

def seedArchive {cp pins : ℕ} (X : Approximation F cp pins) (R s : ℕ) (c : (initialGroup X R s).Choice) :
    Archive ((initialGroup X R s).state c) :=
  ⟨BitDescription.initial X R s c,_,NodeOrder.seedOrdinal X R s c,DescentHistoryOrder.seedHidden X R s c⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
