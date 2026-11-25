import OAI.Computability.NearSquareRoot.SynchronizedBoxRow
import OAI.Computability.NearSquareRoot.SynchronizedNumberedBits
import OAI.Computability.NearSquareRoot.PrecisionGridSplitRank

/-! # Physical bit and spectator numbering for the emitted box opcodes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

variable {k L : ℕ} {b : List (ℕ × ℕ)} [∀ i, NeZero (BoxFin.modulus b i)]

/-- All fields use the rank read by the physical tape routines. -/
noncomputable def physicalLayout (h : BoxShape.Valid k L b) : BoxLayout b :=
  ⟨BoxFin.blockSpectators h, BoxFin.numberedBits h⟩

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
