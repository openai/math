import OAI.Hierarchy.TaggedWideCarried
import OAI.Hierarchy.TaggedWireShelfReads

namespace OAI
/-! # Original row segments cover each true aggregate bond at its physical endpoints -/

noncomputable section
namespace Hierarchy.Tagged.PassiveWindow
open AdaptiveProbe WireTelescope NamedAperture LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators

variable {S n W : ℕ} (ends : Fin n → Chord S) (bits : Fin n→ℕ) (s : Fin S)

/-- Literal row word = a digit of the original ordinal bond. -/
theorem data_at (v : State (installedWidths ends bits) s) (p : EndsAt ends bits s)
    (u : Fin (bits p.val.val.1)) :
    rowBits ends bits v ⟨(⟨p.val.val.1,u⟩,p.val.val.2),p.val.property⟩ =
      (v (byRow ends bits s p)).val.testBit (prefixAt ends bits p.val.val.1+u.val) :=
  rowBit_prefix ends bits v _

end Hierarchy.Tagged.PassiveWindow

end
end OAI
