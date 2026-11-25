import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasTypes
import OAI.Computability.NearSquareRoot.InterchangeStageLedger

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatAtlas

open Interchange

/-- The numerical two-sided incidence table spells the given rectangles. -/
def Represents {L T : ℕ} (bits : List Bool) (r : Fin T → Rectangle (Fin L)) : Prop :=
  ∀ (s : Bool) (t : Fin T) (v : Fin L), mask bits L T s t v = true ↔
    v ∈ (if s then (r t).destinations else (r t).sources)

end FlatAtlas

end NearSquareRoot
end Computability
end OAI
