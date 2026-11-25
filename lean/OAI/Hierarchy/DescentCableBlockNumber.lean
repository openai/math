import OAI.Hierarchy.DescentBundleHistory
import OAI.Hierarchy.DescentRecipeFootprint

namespace OAI
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentKernelHistory
variable {P : Type} {p : ℕ} {bits : P→ℕ}

def BlockRef.cableNumber {d : ℕ} (N : Network d P bits) (v : N.Site) (w : BlockRef p (boundaryWidth N v)) :
    Option (N.Edge×ℕ) := w.port.elim (fun e=>some (e.val,w.block)) (fun _=>none)

end Hierarchy.DescentBundleHistory

end OAI
