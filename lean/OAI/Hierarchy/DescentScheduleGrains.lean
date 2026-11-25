import OAI.Hierarchy.DescentCutAlignment
import OAI.Hierarchy.DescentMeasuredEpoch

namespace OAI
/-! # Calendar grains attached to the actual chosen schedule and its per-profile splits -/
namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing
variable {F P : Type} [Field F] {D : ℕ} {bits : P→ℕ}
variable {G : PoweredGadget F} {u ε : ℝ} {he : 0≤ε}

def SubroundInput.Grain {H : Histories F D P bits} (z : ℕ) (s : SubroundInput H G (u:=u) he) : Prop :=
  (∀c,(s.placement c).z=z) ∧ ∀c t,Normalize.CutsEqual z (s.reblock c t)

def Schedule.Grains : {t : ℕ}→{H : Histories F D P bits}→(ℕ→ℕ)→Schedule G he (u:=u) t H→Prop
  | 0,_,_,_=>True
  | _+1,_,z,s=>SubroundInput.Grain (z 0) s.1 ∧ Grains (fun i=>z (i+1)) s.2

end Hierarchy.DescentSixParty

end OAI
