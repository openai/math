import OAI.Hierarchy.DescentTerminalFixedReplay
import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentInitialHost
import OAI.Hierarchy.Catalyst
import OAI.ThreeFlat.BitNetwork.CopyGraph

namespace OAI
/-! The literal initial ancestry is determined by the input approximation before any choice is read. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler Catalyst DescentInitialHost DescentExteriorReplay
open scoped Classical
noncomputable section

def replayCalendar {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P)
    (S : AtomSchedule) (k tail j r : ℕ) (A : Snapshots k) : DescentTerminalFixedReplay.Calendar k where
  snapshots := A
  age := S.length
  frozenBits := k*S.length
  cohortBits := 8+S.capGain*S.length
  ports := Fintype.card (Port P X.width)
  j := j
  rest := r
  kept := S.groupWidth k tail S.length+k
  hosts := S.hostSize S.length
  seed a := (Fintype.equivFin (Site X.network.copyGraph) (.inr (finProdFinEquiv.symm a).1)).val

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
