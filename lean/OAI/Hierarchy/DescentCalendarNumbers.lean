import OAI.Hierarchy.DescentPublicDegreeNumbers
import OAI.Hierarchy.DescentCompilerSlack
import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentHostDegree
import OAI.Hierarchy.DescentSixPartyGadget

namespace OAI
/-! # Physical directory sizes fixed before the compiler chooses a branch -/

namespace Hierarchy
open DescentHostDegree
open scoped BigOperators

namespace DescentSixParty
noncomputable section
open DescentCompiler
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The initial charge, the reset cut, and all possible ordinary cuts in
one period are covered by a constant independent of the epoch height. -/
def cutRate (t f g : ℕ) :=
  f+g+packExponent 20 3+
    ∑j : Fin t, (gainExponent 20 (atRound j.val)+packExponent 20 (atRound (j.val+1)))

def hostRate (t reset : ℕ) :=
  reset+∑j : Fin t, 2*(2^packExponent 20 (atRound j.val)+2)

def capRate (t g : ℕ) :=
  3+g+G.b+∑j : Fin t,2^gainExponent 20 (atRound j.val)*G.b

def stageNumbers (t J : ℕ) (f g reset M tail : ℕ) : AtomSchedule :=
  let c := hostRate t reset
  let e := capRate G t g
  let k := groupBits t J c e (cutRate t f g)
  ⟨t,J,c,e,2^tail,2^k,M⟩

end
end DescentSixParty
end Hierarchy

end OAI
