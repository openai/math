import OAI.Hierarchy.DescentDatedSeedLayout
import OAI.Hierarchy.DescentCapacityCalendar
import OAI.Hierarchy.DescentPrivateDonorUniform
import OAI.Hierarchy.DescentSIMDLookup
import OAI.Hierarchy.DescentWalshPrecisionNumbers
import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentPackedWalshLanes
import OAI.Hierarchy.DescentOperandWidth
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! # First physical pitches from the actual chooser and operand resolver -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentSixParty DescentPackedWalsh DescentSIMDLookup
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
def originalDegree (gain : ℕ) := Chronology.OrdinaryLink.publicDegree S.rounds G.b
  (((capCalendar G.b S.rounds gain S.height).drop 0).head?.getD 0)
def firstDonor (gain k _p : ℕ) := TerminalScale.donorAmount k (originalDegree G S gain) 256 G.b G.C G.k
def firstPrecision (k tail p f quota : ℕ) :=
  S.localWalshBits p (S.groupWidth k tail 0+k) f quota
def venuePitch (h gain k tail p f quota : ℕ) :=
  if S.rounds=0 then 2^(laneBits (S.groupWidth k tail 0+k) h (firstPrecision S k tail p f quota)-k)
  else lanes h (firstDonor G S gain k p)
def venuePrice (factor gain k tail p f quota : ℕ) :=
  if S.rounds=0 then 16*factor*firstPrecision S k tail p f quota*2^k else 4*factor*firstDonor G S gain k p

def selectedLayout (h k tail gain p drift degree f quota base field wire history : ℕ) : Layout where
  base:=base
  groupsPerNode:=S.firstWidth G.b p/p
  fieldBits:=field
  operandBits:=DescentOperandWidth.recordBits G S k tail drift degree p
  packedLanes:=venuePitch G S h gain k tail p f quota
  operandLanes:=lanes h (2*DescentOperandWidth.recordBits G S k tail drift degree p)
  wire:=wire
  history:=history
  seedWidth:=S.firstWidth G.b p

end Hierarchy.DescentDatedSeedStartup

end OAI
