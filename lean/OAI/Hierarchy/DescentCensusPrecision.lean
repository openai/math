import OAI.Hierarchy.DescentPrivateShapeNumbers

namespace OAI
/-! # Signed census precision and capacity from the public calendar -/
namespace Hierarchy.DescentCompiler.AtomSchedule
def censusExponent (S : AtomSchedule) := S.priceExponent+S.localGrainExponent+S.localCapacityExponent
def censusBits (S : AtomSchedule) (p : ℕ) := Nat.clog 2 (p+1)+S.height*S.censusExponent
def censusCapacity (S : AtomSchedule) := 2*S.epochPower^S.localCapacityExponent
def censusLane (S : AtomSchedule) (p k : ℕ) := (1+S.censusBits p+2*S.censusCapacity)*2^k

end Hierarchy.DescentCompiler.AtomSchedule

end OAI
