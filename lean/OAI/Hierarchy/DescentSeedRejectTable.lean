import OAI.Hierarchy.DescentSeedTokenNumbers
import OAI.Hierarchy.DescentPackedRejection

namespace OAI
/-! # Original packed lookup table for counts outside the seed alphabet -/
namespace Hierarchy.DescentTerminalPackedSeedFlags
open DescentSIMDLookup DescentSeedRoot
open scoped Fin.CommRing
noncomputable section

def predicate (s : ℕ) (x : Cell (digitsNeeded s)) := if x.val ≤ s then 0 else 1

def advice (s M a : ℕ) :=
  DescentPackedRejection.badChunk (predicate s) (M:=M) (a:Cell (digitsNeeded s*M))

end
end Hierarchy.DescentTerminalPackedSeedFlags

end OAI
