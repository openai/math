import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup

def reindexed {h g h' g' a : ℕ} (host : h'=h) (group : g'=g) (Y : Fin h→Fin g→Cell a) :=
  fun (u : Fin h') (v : Fin g')=>Y (Fin.cast host u) (Fin.cast group v)

end Hierarchy.DescentResetOperandSetup.Chart

end OAI
