import OAI.ThreeFlat.Diagonal.NavigationArchiveDirectory
import OAI.ThreeFlat.RAM.NavigationNodeFields

namespace OAI
/-! # Node record for the initial rows of a physical archive -/
namespace ThreeFlat.Diagonal.NavigationPass
open RAM.NavigationNodeRows

def Archive.seedLayer (a : Archive) : Layer :=
  ⟨a.cursor.node,a.initialSites,0,0,0,a.initialRecords,a.initialRecords+5*a.initialSites,a.seed⟩

end ThreeFlat.Diagonal.NavigationPass

end OAI
