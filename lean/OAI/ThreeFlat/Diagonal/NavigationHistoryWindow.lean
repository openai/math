import OAI.ThreeFlat.Diagonal.NavigationArchiveDirectory
import OAI.ThreeFlat.RAM.PackedStageArchive

namespace OAI
/-! # Physical source and destination of a chronological histogram -/

namespace ThreeFlat.Diagonal.NavigationPass
open RAM

def Archive.hist (A : Archive) (steps : List NavigationDirectory.Stage) : PackedStageArchive.Layout :=
  ⟨A.phase,A.oldHistory,A.newHistory,A.cursor.dense,A.histWords steps⟩

end ThreeFlat.Diagonal.NavigationPass

end OAI
