import OAI.ThreeFlat.RAM.NavigationNodeFields

namespace OAI
/-! # The physical row read by the chronological node publisher -/

namespace ThreeFlat.Diagonal.PhysicalStage
open RAM.NavigationNodeRows

/-- The input to one scan of the published two-column charge and eight-column
node directories, with the actual ordered physical children and owner array. -/
structure NodeRow where
  layer : Layer
  parent : Parent
  data : LayerData layer
  owners : Fin layer.count→ℕ

end ThreeFlat.Diagonal.PhysicalStage

end OAI
