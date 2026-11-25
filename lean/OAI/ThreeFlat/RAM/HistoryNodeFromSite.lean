import OAI.ThreeFlat.RAM.HistoryNodeValue
import OAI.ThreeFlat.Diagonal.HistorySelectedChronology

namespace OAI
/-! # The stored node value of a selected chronological site -/

noncomputable section
namespace ThreeFlat.RAM.HistoryStageBody.Physical.NodeValue

/-- The network, external cardinality and endpoint provenance all belong to the same
chronological site of the mathematical assembly. -/
def ofSite {F Pins E : Type} [Field F] (z : Diagonal.PhysicalStage.Run.SelectedNode F Pins E)
    (pointer : E→ℕ) (stream ext : ℕ) : NodeValue F :=
  ⟨z.arity,z.net,z.external,fun j=>pointer (z.origin j),stream,ext⟩

end ThreeFlat.RAM.HistoryStageBody.Physical.NodeValue

end
end OAI
