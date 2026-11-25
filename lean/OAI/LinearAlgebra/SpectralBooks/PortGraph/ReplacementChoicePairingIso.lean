import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoicePartition
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementPairIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementSmallIso

/-! # Naturality of the cut pairing of checked old records -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace PortGraph.ReplacementChoices.System

open PatchRecord ReplacementTemplate

variable {N K : ℕ} {ε : ℝ} (C : System N K ε) {M H : MapRep N} (f : M.map.Iso H.map)

/-- The original map isomorphism restricts to a bijection of the cut wires. -/
def crossEdgeEquiv : (C.pairing M).Wire ≃ (C.pairing H).Wire :=
  Partition.cutEquiv (C.partition M) (C.partition H) M.map H.map f (C.occEquiv f)
    (fun v => (C.part_iso f v).symm)

/-- Both ends of each cut edge are the same numbered stubs of the same
checked records after the change of presentation. -/
theorem pairing_iso (e : (C.pairing M).Wire) (b : Bool) :
    Equiv.sigmaCongr (C.occEquiv f)
      (fun j => atTag (fun r : Checked N K ε => r.val.shape.Stub) (C.checked_iso f j))
      ((C.pairing M).ends (e,b)) = (C.pairing H).ends (C.crossEdgeEquiv f e,b) :=
  Partition.pairing_iso (C.partition M) (C.partition H) M.map H.map f (C.occEquiv f)
    (fun v => (C.part_iso f v).symm) (C.label M) (C.label H) (C.name M) (C.name H)
    MapLabels.vertexName (fun _ => rfl) (fun v => (C.label_iso f v).symm) (C.record_iso f) e b

end PortGraph.ReplacementChoices.System

end

end SpectralBooks
end LinearAlgebra
end OAI
