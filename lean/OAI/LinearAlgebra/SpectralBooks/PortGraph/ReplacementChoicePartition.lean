import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoiceFamily
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementExtraction

/-! # Pairing the canonical record occurrences of an old map -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace PortGraph.ReplacementChoices.System

open scoped BigOperators Classical
open UniformDecorations PatchRecord

variable {N K : ℕ} {ε : ℝ} (C : System N K ε) (M : MapRep N)

/-- The partition used by the old certificate, with the occurrences indexed
by their reported integer identifiers. -/
def partition : Partition (Fin M.vertexCount.val) (C.Occ M) K :=
  ⟨C.part M, C.block M, C.mem_block M, C.nonempty M, C.bounded M⟩

/-- Pair the checked records along the original cut edges of the old map. -/
abbrev pairing : StubPairing (fun j => (C.record M j).shape.Stub) :=
  (C.partition M).pairing M.map (C.label M) (C.name M)

variable {w : ℕ} {B : Type} [CommSemiring B]
    (Term : Checked N K ε → Type) (val : (R : Checked N K ε) → Term R → (R.val.shape.Stub → Bits w) → B)

/-- The selected open tensors, still contracted over the old-width exterior
variables. Different list indices contribute separately. -/
def choiceValue (choice : (C.family Term).Label M) : B :=
  ∑ x : (C.pairing M).Wire → Bits w, ∏ j,
    val (C.checked M j) (choice j) (fun s => x (((C.pairing M).ends.symm ⟨j,s⟩).1))

end PortGraph.ReplacementChoices.System

end

end SpectralBooks
end LinearAlgebra
end OAI
