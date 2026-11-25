import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoicePartition
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementOldRoot
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRecoverChoices

/-! # Forward occurrence tags and their boundary pairing -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph

namespace ReplacementChoices.System

variable {N K : ℕ} {ε : ℝ} (C : System N K ε) (Term : Checked N K ε → Type)
  {H : MapRep N} (t : (C.family Term).Label H)

/-- A concrete forward tag is the checked record and its chosen term index.
The identifier in every full old label distinguishes occurrences. -/
def choiceTag : C.Occ H ↪ Σ R, Term R where
  toFun j := ⟨C.checked H j,t j⟩
  inj' := by
    intro i j h
    apply Subtype.ext
    exact ((C.record_patch H i _).symm.trans (congrArg (fun a : Σ Q, Term Q => a.1.patchId) h)).trans
      (C.record_patch H j _)

variable (T : (Σ R, Term R) → ReplacementTemplate.{0,0,0})
  (stub : ∀ j, (T j).Stub ≃ j.1.val.shape.Stub)

/-- The concrete old pairing on the template stubs. Only the per-template
stub equivalence is applied; the wire set and its direction remain literal. -/
def choicePairing : StubPairing (fun j => (T (C.choiceTag Term t j)).Stub) :=
  (C.pairing H).renameStubs (fun j => (stub (C.choiceTag Term t j)).symm)

end ReplacementChoices.System

end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
